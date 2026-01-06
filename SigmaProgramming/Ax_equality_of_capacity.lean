--== Аксиома Ax_equality_of_capacity ==--
import SigmaProgramming.Defs
import SigmaProgramming.Facts
import SigmaProgramming.Axioms

namespace GES
variable [m : SModel]
open S SM

-- информация о начальном сегменте α
structure iniseg_info (α : S) where
  tl : S
  hd : SM
  pi : tl ∷ hd ⊑ α
  pe : hd ∈ list α

-- извлечение первой головы после β; поэтому ii.tl = β
def getδ (α β : S)
  (tl₀ : S) (hd₀ : SM) (pi₀ : tl₀ ∷ hd₀ ⊑ α) (pe₀ : hd₀ ∈ list α)
  (pi : β ⊑ tl₀) :
  ∃ (ii : iniseg_info α), ii.tl = β :=
  match p : pi with
  | .irefl =>
    have h : tl₀ = β := by assumption
    ⟨⟨tl₀, hd₀, h ▸ pi₀, pe₀⟩, h⟩
  | .icons (tl:=tl₀') hd₀' pi' =>
    have pi₀' : tl₀' ∷ hd₀' ⊑ α := iniseg_cons pi₀
    have pe₀' : hd₀' ∈ list α := iniseg_elem_head pi₀'
    getδ α β tl₀' hd₀' pi₀' pe₀' pi'

--== Собственно, доказательство ==--

theorem Ax_equality_of_capacity {α β : S} (nnil : α ≠ nil) :
  (α = β) ↔ (∀ (γ : S), (γ ⊑ α) →
      (γ ⊑ β) ∧ (γ ≠ β → ∃ δ : elems α, (γ ∷ δ.el ⊑ α) ∧ (γ ∷ δ.el ⊑ β))) := by
  constructor
  ----------------------------------------------------------------------
  -- (→)  Прямое направление
  ----------------------------------------------------------------------
  intro h_eq γ hγ
  constructor
  · exact h_eq ▸ hγ
  · intro hγ_ne
    -- извлекаем нужный δ
    have δ := getδ α γ (tail α) (head α)
        (by have : (tail α ∷ head α) = α := Ax_list3 nnil
            rw [← this]; exact .irefl)
        (elem_cons_head α nnil)
        (iniseg_tail_right (by intro H; exact hγ_ne (H ▸ h_eq)) hγ)
    rcases δ with ⟨ii, eq⟩
    have piA : γ ∷ ii.hd ⊑ α := by simpa [eq] using ii.pi
    have piB : γ ∷ ii.hd ⊑ β := by simpa [h_eq] using piA
    exact ⟨⟨ii.hd, ii.pe⟩, piA, piB⟩
  ----------------------------------------------------------------------
  -- (←)  Обратное направление
  ----------------------------------------------------------------------
  intro H
  have ⟨_,p⟩ := H α .irefl
  -- p : α ≠ β → ∃ δ, ((α ∷ δ.el) ⊑ α) ∧ (α ∷ δ.el) ⊑ β

  -- Доказываем α = β от противного, вычисляя длину.
  -- Здесь нужна либо классическая логика, либо DecidableEq.
  have h : ¬ α ≠ β := by
    intro nα_eq
    have ⟨_,⟨prf,_⟩⟩ := p nα_eq
    have le := iniseg_len_le prf
    have : ‖α‖+1 ≤ ‖α‖ := by simp at le
    exact Nat.not_succ_le_self _ this
  exact Classical.byContradiction h
