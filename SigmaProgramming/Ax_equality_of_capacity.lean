--== Аксиома Ax_equality_of_capacity ==--
import SigmaProgramming.Defs
import SigmaProgramming.Facts
import SigmaProgramming.Axioms

namespace SigmaProg
variable [m : SMModel]

open SM SMM

structure elems (a : SM) : Type where
  el : SMM
  prf : el ∈ list a

-- информация о начальном сегменте sm
structure iniseg_info (sm : SM) where
  tl : SM
  hd : SMM
  pi : cons tl hd ⊑ sm
  pe : hd ∈ list sm

-- извлечение первого hd после ism; поэтому ii.tl = ism
theorem getd (sm ism : SM)
  (tl0 : SM) (hd0 : SMM) (pi0 : cons tl0 hd0 ⊑ sm) (pe0 : hd0 ∈ list sm)
  (pi : ism ⊑ tl0) :
  ∃ (ii : iniseg_info sm), ii.tl = ism := by
  match p : pi with
  | .nn =>
    rename_i h
    have pi0' : cons tl0 hd0 ⊑ sm := by simpa [h] using pi0
    exact ⟨⟨tl0, hd0, pi0', pe0⟩, h⟩
  | .n2 hd0' pi' =>
    rename_i tl0' _
    have pi0' : cons tl0' hd0' ⊑ sm := iniseg_cons pi0
    have pe0' : hd0' ∈ list sm := iniseg_elem_head pi0'
    exact getd sm ism tl0' hd0' pi0' pe0' pi'


--== Собственно, доказательство ==--

theorem Ax_equality_of_capacity
  {a b : SM} (nnil : nonNil a) :
  (a = b) ↔ (∀ (c : SM), (c ⊑ a) →
      (c ⊑ b) ∧ (c ≠ b → ∃ d : elems a, (cons c d.el ⊑ a) ∧ (cons c d.el ⊑ b))) := by
  constructor
  ----------------------------------------------------------------------
  -- (→)  Прямое направление
  ----------------------------------------------------------------------
  intro h_eq c hc
  and_intros
  · simpa [h_eq] using hc
  · intro hc_ne
    -- извлекаем нужный d
    have d := getd a c (tail a) (head a)
        (by have : cons (tail a) (head a) = a := Ax_list3 nnil
            rw [← this]; exact .nn)
        (elem_cons_head a nnil)
        (iniseg_tail_right (by intro H; exact hc_ne (H ▸ h_eq)) hc)

    rcases d with ⟨ii, eq⟩

    have piA : cons c ii.hd ⊑ a := by simpa [eq] using ii.pi
    have piB : cons c ii.hd ⊑ b := by simpa [h_eq] using piA

    exact ⟨⟨ii.hd, ii.pe⟩, piA, piB⟩
  ----------------------------------------------------------------------
  -- (←)  Обратное направление
  ----------------------------------------------------------------------
  intro H
  have p := H a .nn
  -- p : a ⊑ b ∧ (¬ a = b → ∃ d : elems a, cons a d.el ⊑ a ∧ cons a d.el ⊑ b)
  have hab : a ⊑ b := p.1

  -- Доказываем a = b от противного, вычисляя длину.
  -- Здесь нужна либо классическая логика, либо DecidableEq!
  have h : a ≠ b → False := by
    intro na_eq
    have ⟨d,prfs⟩ := p.2 na_eq
    have le := iniseg_len_le prfs.1
    have : ‖a‖+1 ≤ ‖a‖ := by simpa using le
    exact Nat.not_succ_le_self _ this
  exact Classical.byContradiction h
