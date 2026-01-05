--== Аксиома Ax_d0_separation ==--
import SigmaProgramming.Defs
import SigmaProgramming.MemWF

namespace GES
variable [m : SModel]
open S SM

-- определяем тип списка, существование которого нужно доказать
inductive isHLFΦ (Φ : SM → Prop) : S → Prop where
| nil : isHLFΦ Φ <| nil ∷ ⦅nil,nil⦆
| cons (ish : isHLFΦ Φ (α ∷ ⦅α₁,α₂⦆)) (δ : SM) (p :   Φ δ)
  : isHLFΦ Φ (α ∷ ⦅α₁,α₂⦆ ∷ ⦅α₁∷δ,α₂∷δ⦆)
| pass (ish : isHLFΦ Φ (α ∷ ⦅α₁,α₂⦆)) (δ : SM) (p : ¬ Φ δ)
  : isHLFΦ Φ (α ∷ ⦅α₁,α₂⦆ ∷ ⦅α₁∷δ,α₂⦆)

-- конверсия в isHLF
-- def isHLFΦ.HLFΦisHLF : (ishlfφ : isHLFΦ Φ α) → isHLF α
-- | .nil => .nil
-- | .cons hlf δ p => .cons hlf.HLFΦisHLF δ δ
-- | .pass hlf δ p => .pass hlf.HLFΦisHLF δ

structure HLFΦ (Φ : SM → Prop) where
  s : S
  is_hlfφ : isHLFΦ Φ s

-- конверсия
-- def HLFΦ.toHLF : (hlfφ : HLFΦ Φ) → HLF := λ ⟨s,ishlfφ⟩ ↦ ⟨s,ishlfφ.HLFΦisHLF⟩
-- abbrev HLFΦ.conv : (hlfφ : HLFΦ Φ) → HLF := HLFΦ.toHLF

inductive HLFΦ.Mem : SM → HLFΦ Φ → Prop where
| elnil : Mem ⦅nil,nil⦆ ⟨_,.nil⟩
| herec (ish : isHLFΦ Φ (α ∷ ⦅α₁,α₂⦆))
  : Mem ⦅α₁ ∷ δ,α₂ ∷ δ⦆ ⟨_,.cons ish δ p⟩
| herep (ish : isHLFΦ Φ (α ∷ ⦅α₁,α₂⦆))
  : Mem ⦅α₁ ∷ δ,α₂⦆ ⟨_,.pass ish δ p⟩
| therec (ish : isHLFΦ Φ (α ∷ ⦅α₁,α₂⦆))
  : Mem x ⟨_,ish⟩ → Mem x ⟨_,.cons ish δ p⟩
| therep (ish : isHLFΦ Φ (α ∷ ⦅α₁,α₂⦆))
  : Mem x ⟨_,ish⟩ → Mem x ⟨_,.pass ish δ p⟩

instance : Membership SM (HLFΦ Φ) where
  mem := λ x y ↦ HLFΦ.Mem y x

-- голова списка принадлежит HLFΦ
theorem HLFΦ_head : (ish : isHLFΦ Φ (α ∷ x)) → x ∈ (⟨α ∷ x,ish⟩  : HLFΦ Φ)
  | .nil => .elnil
  | .cons hlf _ p => .herec (p:=p) hlf
  | .pass hlf _ p => .herep (p:=p) hlf

-- сущестование предыдущего элемента с его свойствами
theorem HLFΦ_pred {hlf : HLFΦ Φ} : ⦅α₁ ∷ δ, α₂⦆ ∈ hlf
  → ∃ α₃, ⦅α₁,α₃⦆ ∈ hlf ∧ ((Φ δ → α₂ = (α₃ ∷ δ)) ∧ (¬ Φ δ → α₂ = α₃)) := by
  let ish := hlf.is_hlfφ
  intro el
  cases el with
  | herec ish' =>
    expose_names
    cases ish with
    | cons _ _ p' =>
      let el' := HLFΦ.Mem.therec (p:=p') ish' <| HLFΦ_head ish'
      exact ⟨α₂,el',⟨λ _ ↦ rfl, λ _ ↦ by contradiction⟩ ⟩
  | herep ish' =>
    expose_names
    cases ish with
    | pass _ _ p' =>
      let el' := HLFΦ.Mem.therep (p:=p') ish' <| HLFΦ_head ish'
      exact ⟨α₂,el',⟨λ _ ↦ by contradiction, λ _ ↦ rfl⟩ ⟩
  | therec _ el1 =>
    cases ish with
    | cons hlf' _ p' =>
      have ⟨α₃',el',eq'⟩ := HLFΦ_pred el1
      exact ⟨α₃',.therec (p:=p') hlf' el',eq'⟩
  | therep _ el1 =>
    cases ish with
    | pass hlf' _ p' =>
      have ⟨α₃',el',eq'⟩ := HLFΦ_pred el1
      exact ⟨α₃',.therep (p:=p') hlf' el',eq'⟩

-- длина любого элемента HLFΦ меньше, либо равно длине самого HLFΦ
theorem HLFΦ_mem_le_length {Φ : SM → Prop} :
  ∀ {s : S} (ish : isHLFΦ Φ s) {α₁ α₂ α₃ α₄ α : S},
  s = (α ∷ ⦅α₁, α₂⦆) → ⦅α₃, α₄⦆ ∈ (⟨s, ish⟩ : HLFΦ Φ) → α₃.len ≤ α₁.len
  | _, .nil, _, _, _, _, _, rfl, .elnil => Nat.le_refl 0
  | _, .cons _    δ _, _, _, _, _, _, rfl, .herec .. => Nat.le_refl _
  | _, .cons ish' δ _, _, _, _, _, _, rfl, .therec _ el' =>
    let h_prev := HLFΦ_mem_le_length ish' rfl el'
    Nat.le_trans h_prev (Nat.le_succ _)
  | _, .pass _    δ _, _, _, _, _, _, rfl, .herep .. => Nat.le_refl _
  | _, .pass ish' δ _, _, _, _, _, _, rfl, .therep _ el' =>
    let h_prev := HLFΦ_mem_le_length ish' rfl el'
    Nat.le_trans h_prev (Nat.le_succ _)

-- вариант предыдущей леммы
theorem HLFΦ_mem_lt_length
  (el : ⦅α₃, α₄⦆ ∈ (⟨α ∷ ⦅α₁, α₂⦆, ish⟩ : HLFΦ Φ)) : α₃.len < (α₁ ∷ δ).len :=
  Nat.lt_succ_of_le <| HLFΦ_mem_le_length ish rfl el

theorem HLFΦ_head_unique
  (el : ⦅α₀ ∷ a, α₁⦆ ∈ (⟨α ∷ ⦅α₀, α₂⦆, ish⟩ : HLFΦ Φ)) : False := by
  have hle := HLFΦ_mem_le_length ish rfl el
  exact Nat.not_succ_le_self _ hle

-- совпадение первых элементов пары влечёт совпадение вторых
theorem HLFΦ_unique :
  ∀ (hlf : HLFΦ Φ), ⦅α₀, α₁⦆ ∈ hlf → ⦅α₀, α₂⦆ ∈ hlf → α₁ = α₂
  | ⟨_, .nil⟩, el1, el2 => by cases el1; cases el2; rfl
  | ⟨_, .cons ish _ _⟩, el1, el2 => by
    cases el1 with
    | herec _ =>
      cases el2 with
      | herec _ => rfl
      | therec _ el2' => exact (HLFΦ_head_unique el2').elim
    | therec _ el1' =>
      cases el2 with
      | herec _ => exact (HLFΦ_head_unique el1').elim
      | therec _ el2' => exact HLFΦ_unique ⟨_, ish⟩ el1' el2'
  | ⟨_, .pass ish _ _⟩, el1, el2 => by
    cases el1 with
    | herep _ =>
      cases el2 with
      | herep _ => rfl
      | therep _ el2' => exact (HLFΦ_head_unique el2').elim
    | therep _ el1' =>
      cases el2 with
      | herep _ => exact (HLFΦ_head_unique el1').elim
      | therep _ el2' => exact HLFΦ_unique ⟨_, ish⟩ el1' el2'


-- Аксиома Δ₀-выделения

-- док-во второй половины
theorem Ax_d0_separation' {hlf : HLFΦ Φ} : ⦅nil,α⦆ ∈ hlf → α = nil := by
  intro el; cases he : el with
  | elnil => rfl
  | therep ish' el' => exact Ax_d0_separation' el'
  | therec ish' el' => exact Ax_d0_separation' el'

-- всё доказательство
theorem Ax_d0_separation {hlf : HLFΦ Φ} :
  (⦅α₀,α₁⦆ ∈ hlf → ⦅α₀ ∷ δ,α₂⦆ ∈ hlf →  ((Φ δ → α₂ = (α₁ ∷ δ)) ∧ (¬ Φ δ → α₂ = α₁)))
  ∧ (⦅nil,α⦆ ∈ hlf → α = nil) := by
  constructor
  · intro el1 el2
    have ⟨α₃,el3,c⟩ := HLFΦ_pred el2
    have eq := HLFΦ_unique hlf el1 el3
    exact eq ▸ c
  · intro el; exact Ax_d0_separation' el
