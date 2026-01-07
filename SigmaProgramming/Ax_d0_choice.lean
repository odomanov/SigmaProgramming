--== Аксиома Ax_d0_choice ==--
import SigmaProgramming.Defs
import SigmaProgramming.Show

namespace GES
variable [m : SModel]
open S SM

-- функции, заданные парами, удовлетворяющими Φ (обобщение HLF)
inductive isHLFΦ (Φ : SM → SM → Prop) : S → Type where
| nil : isHLFΦ Φ <| nil ∷ ⦅.nil,.nil⦆
| cons : isHLFΦ Φ (α₀ ∷ ⦅α₁,α₂⦆) → (a b : SM) → Φ a b
  → isHLFΦ Φ (α₀ ∷ ⦅α₁,α₂⦆ ∷ ⦅α₁ ∷ a, α₂ ∷ b⦆)

theorem isHLFΦ.HLFΦisHLF : (ishlfφ : isHLFΦ Φ α) → ∃ isp : isPL α, isHLF ⟨α,isp⟩
| .nil => ⟨_,.nil⟩
| .cons hlf a b p => ⟨_,.cons hlf.HLFΦisHLF.snd a b⟩

structure HLFΦ (Φ : SM → SM → Prop) where
  s : S
  is_hlfφ : isHLFΦ Φ s

-- конверсия
@[simp]
def HLFΦ.toHLF : (hlfφ : HLFΦ Φ) → HLF
| ⟨s,ishlfφ⟩ => ⟨⟨s,ishlfφ.HLFΦisHLF.fst⟩,ishlfφ.HLFΦisHLF.snd⟩
@[simp]
abbrev HLFΦ.conv : (hlf : HLFΦ Φ) → HLF := HLFΦ.toHLF

-- принадлежность
inductive HLFΦ.Mem : (s : SM) → HLFΦ Φ → Prop where
| elnil : Mem ⦅nil,nil⦆ ⟨_,.nil⟩
| here (ish : isHLFΦ Φ (α₀ ∷ ⦅α,β⦆))
  : Mem ⦅α∷a, β∷b⦆ ⟨α₀ ∷ ⦅α,β⦆ ∷ ⦅α∷a, β∷b⦆,.cons ish a b p⟩
| there (ish : isHLFΦ Φ (α₀ ∷ ⦅α,β⦆))
  : Mem x ⟨α₀ ∷ ⦅α,β⦆,ish⟩ → Mem x ⟨α₀ ∷ ⦅α,β⦆ ∷ ⦅α∷a, β∷b⦆,.cons ish a b p⟩

instance : Membership SM (HLFΦ Φ) where
  mem := λ α β => HLFΦ.Mem β α

-- Repr

open Std Format

-- mutual
--   partial def HLFΦ.rf [Repr SM] : HLFΦ Φ → Nat → Format := λ hs n =>
--     ", ".intercalate (.map (pretty ∘ (SM.rf · n)) hs.toHLF.conv_list.reverse)
-- end

-- instance : Repr (HLFΦ Φ) := ⟨HLFΦ.rf⟩

-- предварительные леммы

-- если в паре первый элемент - nil, то и второй - nil.
theorem HLFΦ_nil
  : ∀ (ish : isHLFΦ Φ α) {α₂}, ⦅nil,α₂⦆ ∈ (⟨α,ish⟩ : HLFΦ Φ) → α₂ = .nil := by
  intro ish _ el
  cases el with
  | elnil => rfl
  | there ish' el' => exact HLFΦ_nil ish' el'

-- в HLFΦ все элементы кроме первого удовлетворяют Φ
theorem HLFΦ_el : ∀ (hlf : HLFΦ Φ), ⦅α ∷ a, β ∷ b⦆ ∈ hlf → Φ a b := by
  intro hlf el; cases el
  assumption
  rename isHLFΦ Φ _ => ish
  rename HLFΦ.Mem _ _ => el'
  exact HLFΦ_el ⟨_,ish⟩ el'

-- в HLFΦ все элементы, не равные nil, удовлетворяют Φ
theorem HLFΦ_nnil : ∀ (ish : isHLFΦ Φ α),
  ∀ {α₁ α₂}, ⦅α₁,α₂⦆ ∈ (⟨α,ish⟩ : HLFΦ Φ) → (α₁ ≠ .nil) → Φ α₁.head α₂.head := by
  intro ish α₁ _ el _
  cases α₁
  · contradiction
  · cases el with
    | here ish' => assumption
    | there ish' el' => exact HLFΦ_nnil ish' el' (by assumption)


-- аксиома Δ₀-выборки

-- функция добавляет все элементы β к ish₀
def choice_fold (β : S) (Φ : SM → SM → Prop) (p : ∀ α ∈ β, Σ' δ, Φ α δ)
  (ish₀ : isHLFΦ Φ (α ∷ ⦅α₁,α₂⦆)) : Σ' (α : S), isHLFΦ Φ α
  := match h : β with
    | .nil => ⟨_,ish₀⟩
    | .cons tl hd =>
      let ⟨δ,Φδ⟩ := p hd .here
      have pp : ∀ α, (α ∈ tl) → Σ' δ, Φ α δ := by
        intro α inα
        have ⟨hα,hΦα⟩ := p α (.there inα)
        exists hα
      choice_fold tl Φ pp (isHLFΦ.cons ish₀ hd δ Φδ)

def choice (β : S) (Φ : SM → SM → Prop) (p : ∀ α ∈ β, Σ' δ, Φ α δ)
  : Σ' (α : S), isHLFΦ Φ α := choice_fold β Φ p .nil

theorem Ax_d0_choice (β : S) (Φ : SM → SM → Prop) (p : ∀ α ∈ β, Σ' δ, Φ α δ)
  : ∃ (α : S) (ish : isHLFΦ Φ α), ∀ {α₁ α₂}, ((⦅α₁, α₂⦆ ∈ (⟨α,ish⟩ : HLFΦ Φ)) →
  ((α₁ = .nil → α₂ = .nil) ∧ (α₁ ≠ .nil → Φ α₁.head α₂.head))) := by
  let ⟨α,ish⟩ := choice β Φ p
  exists α, ish
  intro _ _ el
  constructor
  · intro eq; rw [eq] at el; exact HLFΦ_nil ish el
  · intro nnil; exact HLFΦ_nnil ish el nnil
