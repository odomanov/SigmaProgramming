--== Аксиомы ==--
import SigmaProgramming.Defs
import SigmaProgramming.Facts
import SigmaProgramming.MemWF

namespace GES
variable [m : SModel]
open S SM

theorem Ax_empty_list  : ¬ (α ∈ list nil) := nofun
theorem Ax_uniqueness : cons αs α = cons βs β → αs = βs ∧ α = β := by
  intro p
  injection p
  constructor <;> assumption
theorem Ax_list1 : tail (cons αs α) = αs := by cases α <;> trivial
theorem Ax_list2 : head (cons αs α) = α := by cases α <;> trivial
theorem Ax_list3 (ne : αs ≠ nil) : (cons (tail αs) (head αs)) = αs := by
  cases αs <;> trivial
theorem Ax_list4 : tail nil = nil := by trivial
theorem Ax_list5 : head nil = list nil := by trivial
theorem Ax_list6 : cons (conc a b) c = conc a (cons b c) := by
  cases a <;> cases b <;> cases c <;> trivial
theorem Ax_list7 : ∀ α β γ, conc (conc α β) γ = conc α (conc β γ) := by
  intros _ _ γ
  induction γ with
  | nil => rfl
  | cons _ hd ih =>
    rw [conc,conc,conc]
    exact congrFun (congrArg cons ih) hd
theorem Ax_list8 : ∀ αs, conc nil αs = αs
  | .nil => rfl
  | .cons βs β => conc_nil β βs (Ax_list8 βs)
theorem Ax_list9 : conc αs nil = αs := rfl
theorem Ax_induction {Φ : S → Prop} :   --    элиминаторы не стандартные!
    Φ nil
  → (∀ α δ, (Φ α → Φ (cons α δ)))
  → (α : S) → Φ α := by
  intro _ h α
  induction α
  · assumption
  · apply h; assumption
theorem Ax_inductionSM {Φ : SM → Prop} :   -- принцип индукции для SM
    Φ (list nil)
  → (∀ a, Φ (atom a))
  → (∀ α δ, (Φ (list α) → Φ (list (cons α δ))))
  → (α : SM) → Φ α := by
  intro hn ha h α
  induction α with
  | atom => exact ha _
  | listn => exact hn
  | listc ih1 ih2 ih3 _ => exact h ih1 ih2 ih3
-- Ax_equality_of_capacity -- см. отдельный файл
theorem Ax_foundation {Φ : SM → Prop} :
  (∀ δ : SM, ((∀ γ, γ ∈ δ → Φ γ) → Φ δ)) → ∀ α, Φ α := by
  intros
  apply WellFounded.induction mem_wf
  assumption
-- Ax_d0_separation -- см. отдельный файл
-- Ax_d0_choice -- см. отдельный файл
