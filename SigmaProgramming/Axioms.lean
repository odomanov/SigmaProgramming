--== Аксиомы ==--
import SigmaProgramming.Defs
import SigmaProgramming.Facts
import SigmaProgramming.MemWF

namespace GES
variable [m : SModel]
open S SM

theorem Ax_empty_list  : ∀ α, α ∉ nil := nofun
theorem Ax_uniqueness : cons αs α = cons βs β → αs = βs ∧ α = β := by
  intro p; injection p; constructor <;> assumption
theorem Ax_list1 : tail (cons αs α) = αs := by cases α <;> trivial
theorem Ax_list2 : head (cons αs α) = α := by cases α <;> trivial
theorem Ax_list3 (ne : αs ≠ nil) : (cons (tail αs) (head αs)) = αs := by
  cases αs <;> trivial
theorem Ax_list4 : tail nil = nil := by trivial
theorem Ax_list5 : head nil = list nil := by trivial
theorem Ax_list6 : cons (conc α β) γ = conc α (cons β γ) := by simp_all
theorem Ax_list7 : conc (conc α β) γ = conc α (conc β γ) := by
  cases γ with
  | nil => rfl
  | cons _ _ => simp; apply Ax_list7
theorem Ax_list8 : ∀ α, conc nil α = α
  | nil => rfl
  | cons β _ => by simp_all; cases β <;> apply Ax_list8
theorem Ax_list9 : conc α nil = α := rfl
theorem Ax_induction {Φ : S → Prop} :
    Φ nil
  → (∀ α δ, (Φ α → Φ (cons α δ)))
  → (α : S) → Φ α := by
  intro _ h α
  induction α with
  | nil => assumption
  | cons _ _ _ => apply h; assumption
theorem Ax_inductionSM {Φ : SM → Prop} :   -- принцип индукции для SM
    Φ (list nil)
  → (∀ a, Φ (atom a))
  → (∀ α, ((∀ x ∈ (list α), Φ x) → Φ (list α)))
  → (α : SM) → Φ α := by
  intro hn ha hl α
  induction α with
  | atom _ => apply ha
  | list s ih => apply hl s ih
-- Ax_equality_of_capacity -- см. отдельный файл
theorem Ax_foundation {Φ : SM → Prop} :
  (∀ δ : SM, ((∀ γ ∈ δ, Φ γ) → Φ δ)) → ∀ α, Φ α := by
  intros
  apply WellFounded.induction mem_wf
  assumption
-- Ax_d0_separation -- см. отдельный файл
-- Ax_d0_choice -- см. отдельный файл
