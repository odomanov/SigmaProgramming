--== Аксиомы ==--
import SigmaProgramming.Defs
import SigmaProgramming.ElemWF

namespace SigmaProg
variable [m : SMModel]

open SM SMM

theorem Ax_empty_list  : ¬ (x ∈ list nil) := nofun
theorem Ax_uniqueness : cons xs x = cons ys y → xs = ys ∧ x = y := by
  intro p
  constructor
  · cases x <;> cases y <;> injection p
  · cases xs <;> cases ys <;> cases x <;> cases y <;> injection p
theorem Ax_list1 : tail (cons xs x) = xs := by cases x <;> trivial
theorem Ax_list2 : head (cons xs x) = x := by cases x <;> trivial
theorem Ax_list3 (ne : nonNil xs) : (cons (tail xs) (head xs)) = xs := by
  cases xs <;> trivial
theorem Ax_list4 : tail nil = nil := by trivial
theorem Ax_list5 : head nil = list nil := by trivial
theorem Ax_list6 : cons (conc a b) c = conc a (cons b c) := by
  cases a <;> cases b <;> cases c <;> trivial
theorem Ax_list7 : ∀ a b c, conc (conc a b) c = conc a (conc b c) := by
  intro a b c
  induction c with
  | nil => rfl
  | cons _ hd ih =>
    rw [conc,conc,conc]
    exact congrFun (congrArg cons ih) hd
theorem conc_nil : ∀ y ys, conc .nil ys = ys → conc .nil (cons ys y) = cons ys y := by
    intro y ys eq
    cases y <;> rw [conc,eq]
theorem Ax_list8 : conc nil xs = xs :=
  match xs with
  | .nil => rfl
  | .cons zs z => conc_nil z zs (@Ax_list8 zs)
theorem Ax_list9 : conc xs nil = xs := rfl
-- theorem Ax_induction -- автоматически определяется для  индуктивных типов
--    да, но элиминатор у меня свой!
-- Ax_equality_of_capacity -- см. отдельный файл
theorem Ax_foundation {P : (SMM) → Prop} :
  (∀ d : SMM, ((∀ g, g ∈ d → P g) → P d)) → ∀ x, P x := by
  intros
  apply WellFounded.induction elem_wf
  assumption
-- theorem Ax_d0_separation : TODO
-- theorem Ax_d0_choice : TODO
