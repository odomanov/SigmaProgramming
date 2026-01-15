-- Доказательство фундирования для Mem - нестандартные элиминаторы
import SigmaProgramming.Defs

namespace GES
variable [m : SModel]
open S SM

-- Определяем элиминаторы для S, SM
@[induction_eliminator]
theorem S.induction {motive : S → Prop}
  (nil : motive nil)
  (cons : (tl : S) → (hd : SM) → motive tl → motive (tl ∷ hd))
  : (x : S) → motive x :=
  S.rec
    (motive_1 := motive)
    (motive_2 := λ _ ↦ True)
    nil
    (λ tl hd ih _ ↦ cons tl hd ih)
    (λ _ ↦ .intro)
    (λ _ _ ↦ .intro)

@[induction_eliminator]
theorem SM.induction {motive : SM → Prop}
  (atom : (a : M)  → motive (atom a))
  (list : (s : S) → (∀ x ∈ (list s), motive x) → motive (list s))
  : (α : SM) → motive α :=
  SM.rec
    (motive_1 := λ s ↦ ∀ x ∈ (SM.list s), motive x)
    (motive_2 := motive)
    (nil := nofun)
    (cons := λ _ _ ih1 ih2 _ el ↦ match el with | .here => ih2 | .there el' => ih1 _ el')
    (atom := atom)
    (list := list)

theorem mem_wf : WellFounded Mem := by
  constructor
  intro s
  induction s with
  | atom _ => constructor; intros; contradiction
  | list _ ih =>
    constructor
    intro _ p
    cases p with
    | here => apply ih; exact .here
    | there hh => apply ih; exact .there hh
