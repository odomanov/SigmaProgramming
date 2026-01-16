-- Доказательство фундирования для Mem - внутренний индукц.принцип
import Init.WF
import SigmaProgramming.Defs

namespace GES
variable [m : SModel]
open S SM

#print SM.rec
#print S.rec

theorem mem_wf : WellFounded SM.Mem := by
  constructor
  intro sm
  apply SM.rec
    (motive_1 := λ s ↦ ∀ x ∈ (list s), Acc Mem x)
    (motive_2 := λ x ↦ Acc Mem x)
  · nofun                                     -- nil
  · intro _ _ ih1 ih2 _ h                     -- cons
    cases h with
    | here => apply ih2
    | there el => apply ih1 _ el
  · intros; constructor; intro _ h; cases h   -- atom
  · intro _ ih; constructor; apply ih         -- list

-- другой способ
theorem mem_wf₁ : WellFounded SM.Mem := by
  constructor
  intro sm
  induction sm using SM.rec (motive_1 := λ s ↦ ∀ x ∈ (list s), Acc Mem x) with
  | nil => contradiction
  | cons _ _ ih1 ih2 _ h =>
    cases h with
    | here => apply ih2
    | there el => apply ih1 _ el
  | atom _ => constructor; intro _ h; cases h
  | list _ ih => constructor; apply ih

-- ещё способ
theorem mem_wf₂ : WellFounded SM.Mem :=
  WellFounded.intro (
    SM.rec
      (motive_1 := λ s ↦ ∀ x ∈ (list s), Acc Mem x)
      (motive_2 := λ x ↦ Acc Mem x)
      nofun                                     -- nil
      (λ _ _ ih1 ih2 x h ↦                     -- cons
        match h with
        | .here => ih2
        | .there el => ih1 x el)
      (λ a ↦ Acc.intro (atom a) nofun)               -- atom
      (λ s ih ↦ Acc.intro (list s) ih)               -- list
  )

-- Определяем элиминаторы для S, SM
@[induction_eliminator]
theorem S.induction {motive : S → Prop}
  (nil : motive nil)
  (cons : (tl : S) → (hd : SM) → motive tl → motive (tl ∷ hd))
  : (x : S) → motive x :=
  S.rec
    (motive_1 := motive)
    (motive_2 := λ _ ↦ True)
    (nil  := nil)
    (cons := λ tl hd ih _ ↦ cons tl hd ih)
    (atom := λ _ ↦ trivial)
    (list := λ _ _ ↦ trivial)

@[induction_eliminator]
theorem SM.induction {motive : SM → Prop}
  (atom : (a : M)  → motive (atom a))
  (list : (s : S) → (∀ x ∈ (list s), motive x) → motive (list s))
  : (α : SM) → motive α :=
  SM.rec
    (motive_1 := λ s ↦ ∀ x ∈ (SM.list s), motive x)
    (motive_2 := motive)
    (nil  := nofun)
    (cons := λ _ _ ih1 ih2 _ el ↦ match el with | .here => ih2 | .there el' => ih1 _ el')
    (atom := atom)
    (list := list)

-- доказательство с этими элиминаторами
theorem mem_wf' : WellFounded Mem := by
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
