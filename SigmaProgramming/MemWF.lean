-- Доказательство фундирования для Mem - внутренний индукц.принцип
import Init.WF
import SigmaProgramming.Defs

namespace GES
variable [m : SModel]
open S SM

#print SM.rec

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
