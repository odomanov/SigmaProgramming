-- Доказательство фундирования для Mem - внутренний индукц.принцип
import Init.WF
import SigmaProgramming.Defs

namespace GES
variable [m : SModel]
open S SM

#print SM.rec

theorem mem_wf : WellFounded SM.Mem := by
  constructor
  intro s
  apply SM.rec
    (motive_1 := fun s => ∀ x ∈ (list s), Acc Mem x)
    (motive_2 := fun sm => Acc Mem sm)
  · -- nil
    nofun
  · -- cons
    intro _ _ ih1 ih2 _ h
    cases h with
    | here => exact ih2
    | there el => apply ih1; exact el
  · -- atom
    intros; constructor; intro _ h; cases h
  · -- list
    intro a ih
    constructor
    apply ih
