-- Доказательство фундирования для elem
import SigmaProgramming.Defs

namespace SigmaProg
variable [m : SMModel]

open SM SMM

-- Определяем свои элиминаторы для SM, SMM
@[induction_eliminator]
def SM.induction {motive : SM → Sort u}
  (nil : motive nil)
  (cons : (tl : SM) → (hd : SMM) → motive tl → motive (cons tl hd))
  : (x : SM) → motive x
    | .nil => nil
    | .cons tl hd => cons tl hd (SM.induction nil cons tl)

@[induction_eliminator]
def SMM.induction {motive : SMM → Sort u}
  (atom : (a : M)  → motive (atom a))
  (listn : motive (list nil))
  (listc : (tl : SM) → (hd : SMM) → motive (list tl) → motive hd → motive (list (cons tl hd)))
  : (x : SMM) → motive x
    | .atom a => atom a
    | .list nil => listn
    | .list (cons tl hd) =>
      listc tl hd (SMM.induction atom listn listc (list tl)) (SMM.induction atom listn listc hd)

theorem elem_nil : ∀ (y : SMM), ¬ elem y (list nil) := by intro _ _; trivial

theorem elem_wf : WellFounded elem := by
  constructor
  intro s
  induction s with
  | atom _ => constructor; intros; contradiction
  | listn => constructor; intros; contradiction
  | listc _ _ ih ih2 =>
    constructor
    intro _ p
    cases p with
    | here => exact ih2
    | there hh => exact Acc.inv ih hh
