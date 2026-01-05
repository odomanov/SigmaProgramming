-- Доказательство фундирования для Mem
import SigmaProgramming.Defs

namespace GES
variable [m : SModel]
open S SM

-- Определяем элиминаторы для S, SM
@[induction_eliminator]
def S.induction {motive : S → Sort u}
  (nil : motive nil)
  (cons : (tl : S) → (hd : SM) → motive tl → motive (tl ∷ hd))
  : (x : S) → motive x
    | .nil => nil
    | .cons tl hd => cons tl hd (S.induction nil cons tl)

@[induction_eliminator]
def SM.induction {motive : SM → Sort u}
  (atom : (a : M)  → motive (atom a))
  (listn : motive (list nil))
  (listc : (tl : S) → (hd : SM) → motive (list tl) → motive hd
    → motive (list (tl ∷ hd)))
  : (α : SM) → motive α
    | .atom a => atom a
    | .list nil => listn
    | .list (tl ∷ hd) =>
      listc tl hd (SM.induction atom listn listc (list tl))
      (SM.induction atom listn listc hd)

theorem mem_wf : WellFounded Mem := by
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
