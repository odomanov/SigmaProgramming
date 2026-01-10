-- Доказательство фундирования для Mem - через размер
import Init.WF
import SigmaProgramming.Defs

namespace GES
variable [m : SModel]
open S SM

mutual
  @[simp]
  def size_S : S → Nat
    | .nil => 0
    | .cons tl hd => 1 + size_S tl + size_SM hd
  @[simp]
  def size_SM : SM → Nat
    | .atom _ => 1
    | .list s => 1 + size_S s
end

theorem size_lt {y x : SM} (h : Mem y x) : size_SM y < size_SM x := by
  induction hh : h with
  | here => simp; rename_i α; cases size_S α ; linarith; linarith
  | there h' ih =>
    have hhh : ∀ α b, size_SM (list α) < size_SM (list (α ∷ b)) := by
      intro α b; simp; linarith
    rename_i α b
    exact Nat.lt_trans (ih h' rfl) (hhh α b)

theorem mem_wf : WellFounded Mem :=
  Subrelation.wf size_lt (WellFounded.onFun (wellFounded_lt))
