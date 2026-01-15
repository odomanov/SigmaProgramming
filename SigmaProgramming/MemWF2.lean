-- Доказательство фундирования для Mem - через размер
import Init.WF
import SigmaProgramming.Defs

namespace GES
variable [m : SModel]
open S SM

-- Используем автоматические sizeOf

#synth SizeOf S
#synth SizeOf SM

theorem size_lt {y x : SM} (h : Mem y x) : sizeOf y < sizeOf x := by
  induction hh : h with
  | here => simp; rename_i α; cases sizeOf α ; linarith; linarith
  | there h' ih =>
    have hhh : ∀ α b, sizeOf (list α) < sizeOf (list (α ∷ b)) := by
      intro α b; simp; linarith
    rename_i α b
    exact Nat.lt_trans (ih h' rfl) (hhh α b)

theorem mem_wf : WellFounded Mem :=
  Subrelation.wf size_lt (WellFounded.onFun (wellFounded_lt))
