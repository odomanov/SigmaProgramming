-- Функции для вывода (Repr, toString,...)
import SigmaProgramming.Defs

namespace GES
variable [m : SModel]
open S SM
open Std Format

mutual
  partial def S.rf : S → Nat → Format := λ xs n =>
   "⟨" ++ ", ".intercalate (.map (pretty ∘ (SM.rf · n)) xs.conv.reverse) ++ "⟩"

  partial def SM.rf : SM → Nat → Format
    | atom x, _ => repr x
    | list xs, n => xs.rf n

  partial def HLF.rf : HLF → Nat → Format := λ hs n =>
    ", ".intercalate (.map (pretty ∘ (SM.rf · n)) hs.conv_list.reverse)
end

instance : Repr S := ⟨S.rf⟩
instance : Repr SM := ⟨SM.rf⟩
instance : Repr HLF := ⟨HLF.rf⟩
