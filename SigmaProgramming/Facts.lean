-- Некоторые факты - для использования в других модулях
import SigmaProgramming.Defs

namespace SigmaProg
variable [m : SMModel]

open SM SMM

-- теоремы о длинах

theorem iniseg_len_le {x y : SM} (h : x ⊑ y) : ‖x‖ ≤ ‖y‖ := by
  induction h with
  | nn => exact Nat.le_refl ‖x‖
  | n2 _ _ ih => exact Nat.le_succ_of_le ih
-- см. asymm ниже
theorem iniseg_len_eq (hxy : x ⊑ y) (hyx : y ⊑ x) : ‖x‖ = ‖y‖ :=
  have hxy_len := iniseg_len_le hxy
  have hyx_len := iniseg_len_le hyx
  Nat.le_antisymm hxy_len hyx_len
-- cons увеличивает длину
theorem len_cons (tl : SM) (hd : SMM) : ‖cons tl hd‖ = ‖tl‖ + 1 := rfl
theorem iniseg_len_cons (h : xs ⊑ tl) : ‖xs‖ < ‖cons tl hd‖ := by
  have := iniseg_len_le h
  simpa using Nat.lt_succ_of_le this

-- теоремы о принадлежности ∈

theorem elem_head_cons : hd ∈ list (cons tl hd) := .here
theorem elem_cons_head (x : SM) (nnil : nonNil x) : head x ∈ list x := by
  cases x
  · trivial
  · exact .here

-- теоремы о конкатенации

theorem conc_nil : ∀ y ys, conc .nil ys = ys → conc .nil (cons ys y) = cons ys y := by
    intro y ys eq
    cases y <;> rw [conc,eq]

-- теоремы о начальных сегментах

theorem iniseg_cons : (cons tl hd ⊑ x) → (tl ⊑ x) := by
  intro pi
  cases pi with
  | nn => exact .n2 _ .nn
  | n2 _ pi' => exact .n2 _ (iniseg_cons pi')
theorem iniseg_elem_head : (cons tl hd ⊑ x) → hd ∈ list x := by
  intro pi
  cases pi with
  | nn => exact .here
  | n2 _ pi' => exact .there (iniseg_elem_head pi')
theorem iniseg_tail_right  (neq : x ≠ y) : (x ⊑ y) → x ⊑ tail y := by
  intro pi
  cases pi with
  | nn => contradiction
  | n2 _ pi' => exact pi'
theorem iniseg_tail_left : (x ⊑ y) → (tail x ⊑ y) := by
  intro pi
  cases pi with
  | nn =>
    cases x
    · exact .nn
    · exact .n2 _ .nn
  | n2 _ h' => exact .n2 _ (iniseg_tail_left h')
theorem iniseg_tail : (cons xs xh ⊑ cons ys yh) → xs ⊑ ys := by
  intro pi
  cases pi with
  | nn => exact .nn
  | n2 hd pi' => exact iniseg_cons pi'

-- Свойства отношения ⊑

-- рефлексивность
theorem refl : xs ⊑ xs := .nn

-- антисимметричность
theorem asymm (hxy : x ⊑ y) (hyx : y ⊑ x) : x = y := by
  have len_eq : ‖x‖ = ‖y‖ := iniseg_len_eq hxy hyx
  induction hyx with
  | nn => rfl
  | n2 _ hxy' ih =>
    expose_names
    have hle : ‖y‖ ≤ ‖tl‖ := iniseg_len_le hxy'
    have : False := by
      have := Nat.lt_of_le_of_lt hle (Nat.lt_succ_self _)
      rw [← len_eq] at this
      apply Nat.lt_irrefl (‖tl‖ + 1)
      exact this
    exact False.elim this

-- транзитивность
theorem trans  (hxy : xs ⊑ ys) (hyz : ys ⊑ zs) : (xs ⊑ zs) := by
  match hyz with
  | .nn => exact hxy
  | .n2 hd hyz' => exact .n2 hd (trans hxy hyz')
