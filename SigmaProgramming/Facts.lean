-- Некоторые факты для использования в других модулях
import Mathlib.Tactic
import SigmaProgramming.Defs
set_option pp.proofs true

namespace GES
variable [m : SModel]
open S SM

-- теоремы о длинах

theorem iniseg_len_le {α β : S} (h : α ⊑ β) : ‖α‖ ≤ ‖β‖ := by
  induction h with
  | irefl => exact Nat.le_refl ‖α‖
  | icons _ _ _ ih => exact Nat.le_succ_of_le ih
-- см. также asymm ниже
theorem iniseg_len_eq {α β : S} (hαβ : α ⊑ β) (hβα : β ⊑ α) : ‖α‖ = ‖β‖ :=
  have hαβ_len := iniseg_len_le hαβ
  have hβα_len := iniseg_len_le hβα
  Nat.le_antisymm hαβ_len hβα_len
-- cons увеличивает длину
theorem len_cons (tl : S) (hd : SM) : ‖cons tl hd‖ = ‖tl‖ + 1 := rfl
theorem iniseg_len_cons {αs tl : S} {hd : SM} (h : αs ⊑ tl) : ‖αs‖ < ‖cons tl hd‖ := by
  have := iniseg_len_le h
  simpa using Nat.lt_succ_of_le this
theorem len_neq {α β : S} : ‖α‖ ≠ ‖β‖ → α ≠ β := by
  contrapose; intro h; congr

-- теоремы о принадлежности ∈

theorem elem_head_cons : hd ∈ list (cons tl hd) := .here
theorem elem_cons_head (α : S) (nnil : α ≠ nil) : head α ∈ list α := by
  cases α
  · trivial
  · exact .here

theorem elem_nil : ∀ (β : SM), ¬ Mem β (list nil) := by intro _ _; trivial


-- теоремы о конкатенации

theorem conc_nil : ∀ β βs, conc .nil βs = βs → conc .nil (cons βs β) = cons βs β := by
    intro β βs eq
    cases β <;> rw [conc,eq]

-- теоремы о начальных сегментах

theorem iniseg_cons : (cons tl hd ⊑ α) → (tl ⊑ α) := by
  intro pi
  cases pi with
  | irefl => exact .icons _ _ .irefl
  | icons _ _ pi' => exact .icons _ _ (iniseg_cons pi')
theorem iniseg_elem_head : (cons tl hd ⊑ α) → hd ∈ list α := by
  intro pi
  cases pi with
  | irefl => exact .here
  | icons _ _ pi' => exact .there (iniseg_elem_head pi')
theorem iniseg_tail_right {α β : S}  (neq : α ≠ β) : (α ⊑ β) → (α ⊑ tail β) := by
  intro pi
  cases pi with
  | irefl => contradiction
  | icons _ _ pi' => exact pi'
theorem iniseg_tail_left {α β : S} : (α ⊑ β) → (tail α ⊑ β) := by
  intro pi
  cases pi with
  | irefl =>
    cases α
    · exact .irefl
    · exact .icons _ _ .irefl
  | icons _ _ h' => exact .icons _ _ (iniseg_tail_left h')
theorem iniseg_tail : (cons αs αh ⊑ cons βs βh) → (αs ⊑ βs) := by
  intro pi
  cases pi with
  | irefl => exact .irefl
  | icons _ _ pi' => exact iniseg_cons pi'
theorem iniseg_cons_right {α tl : S} {hd : SM} : (α ⊑ tl) → (α ⊑ cons tl hd) := .icons _ hd

-- Свойства отношения ⊑

-- рефлексивность
theorem refl {α : S} : α ⊑ α := .irefl

-- антисимметричность
theorem asymm {α β : S} (hαβ : α ⊑ β) (hβα : β ⊑ α) : α = β := by
  have len_eq : ‖α‖ = ‖β‖ := iniseg_len_eq hαβ hβα
  induction hβα with
  | irefl => rfl
  | icons tl hd hαβ' ih =>
    have hle : ‖β‖ ≤ ‖tl‖ := iniseg_len_le hαβ'
    have : False := by
      have := Nat.lt_of_le_of_lt hle (Nat.lt_succ_self _)
      rw [← len_eq] at this
      apply Nat.lt_irrefl (‖tl‖ + 1)
      exact this
    contradiction

-- транзитивность
theorem iniseg.trans {α β γ : S} (hαβ : α ⊑ β) (hβγ : β ⊑ γ) : (α ⊑ γ) := by
  match hβγ with
  | .irefl => exact hαβ
  | .icons _ _ hβγ' => exact .icons _ _ (trans hαβ hβγ')

-- полнота (для нач.сегментов одного списка X)
theorem compl {X α β : S} : (α ⊑ X) → (β ⊑ X) → (α ⊑ β) ∨ (β ⊑ α) := by
  intro hα hβ
  induction hαeq : hα with
  | irefl => exact Or.inr hβ
  | icons _ hd p ih =>
    cases hβ with
    | irefl => exact Or.symm (Or.inr hα)
    | icons _ hd' p' => exact ih p p' rfl

-- другая формулировка
theorem compl' : ∀ (αs βs : segs X), (αs.s ⊑ βs.s) ∨ (βs.s ⊑ αs.s) :=
  λ αs βs => compl αs.is_seg βs.is_seg

-- свойства HLF

-- HLF никогда не пусто
theorem hlf_nonnil (hlf : HLF) : hlf.s ≠ .nil := by
  let ⟨s,p⟩ := hlf
  cases p with
  | nil => simp
  | cons p' _ _ => simp
  | pass p' _ => simp

theorem mem_hlf_s : ∀ (hlf : HLF), x ∈ hlf → x ∈ hlf.s
  | _, .elnil => .here
  | _, .herec => .here
  | _, .herep => .here
  | _, .therec e => .there <| (mem_hlf_s _) e
  | _, .therep e => .there <| (mem_hlf_s _) e

-- PL не может быть пуст
theorem PL_nnil : ∀ pl : PL, pl.s ≠ nil := nofun

theorem iniseg.nil_all : ∀ (α : S), nil ⊑ α
| nil => .irefl
| cons tl _ => .icons _ _ (nil_all tl)

theorem isPL_of_last (p : isPL (s ∷ s₁ ∷ x)) : isPL (s ∷ s₁) := by
  cases p; assumption

theorem PL.s_eq_eqv {α β : PL} : α.s = β.s ↔ α = β := by
  constructor
  · generalize hb : β.s = y
    intro h
    induction h with
    | refl => cases α with | mk _ _ => cases β with | mk _ _ =>
      congr; simp at hb; exact hb.symm
  · intro h; congr

theorem PL.s_neq_eqv {α β : PL} : α.s ≠ β.s ↔ α ≠ β := by
  constructor
  · generalize hb : β.s = y
    intro h hh
    induction hh with
    | refl => cases α with | mk _ _ => cases β with | mk _ _ =>
      contradiction
  · intro h hh; have := PL.s_eq_eqv.mp hh; contradiction

lemma PL.len_ge_1 (α : PL) : 1 ≤ α.len := by
  match α with
  | ⟨_,.singl _ _⟩ => simp [PL.len]
  | ⟨_,.cons _ _ _⟩ => simp [PL.len]

theorem PL.s_iniseg {α β : PL} : (α ⊑ β) ↔ (α.s ⊑ β.s) := by
  constructor
  · intro h; induction h with
    | irefl => exact .irefl
    | icons _ _ _ _ _ _ _ ih => exact .icons _ _ ih
  · intro h
    generalize hb : β.s = y
    rw [hb] at h
    induction hh : h generalizing β with
    | irefl => exact PL.s_eq_eqv.mp hb.symm ▸ .irefl
    | icons tl hd ini ih => cases hβ : β with | mk βs βp =>
      revert βp
      generalize hgen : βs = x
      intro βp βeq
      cases hβp : βp with
      | singl α₁ α₂ =>
        have hhh := βeq ▸ hb
        simp [*] at hhh
        let ⟨tl_nil,hd_pair⟩ := hhh
        rw [←tl_nil] at ini
        have le : ‖α.s‖ ≤ ‖nil‖ := iniseg_len_le ini
        simp [S.len] at le
        have ge : 1 ≤ ‖α.s‖ := PL.len_ge_1 α
        linarith
      | cons prev_p α₁ α₂ =>
        rename_i α' α₁' α₂'
        have hhh := βeq ▸ hb
        simp [*] at hhh
        let ⟨tl_eq,hd_eq⟩ := hhh
        let β' : PL := ⟨tl, tl_eq ▸ prev_p⟩
        have sub_ini : α ⊑ β' := ih (β:=β') ini rfl rfl
        subst β'; subst tl_eq
        exact inisegPL.icons α' α₁' α₂' prev_p sub_ini α₁ α₂

-- = PL.fst !
theorem PL.get_fst
  : ({ s := _ ∷ ⦅α₁,α₂⦆, is_pl := p ∷ ⦅α₁,_⦆ } : PL).fst = α₁ := by
  dsimp [PL.fst]

theorem inisegPL_cons {α α₁ α₂ : S} {pl : PL} {p : isPL (α ∷ ⦅α₁',α₂'⦆)}
  : (⟨_, .cons p α₁ α₂⟩ ⊑ pl) → (⟨_,p⟩ ⊑ pl) := by
  intro ini
  cases ini with
  | irefl => exact .icons _ _ _ _ .irefl _ _
  | icons _ _ _ _ ini' _ _ => exact .icons _ _ _ _ (inisegPL_cons ini') _ _

theorem isPL.inner : isPL (α ∷ hd1 ∷ hd2) → isPL (α ∷ hd1) := by
  intro h; cases h; assumption

theorem inisegPL.trans {α β γ : PL} (ini1 : α ⊑ β) (ini2 : β ⊑ γ) : α ⊑ γ := by
  induction ini2 with
  | irefl => exact ini1
  | icons _ _ _ ini' _ _ _ ih => exact inisegPL.icons _ _ _ ini' (ih ini1) _ _

-- Лемма: Приращение в HLF всегда сохраняет iniseg для компонентов
theorem isHLF.step_mono {p : isPL (α ∷ ⦅α₁', α₂'⦆ ∷ ⦅α₁, α₂⦆)}
  (ish : isHLF ⟨_, p⟩) : α₁' ⊑ α₁ := by
  cases ish with
  | cons _ _ _ => exact .icons α₁' _ .irefl
  | pass _ _ => exact .icons α₁' _ .irefl

-- Лемма: если префикс плавно растет до pl по правилам isHLF,
-- то его fst является префиксом для fst итогового pl.
-- theorem isHLF_fst_mono {pl : PL} (ish : isHLF pl) {α' : PL} (ini : α' ⊑ pl) :
--   α'.fst ⊑ pl.fst := by
--   induction hi : ini with
--   | irefl => exact .irefl
--   | icons α₀ α₀₁' α₀₂' p_inner ini_step α₀₁ α₀₂ ih =>
--     -- Здесь ih : α'.fst ⊑ ⟨α₀ ∷ ⦅α₀₁', α₀₂'⦆, p_inner⟩.fst
--     -- Нам нужно доказать α'.fst ⊑ (⟨α₀ ∷ ⦅α₀₁', α₀₂'⦆ ∷ ⦅α₀₁, α₀₂⦆, ...⟩).fst

--     -- Вот тут нам и нужно заглянуть внутрь isHLF, чтобы понять,
--     -- как α₀₁ (новый fst) соотносится с α₀₁' (старый fst).

--     -- Но ish — это доказательство для ИТОГОВОГО pl.
--     -- Чтобы использовать его для α₀, нам нужно сначала "откатить" ish.
--     -- В Lean это делается через инверсию (cases ish).

--     -- generalize hpl : pl =xp
--     -- revert α₀₁ α₀₂ ish
--     -- intro α₀₁ α₀₂ ish ini'' eqini''
--     cases h_ish : ish with
--     -- | nil =>
--     --   -- Случай nil невозможен для конструктора icons (т.к. icons добавляет блоки),
--     --   -- Lean может потребовать это доказать или сделает это сам через противоречие.
--     --   contradiction
--     | cons ish_prev a b =>
--       -- Здесь магия имен: Lean сопоставит паттерн из isHLF.cons
--       -- с текущей структурой pl из icons.
--       -- Вы увидите, что α₀₁ = α₀₁' ∷ a
--       -- injection h_ish with _ h_s_eq
--       -- -- h_s_eq будет чем-то вроде (α₀ ∷ ⦅α₀₁', α₀₂'⦆ ∷ ⦅α₀₁, α₀₂⦆) = (αₚ ∷ ⦅α₁ ∷ a, α₂ ∷ b⦆)
--       -- injection h_s_eq with _ _ h_tail_eq
--       -- injection h_tail_eq with h_fst_eq
--       dsimp [PL.fst]
--       -- Нам нужно доказать: α''.fst ⊑ ⟨α₀₁, p_α₀₁⟩
--       -- У нас есть ih : α''.fst ⊑ ⟨α₀₁', p_α₀₁'⟩

--       -- Определим промежуточный PL для транзитивности
--       let pl_prev_fst : PL := ⟨α₀₁', isPL_of_HLF_prev ish_prev⟩ -- нам нужно доказать, что α₀₁' корректен

--       apply inisegPL.trans (β := pl_prev_fst)
--       · exact ih ini_step
--       · -- Осталось доказать ⟨α₀₁', ...⟩ ⊑ ⟨α₀₁' ∷ a, ...⟩
--         -- Это конструктор icons для отношения ⊑
--         exact inisegPL.icons _ _ _ _ .irefl _ _

--   | pass ish_prev a =>
--     -- Аналогично для случая pass
--     sorry

-- нач.сегменты HLF -- также HLF
-- см. ниже
-- theorem isHLF_of_iniseg : ∀ {pl : PL} (_ : isHLF pl) {α' : PL},
--   (α' ⊑ pl) → isHLF α' := by
--   intro pl ish α' ini
--   induction ini with
--   | irefl => exact ish
--   | icons α₀ α₀₁' α₀₂' p_inner ini_step α₀₁ α₀₂ ih =>
--     cases ish with
--     | cons ish_prev a b => exact ih ish_prev
--     | pass ish_prev a => exact ih ish_prev

-- theorem PL.sub_fst : ∀ {pl} (ish : isHLF pl) {α' α'' : PL},
--   (α' ⊑ pl) → (α'' ⊑ α') → (α''.fst ⊑ α'.fst)
--   := sorry

theorem PL_trans {pl α' α'' : PL} (ini'' : α'' ⊑ α') (ini' : α' ⊑ pl) : (α'' ⊑ pl) := by
  induction ini' with
  | irefl => exact ini''
  | icons _ _ _ _ _ _ _ ih => exact inisegPL.icons _ _ _ _ (ih ini'') _ _

-- префикс HLF списка также является HLF
theorem isHLF_iniseg {α β : PL} (h : α ⊑ β) (ish : isHLF β) : isHLF α := by
  induction hh : h with
  | irefl => exact ish
  | icons tl α₁' α₂' p ini α₁ α₂ ih =>
    cases hi : ish with
    | cons ish_prev => exact ih ini ish_prev rfl
    | pass ish_prev => exact ih ini ish_prev rfl

-- theorem PL_iniseg (ish : isHLF pl) :
--   ∀ (αₚ' αₚ'' : PL), (αₚ' ⊑ pl) → (αₚ'' ⊑ αₚ') → (αₚ''.fst ⊑ αₚ'.fst) := by
--   intro αₚ' αₚ'' ini' ini''
--   match ha' : αₚ', ha'' : αₚ'', hini'' : ini'' with
--   | _, _, .irefl => exact .irefl
--   | _, ⟨α₂ ∷ ⦅hd1,hd2⦆,p₂⟩, .icons α' α₁' α₂' ini1 _ _ _ =>
--     -- have p' : isPL α' := by assumption
--     expose_names
--     have ini2 : ⟨α',_⟩ ⊑ pl := inisegPL_cons ini'
--     -- have p' : isPL (α' ∷ ⦅α₁',α₂'⦆) := by assumption
--     -- have ini2 : ⟨α' ∷ ⦅α₁',α₂'⦆,p'⟩ ⊑ pl := sorry  --inisegPL_cons ini'
--     have := PL_iniseg ish _ _ ini2 ini1
--     -- exact .icons _ _ this --<| PL_iniseg ish ⟨α',p⟩ x ini2 ini1
--     rw [PL.get_fst,PL.get_fst]
--     refine .icons α₁' ?_ this
