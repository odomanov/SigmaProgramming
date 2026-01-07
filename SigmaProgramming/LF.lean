-- Доказательство выполнения свойства LF
import SigmaProgramming.Defs
import SigmaProgramming.Facts

namespace GES
variable [m : SModel]
open S SM

-- для любой δ существует пара γ, в которой δ будет первым элементом
theorem LF_cond1 (ish : isHLF pl)
  : ∀ δ, (δ ⊑ ish.getβ) → ∃ γ, (γ ∈ ish.getα) ∧ (∃ ε, ⦅δ,ε⦆ = γ) := by
  induction hi : ish with
  -- β = nil, δ = nil
  | nil =>
    intro δ ini
    have : δ = .nil := by cases ini; rfl
    exists ⦅nil,nil⦆
    constructor
    · simp; exact .here
    · exists nil; simp [this]
  | cons ish' a b ih =>
    rename_i α' α₁' α₂' p
    intro δ ini
    -- упрощаем ini перед match
    simp [isHLF.getβ,PL.fst] at ini
    rw [isHLF.getα]
    match hini : ini with
    | .irefl =>
      exists ⦅δ ,α₂'∷b⦆
      constructor
      · simp; exact .here
      · exists α₂' ∷ b
    | .icons tl hd ini' =>
      have h_eq : (ish'.getβ ∷ a) = (tl ∷ hd) := by assumption
      injection h_eq with h_tl h_hd
      rw [← h_tl] at ini'
      obtain ⟨γ, hmem, ⟨ε, heq⟩⟩ := ih ish' rfl δ ini'
      exact ⟨γ,.there hmem, ⟨ε, heq⟩⟩

  -- структура док-ва та же, что и для cons
  | pass ish' a ih =>
    rename_i α' α₁' α₂' p
    intro δ ini
    -- упрощаем ini перед match
    simp [isHLF.getβ,PL.fst] at ini
    rw [isHLF.getα]
    match hini : ini with
    | .irefl =>
      exists ⦅δ ,α₂'⦆
      constructor
      · simp; exact .here
      · exists α₂'
    | .icons tl hd ini' =>
      have h_eq : (ish'.getβ ∷ a) = (tl ∷ hd) := by assumption
      injection h_eq with h_tl h_hd
      rw [← h_tl] at ini'
      obtain ⟨γ, hmem, ⟨ε, heq⟩⟩ := ih ish' rfl δ ini'
      exact ⟨γ,.there hmem, ⟨ε, heq⟩⟩

theorem LF_cond2 (ish : isHLF pl)
  : ∀ (α' α'' : PL), (α' ⊑ pl) → (α'' ⊑ α')
    → ∃ δ' δ'', (δ' = α'.fst) ∧ (δ'' = α''.fst) ∧ (δ'' ⊑ δ')
      ∧ (α' ≠ α'' ↔ δ' ≠ δ'') := by
  induction ish with
  | nil =>
    intro α' α'' hαp' hαp''
    cases hαp' with | irefl => cases hαp'' with | irefl =>
      use nil, nil; simp [PL.fst]; exact .irefl
  | cons ish_prev a b ih =>
    rename_i α α1 α2 p
    let pl_prev : PL := ⟨α ∷ ⦅α1, α2⦆, p⟩
    have eq_prev : pl_prev.fst = α1 := rfl
    intro α' α'' hαp' hαp''
    cases hαp' with
    | irefl =>
      cases hαp'' with
      | irefl =>
        use (α1 ∷ a), (α1 ∷ a)
        and_intros; rfl; rfl; exact .irefl; simp
      | icons _ _ _ _ h_inner _ _ =>
        let ⟨δ₁, δ₂, hδ₁, hδ₂, hδ₃, hδ₄⟩ := ih pl_prev α'' .irefl h_inner
        use (α1 ∷ a), α''.fst
        and_intros
        · simp [PL.fst]
        · rfl
        · rw [←hδ₂,←eq_prev,←hδ₁]; exact .icons _ _ hδ₃
        · constructor
          · intro _
            have hlen_le : ‖α''.fst‖ ≤ ‖α1‖ := iniseg_len_le (hδ₂ ▸ eq_prev ▸ hδ₁ ▸ hδ₃)
            have hlen_ne : ‖α1 ∷ a‖ = ‖α1‖ + 1 := by simp [S.len]
            have : ‖α1 ∷ a‖ ≠ ‖α''.fst‖ := by linarith
            exact len_neq this
          · intro hne heq
            rw [←heq] at hne
            contradiction
    | icons _ _ _ _ h_inner _ _ => exact ih α' α'' h_inner hαp''
  | pass ish_prev a ih =>
    rename_i α α1 α2 p
    let pl_prev : PL := ⟨α ∷ ⦅α1, α2⦆, p⟩
    have eq_prev : pl_prev.fst = α1 := rfl
    intro α' α'' hαp' hαp''
    cases hαp' with
    | irefl =>
      cases hαp'' with
      | irefl =>
        use (α1 ∷ a), (α1 ∷ a)
        and_intros; rfl; rfl; exact .irefl; simp
      | icons _ _ _ _ h_inner _ _ =>
        let ⟨δ₁, δ₂, hδ₁, hδ₂, hδ₃, hδ₄⟩ := ih pl_prev α'' .irefl h_inner
        use (α1 ∷ a), α''.fst
        and_intros
        · simp [PL.fst]
        · rfl
        · rw [←hδ₂,←eq_prev,←hδ₁]; exact .icons _ _ hδ₃
        · constructor
          · intro _
            have hlen_le : ‖α''.fst‖ ≤ ‖α1‖ := iniseg_len_le (hδ₂ ▸ eq_prev ▸ hδ₁ ▸ hδ₃)
            have hlen_ne : ‖α1 ∷ a‖ = ‖α1‖ + 1 := by simp [S.len]
            have : ‖α1 ∷ a‖ ≠ ‖α''.fst‖ := by linarith
            exact len_neq this
          · intro hne heq
            rw [←heq] at hne
            contradiction
    | icons _ _ _ _ h_inner _ _ => exact ih α' α'' h_inner hαp''

-- def pfst (pl : PL) (γ : SM) (el : γ ∈ pl.s) : S := by
--   revert el
--   match pl with
--   | ⟨_, .singl α₁ α₂⟩ =>
--     intro el
--     simp [Membership.mem] at el
--     cases el with
--     | here =>
--       simp [S.ORDPAIR] at *
--       exact α₁
--   | ⟨_, .cons isp α₁ α₂⟩ =>
--     intro el
--     simp [Membership.mem] at el
--     cases el with
--     | here =>
--       simp [S.ORDPAIR] at *
--       exact α₁
--     | there el' =>
--       exact pfst ⟨_, isp⟩ γ el'

def pfst : SM → S
| list ( cons ( cons nil (list α₁)) (list _)) => α₁
| _ => nil
def psnd : SM → S
| list ( cons ( cons nil (list _)) (list α₂)) => α₂
| _ => nil

theorem HLF_cond1 (ish : isHLF pl)
  : ∀ γ ∈ ish.getα, (pfst γ = nil → psnd γ = nil) := by
  simp only [isHLF.getα]
  induction ish with
  | nil =>
    intro γ el
    simp [Membership.mem] at el
    cases he : el with
    | here => simp [pfst,psnd]
    | there el' => simp [pfst,psnd]; contradiction
  | cons ish' a b ih =>
    intro γ el
    simp [Membership.mem] at el
    cases he : el with
    | here => simp [pfst,psnd]
    | there el' => simp [pfst,psnd]; exact ih γ el'
  | pass ish' a ih =>
    intro γ el
    simp [Membership.mem] at el
    cases he : el with
    | here => simp [pfst,psnd]
    | there el' => simp [pfst,psnd]; exact ih γ el'

theorem HLF_cond2 (ish : isHLF pl)
  : ∀ α₁ α₂, (⦅α₁,α₂⦆ ∈ ish.getα ∧ ∃ α₁' a, α₁ = (α₁' ∷ a))
  → (∃ α₂' b, α₂ = (α₂' ∷ b) ∧ ⦅α₁',α₂'⦆ ∈ ish.getα)
    ∨ (∃ α₂', α₂ = α₂' ∧ ⦅α₁',α₂'⦆ ∈ ish.getα) := by
    intro α₁ α₂ x
    obtain ⟨el,⟨α₁',a,eq⟩ ⟩ := x
    rw [isHLF.getα] at el
    cases hp : pl with | mk s isp =>

    injection x at x
    constructor
    · and_intros



  done
