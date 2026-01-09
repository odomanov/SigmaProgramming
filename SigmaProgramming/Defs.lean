-- Goncharov S.S.; Sviridenko D.I. - Sigma-Programming. AMS (1989)
import Mathlib.Tactic

--== теория списочных расширений ==--

namespace GES

class SModel : Type (u + 1) where
  domain : Type u
  reprm : Repr domain

variable [m : SModel]

-- базовая модель
def M := m.domain
instance : Repr M := m.reprm

-- superstructure, list of lists
mutual
  inductive S where
  | nil : S
  | cons : S → SM → S    -- добавляем в конец списка

  inductive SM where
  | atom : M → SM
  | list : S → SM
end

-- Список можно было сделать параметрическим, как это обычно делается,
-- но будем держаться текста.

open S SM

@[match_pattern]
infixl:(min+1) " ∷ " => S.cons

@[simp]
def S.head : S → SM
| .nil => list .nil
| .cons _ α => α

@[simp]
def S.tail : S → S
| .nil => .nil
| .cons α _ => α

-- конкатенация
@[simp]
def S.conc : S → S → S
| α, nil => α
| α, cons β b => cons (conc α β) b

-- длина списка
@[simp]
def S.len : S → Nat
  | .nil => 0
  | .cons tl _ => len tl + 1

notation:max (priority := high) "‖" α "‖" => S.len α

-- предикат принадлежности для Membership
inductive SM.Mem : SM → SM → Prop where
| here : ∀ {a} {α}, Mem a (list (α ∷ a))
| there : ∀ {a} {α} {b}, Mem a (list α) → Mem a (list (α ∷ b))

scoped instance : Membership SM SM where
  mem := λ α β => SM.Mem β α

scoped instance : Membership SM S where
  mem := λ α β => SM.Mem β (list α)

-- тип элементов списка α
structure S.elems (α : S) where
  el : SM
  is_elem : el ∈ (list α)

def S.isList (α : SM) : Prop := if α matches .list _ then True else False
def S.nonNil (α : S)  : Prop := if α matches .nil then False else True

-- конверсия в List
def S.conv : S → List SM
| .nil => []
| .cons xs x => x :: xs.conv

-- начальный сегмент
inductive S.iniseg  : S → S → Prop where
| irefl : ∀ {α}, iniseg α α
| icons : ∀ {α} (tl : S) (hd : SM), iniseg α tl → iniseg α (tl ∷ hd)

scoped notation:min α " ⊑ " β => S.iniseg α β

-- тип начальных сегментов списка α
structure S.segs (α : S) where
  s : S
  is_seg : s ⊑ α

@[match_pattern]
def S.ORDPAIR α₁ α₂ := S.cons (S.cons S.nil (list α₁)) (list α₂)

scoped notation:arg "⦅ " α₁ "," α₂ " ⦆" => list (ORDPAIR α₁ α₂)

def isORDPAIR (s : S) : Prop := if s matches cons (cons nil _) _ then True else False


-- списки пар

inductive isPL : S → Prop where
| singl : (α₁ α₂ : S) → isPL (nil ∷ ⦅α₁,α₂⦆)
| cons : isPL (α ∷ ⦅α₁',α₂'⦆) → (α₁ α₂ : S) → isPL (α ∷ ⦅α₁',α₂'⦆ ∷ ⦅α₁,α₂⦆)

-- список + док-во, что он PL
structure PL where
  s : S
  is_pl : isPL s

@[simp]
def PL.base : (pl : PL) → S | ⟨α ∷ ⦅_,_⦆,_⟩ => α
@[simp]
def PL.fst : (pl : PL) → S | ⟨_ ∷ ⦅α₁,_⦆,_⟩ => α₁
@[simp]
def PL.snd : (pl : PL) → S | ⟨_ ∷ ⦅_,α₂⦆,_⟩ => α₂

@[simp]
theorem PL_eta : ∀ (p : PL), p.s = (p.base ∷ ⦅p.fst,p.snd⦆)
| ⟨_,.singl α₁ α₂⟩  => by simp
| ⟨_,.cons p α₁ α₂⟩ => by simp

def PL.singl (α₁ α₂ : S) : PL := ⟨_,.singl α₁ α₂⟩
def PL.cons (p : PL) (α₁ α₂ : S) : PL := ⟨_,.cons (PL_eta p ▸ p.is_pl) α₁ α₂⟩

@[match_pattern]
notation:(min+1) αₚ " ∷ " "⦅ " α₁ ", " α₂ " ⦆" => isPL.cons αₚ α₁ α₂

def PL.len (pl : PL) : Nat := ‖pl.s‖

inductive PL.iniseg : PL → PL → Prop where
| irefl : iniseg ⟨αs,p⟩ ⟨αs,p⟩
| icons (α α₁' α₂' : S) (p : isPL (α ∷ ⦅α₁',α₂'⦆))
  : iniseg αs ⟨α ∷ ⦅α₁',α₂'⦆,p⟩ → (α₁ α₂ : S)
  → iniseg αs ⟨α ∷ ⦅α₁',α₂'⦆ ∷ ⦅α₁,α₂⦆,.cons p α₁ α₂⟩
-- | irefl : iniseg p p
-- | icons (p : PL) : iniseg p₀ p → (α₁ α₂ : S) → iniseg p₀ (p.cons α₁ α₂)

scoped notation:min α " ⊑ " β => PL.iniseg α β

scoped instance : Membership SM PL where
  mem := λ α β => SM.Mem β (list α.s)


--== наследственные списочные функции ==--

-- Предикат проверки, что список есть HLF. HLF никогда не пуст.
-- Здесь S всегда имеет вид α ∷ ⦅α₁,α₂⦆, т.е PL.s.
inductive isHLF : PL → Prop where
| nil : isHLF ⟨nil ∷ ⦅nil,nil⦆,.singl nil nil⟩
-- | cons : isHLF p → (a b : SM)
--   → isHLF (.cons p (p.fst ∷ a) (p.snd ∷ b))       -- добавляем b
-- | pass : isHLF p → (a : SM)
--   → isHLF (.cons p (p.fst ∷ a) p.snd)           -- не добавляем ничего
| cons : isHLF ⟨α ∷ ⦅α₁,α₂⦆,p⟩ → (a b : SM) → isHLF ⟨_,p ∷ ⦅α₁ ∷ a, α₂ ∷ b⦆⟩
| pass : isHLF ⟨α ∷ ⦅α₁,α₂⦆,p⟩ → (a : SM)   → isHLF ⟨_,p ∷ ⦅α₁ ∷ a, α₂⦆⟩

-- HLF = PL + док-во, что он HLF
structure HLF where
  pl : PL
  is_hlf : isHLF pl

@[simp]
def HLF.s (hlf : HLF) : S := hlf.pl.s
@[simp]
def HLF.base (hlf : HLF) : S := hlf.pl.base
@[simp]
def HLF.fst (hlf : HLF) : S := hlf.pl.fst
@[simp]
def HLF.snd (hlf : HLF) : S := hlf.pl.snd

@[simp]
theorem HLF_eta : ∀ (hlf : HLF), hlf.s = (hlf.base ∷ ⦅hlf.fst,hlf.snd⦆)
| ⟨_,.nil⟩  => by simp
| ⟨_,.cons p a b⟩ => by simp   --dsimp; simp
| ⟨_,.pass p a⟩ => by simp     --dsimp; simp

@[simp]
theorem HLF_eta' : ∀ (hlf : HLF), hlf.pl = ⟨hlf.base ∷ ⦅hlf.fst,hlf.snd⦆,PL_eta hlf.pl ▸ hlf.pl.is_pl⟩
| ⟨_,.nil⟩  => by simp
| ⟨_,.cons p a b⟩ => by simp    --dsimp; unfold PL.cons; simp_all
| ⟨_,.pass p a⟩ => by simp      --dsimp; unfold PL.cons; simp_all

def HLF.nil : HLF := ⟨_,.nil⟩
def HLF.cons (hlf : HLF) (a b : SM) : HLF := ⟨_,.cons (HLF_eta' hlf ▸ hlf.is_hlf) a b⟩
def HLF.pass (hlf : HLF) (a : SM) : HLF := ⟨_,.pass (HLF_eta' hlf ▸ hlf.is_hlf) a⟩

-- отношение для Membership
inductive HLF.Mem : SM → HLF → Prop where
| elnil : Mem ⦅.nil,.nil⦆ ⟨_,.nil⟩
| herec {ish: isHLF ⟨α ∷ ⦅α₁,α₂⦆,p⟩}
  : Mem ⦅α₁∷a,α₂∷b⦆ ⟨⟨α ∷ ⦅α₁,α₂⦆ ∷ ⦅α₁∷a,α₂∷b⦆,_⟩,.cons ish a b⟩
| herep {ish : isHLF ⟨α ∷ ⦅α₁,α₂⦆,p⟩}
  : Mem ⦅α₁∷a,α₂⦆ ⟨⟨α ∷ ⦅α₁,α₂⦆ ∷ ⦅α₁∷a,α₂⦆,_⟩,.pass ish a⟩
| therec : Mem x ⟨_,ish⟩ → Mem x ⟨_,.cons ish a b⟩
| therep : Mem x ⟨_,ish⟩ → Mem x ⟨_,.pass ish a⟩

instance : Membership SM HLF where
  mem := λ α β => HLF.Mem β α

def HLF.conv (hlf : HLF) : S := hlf.pl.s
def HLF.conv_list (hlf : HLF) : List SM := hlf.pl.s.conv

@[simp]
def isHLF.getα {pl : PL} (_ : isHLF pl) : S := pl.s
@[simp]
def HLF.getα (x : HLF) : S := x.pl.s

@[simp]
def isHLF.getβ {pl : PL} (_ : isHLF pl) : S := pl.fst
@[simp]
def HLF.getβ (x : HLF) : S := x.pl.fst
