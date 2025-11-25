-- Goncharov S.S.; Sviridenko D.I. - Sigma-Programming. AMS (1989)

namespace SigmaProg

class SMModel : Type (u + 1) where
  domain : Type u
  beqm : BEq domain

variable [m : SMModel]

def M := m.domain
instance : BEq M := m.beqm

-- superstructure, list of lists
mutual
  inductive SM where
  | nil : SM
  | cons : SM → SMM → SM    -- добавляем в конец списка
  deriving BEq

  inductive SMM where
  | atom : M → SMM
  | list : SM → SMM
  deriving BEq
end

open SM SMM

@[simp]
def SM.head : SM → SMM
| .nil => list .nil
| .cons _ x => x

@[simp]
def SM.tail : SM → SM
| .nil => .nil
| .cons x _ => x

-- конкатенация
@[simp]
def SM.conc : SM → SM → SM
| xs, nil => xs
| xs, cons ys y => cons (conc xs ys) y

-- длина списка
@[simp]
def SM.len : SM → Nat
  | .nil         => 0
  | .cons tl _   => len tl + 1

notation:max (priority := high) "‖" x "‖" => len x

scoped syntax "⟪ " term,* " ⟫" : term
macro_rules -- (kind := term)
  | `(⟪⟫) => `(SM.nil)
  | `(⟪ $t ⟫) => `(.cons .nil $t)
  | `(⟪ $t,*, $h ⟫) => `(.cons ⟪$t,*⟫ $h)

-- x - элемент xs
inductive elem : SMM → SMM → Prop where
| here : elem x (list (cons xs x))
| there : elem x (list xs) → elem x (list (cons xs y))

scoped instance : Membership SMM SMM where
  mem := λ x y => elem y x

def SM.isList (x : SMM) : Prop := if x matches .list _ then True else False
def SM.nonNil (x : SM) : Prop := if x matches .nil then False else True

-- начальный сегмент
inductive iniseg  : SM → SM → Prop where
| nn : ∀ {xs}, iniseg xs xs
| n2 : ∀ {xs tl : SM} (hd : SMM), iniseg xs tl → iniseg xs (cons tl hd)

scoped notation:lead x " ⊑ " y => iniseg x y

-- это отношение не фундировано!
-- -- конечные слова
-- inductive FinWord where
-- | empty : FinWord
-- | cons : FinWord → M → FinWord

-- -- суперструктура конечных слов
-- inductive Sfin where

-- notation:arg "Sᶠⁱⁿ" => Sfin
