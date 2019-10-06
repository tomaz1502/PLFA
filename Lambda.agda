module Lambda where

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Data.String using (String; _≟_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Data.List using (List; _∷_; [])

Id : Set
Id = String

infix 5 ƛ_⇒_
infix 5 μ_⇒_
infixl 7 _·_
infix 8 `suc_
infix 9 `_

data Term : Set where
  `_                      :  Id → Term
  ƛ_⇒_                    :  Id → Term → Term
  _·_                     :  Term → Term → Term
  `zero                   :  Term
  `suc_                   :  Term → Term
  case_[zero⇒_|suc_⇒_]    :  Term → Term → Id → Term → Term
  μ_⇒_                    :  Id → Term → Term


two : Term
two = `suc `suc `zero

plus : Term
plus = μ "+" ⇒ ƛ "m" ⇒ ƛ "n" ⇒
  case ` "m"
    [zero⇒ ` "n"
    |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n") ]

twoᶜ : Term
twoᶜ =  ƛ "s" ⇒ ƛ "z" ⇒ ` "s" · (` "s" · ` "z")

plusᶜ : Term
plusᶜ =  ƛ "m" ⇒ ƛ "n" ⇒ ƛ "s" ⇒ ƛ "z" ⇒
  ` "m" · ` "s" · (` "n" · ` "s" · ` "z")

sucᶜ : Term
sucᶜ = ƛ "n" ⇒ `suc (` "n")

mul : Term 
mul = μ "×" ⇒ ƛ "m" ⇒ ƛ "n" ⇒
  case ` "m"
    [zero⇒ `zero
    |suc "m" ⇒ plus · (`"×" · `"m" · `"n") · `"n" ]

mulᶜ : Term
mulᶜ = ƛ "m" ⇒ ƛ "n" ⇒ ƛ "s" ⇒ ƛ "z" ⇒
  `"m" · (`"n" · `"s") · `"z"

mulᶜᶜ : Term
mulᶜᶜ = ƛ "m" ⇒ ƛ "n" ⇒ ƛ "s" ⇒ ƛ "z" ⇒
  `"m" · (plus · `"n") · `"z"

ƛ´_⇒_ : Term → Term → Term
ƛ´ (` x) ⇒ N = ƛ x ⇒ N
ƛ´ _     ⇒ _ = ⊥-elim impossible
  where postulate impossible : ⊥


case´_[zero⇒_|suc_⇒_] : Term → Term → Term → Term → Term
case´ L [zero⇒ M |suc (` x) ⇒ N ]  =  case L [zero⇒ M |suc x ⇒ N ]
case´ _ [zero⇒ _ |suc _ ⇒ _ ]      =  ⊥-elim impossible
  where postulate impossible : ⊥

μ´_⇒_ : Term → Term → Term
μ´ (` x) ⇒ N  =  μ x ⇒ N
μ´ _ ⇒ _      =  ⊥-elim impossible
  where postulate impossible : ⊥



plus´ : Term
plus´ = μ´ + ⇒ ƛ´ m ⇒ ƛ´ n ⇒
  case´ m
    [zero⇒ n
    |suc m ⇒ `suc (+ · m · n)]
  where
  + = `"+"
  m = `"m"
  n = `"n"

mul´ : Term 
mul´ = μ´ × ⇒ ƛ´ m ⇒ ƛ´ n ⇒
  case´ m
    [zero⇒ `zero
    |suc m ⇒ plus · (× · m · n) · n ]
  where
  × = `"×"
  m = `"m"
  n = `"n"

data Value : Term → Set where

  V-ƛ : ∀ {x N} → Value (ƛ x ⇒ N)

  V-zero : Value `zero

  V-suc : ∀ {V} → Value V -> Value (`suc V)


infix 9 _[_:=_]

_[_:=_] : Term → Id → Term → Term
(` x) [ y := V ] with x ≟ y
... | yes _ = V
... | no  _ = (` x)
(ƛ x ⇒ N) [ y := V ] with x ≟ y
... | yes _ = ƛ x ⇒ N
... | no  _ = ƛ x ⇒ N [ y := V ]
(N · M) [ y := V ] = N [ y := V ] · M [ y := V ]
`zero [ y := V ] = `zero
(`suc N) [ y := V ] = `suc N [ y := V ]
case N [zero⇒ M |suc x ⇒ L ] [ y := V ] with x ≟ y
... | yes _ = case N [ y := V ] [zero⇒ M [ y := V ] |suc x ⇒ L ]
... | no  _ = case N [ y := V ] [zero⇒ M [ y := V ] |suc x ⇒ L [ y := V ] ]
(μ x ⇒ N) [ y := V ] with x ≟ y
... | yes _ = μ x ⇒ N
... | no  _ = μ x ⇒ N [ y := V ]

_ : (ƛ "z" ⇒ ` "s" · (` "s" · ` "z")) [ "s" := sucᶜ ] ≡ ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")
_ = refl

_ : (sucᶜ · (sucᶜ · ` "z")) [ "z" := `zero ] ≡ sucᶜ · (sucᶜ · `zero)
_ = refl

_ : (ƛ "x" ⇒ ` "y") [ "y" := `zero ] ≡ ƛ "x" ⇒ `zero
_ = refl

_ : (ƛ "x" ⇒ ` "x") [ "x" := `zero ] ≡ ƛ "x" ⇒ ` "x"
_ = refl

_ : (ƛ "y" ⇒ ` "y") [ "x" := `zero ] ≡ ƛ "y" ⇒ ` "y"
_ = refl

-- Answer to Quiz 1 : (3)


_[_::=_] : Term → Id → Term → Term
subsDec : Term → Id → Term → Term

(` x) [ y ::= V ] with x ≟ y
... | yes _ = V
... | no  _ = (` x)
(ƛ x ⇒ N) [ y ::= V ] = subsDec (ƛ x ⇒ N) y V
(N · M) [ y ::= V ] = N [ y ::= V ] · M [ y ::= V ]
`zero [ y ::= V ] = `zero
(`suc N) [ y ::= V ] = `suc N [ y ::= V ]
case N [zero⇒ M |suc x ⇒ L ] [ y ::= V ] = subsDec (case N [zero⇒ M |suc x ⇒ L ]) y V
(μ x ⇒ N) [ y ::= V ] = subsDec (μ x ⇒ N) y V

subsDec (ƛ x ⇒ T) y V with x ≟ y
... | yes _ = ƛ x ⇒ T
... | no  _ = ƛ x ⇒ T [ y ::= V ]
subsDec case T [zero⇒ T₁ |suc x ⇒ T₂ ] y V with x ≟ y
... | yes _ = case T [zero⇒ T₁ |suc x ⇒ T₂ ]
... | no  _ = case T [zero⇒ T₁ |suc x ⇒ T₂ [ y ::= V ] ]
subsDec (μ x ⇒ T) y V with x ≟ y
... | yes _ = μ x ⇒ T
... | no  _ = μ x ⇒ T [ y ::= V ]
subsDec _            y V = ⊥-elim impossible
  where postulate impossible : ⊥


_ : (ƛ "z" ⇒ ` "s" · (` "s" · ` "z")) [ "s" ::= sucᶜ ] ≡ ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")
_ = refl

_ : (sucᶜ · (sucᶜ · ` "z")) [ "z" ::= `zero ] ≡ sucᶜ · (sucᶜ · `zero)
_ = refl

_ : (ƛ "x" ⇒ ` "y") [ "y" ::= `zero ] ≡ ƛ "x" ⇒ `zero
_ = refl

_ : (ƛ "x" ⇒ ` "x") [ "x" ::= `zero ] ≡ ƛ "x" ⇒ ` "x"
_ = refl

_ : (ƛ "y" ⇒ ` "y") [ "x" ::= `zero ] ≡ ƛ "y" ⇒ ` "y"
_ = refl

infix 4 _—→_

data _—→_ : Term → Term → Set where

  ξ—·₁   : ∀ {L L´ M}     → L —→ L´ → L · M —→ L´ · M
  ξ—·₂   : ∀ {V M M´}     → Value V → M —→ M´ → V · M —→ V · M´
  β—ƛ    : ∀ {x L V}      → Value V → (ƛ x ⇒ L) · V —→ L [ x := V ]
  ξ—suc  : ∀ {M M´}       → `suc M —→ `suc M´
  ξ-case : ∀ {x L L′ M N} → L —→ L′ → case L [zero⇒ M |suc x ⇒ N ] —→ case L′ [zero⇒ M |suc x ⇒ N ]
  β—zero : ∀ {x M N}      → case `zero [zero⇒ M |suc x ⇒ N ] —→ M
  β—suc  : ∀ {x V M N}    → Value V → case `suc V [zero⇒ M |suc x ⇒ N ] —→ N [ x := V ]
  β—μ    : ∀ {x M}        → μ x ⇒ M —→ M [ x := μ x ⇒ M ]
