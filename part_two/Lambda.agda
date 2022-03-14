{-# OPTIONS --allow-unsolved-metas #-}

module plfa.part_two.Lambda where

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong)
open import Data.String using (String; _≟_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Data.List using (List; _∷_; [])
open import Data.Product using (_×_; proj₁; proj₂; ∃; ∃-syntax)
                                renaming (_,_ to ⟨_,_⟩)
open import plfa.part_one.Isomorphism

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

one : Term
one = `suc `zero

two : Term
two = `suc `suc `zero

plus : Term
plus = μ "+" ⇒ ƛ "m" ⇒ ƛ "n" ⇒
  case ` "m"
    [zero⇒ ` "n"
    |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n") ]

oneᶜ : Term
oneᶜ = ƛ "s" ⇒ ƛ "z" ⇒ ` "s" · ` "z"

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

  ξ-·₁   : ∀ {L L´ M}
    → L —→ L´
    ---------------------
    → L · M —→ L´ · M

  ξ-·₂   : ∀ {V M M´}
    → Value V
    → M —→ M´
    ---------------------
    → V · M —→ V · M´

  β-ƛ    : ∀ {x L V}
    → Value V
    ---------------------
    → (ƛ x ⇒ L) · V —→ L [ x := V ]

  ξ-suc  : ∀ {M M´}
    → M —→ M´
    ---------------------
    → `suc M —→ `suc M´

  ξ-case : ∀ {x L L′ M N}
    → L —→ L′
    -----------------------------------------------------------------
    → case L [zero⇒ M |suc x ⇒ N ] —→ case L′ [zero⇒ M |suc x ⇒ N ]

  β-zero : ∀ {x M N}
    -----------------------------------------------------------------
    → case `zero [zero⇒ M |suc x ⇒ N ] —→ M

  β-suc  : ∀ {x V M N}
    → Value V
    -----------------------------------------------------------------
    → case `suc V [zero⇒ M |suc x ⇒ N ] —→ N [ x := V ]

  β-μ    : ∀ {x M}
    -----------------------------------------------------------------
    → μ x ⇒ M —→ M [ x := μ x ⇒ M ]


QuizUm : (ƛ "x" ⇒ ` "x") · (ƛ "x" ⇒ ` "x")  —→ (ƛ "x" ⇒ ` "x")
QuizUm = β-ƛ V-ƛ

QuizDois : (ƛ "x" ⇒ ` "x") · (ƛ "x" ⇒ ` "x") · (ƛ "x" ⇒ ` "x") —→ (ƛ "x" ⇒ ` "x") · (ƛ "x" ⇒ ` "x")
QuizDois = ξ-·₁ QuizUm

QuizTres : twoᶜ · sucᶜ · `zero  —→  (ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")) · `zero
QuizTres = ξ-·₁ (β-ƛ V-ƛ)


infix 2  _—↠_
infix 1  begin_
infixr 2 _—→⟨_⟩_
infix 3  _∎

data _—↠_ : Term → Term → Set where

  _∎ : ∀ M
    ----------
    → M —↠ M

  _—→⟨_⟩_ : ∀ L {M N}
    → L —→ M
    → M —↠ N
    -------------
    → L —↠ N

begin_ : ∀ {M N} → M —↠ N → M —↠ N
begin M—↠N = M—↠N

↠-trans : ∀ {L M N} → L —↠ M → M —↠ N → L —↠ N
↠-trans (_ ∎) L—↠N = L—↠N
↠-trans (_ —→⟨ L—→M ⟩ M—↠M₁) M₁—↠N = _ —→⟨ L—→M ⟩ ↠-trans M—↠M₁ M₁—↠N

data _—↠´_ : Term → Term → Set where

  step´ : ∀ {M N}
    → M —→ N
    -------------
    → M —↠´ N

  refl´ : ∀ {M}
    -------------
    → M —↠´ M

  trans´ : ∀ {L M N}
    → L —↠´ M
    → M —↠´ N
    -------------
    → L —↠´ N

to∘emb—↠ : ∀ {M N} → M —↠ N → M —↠´ N
to∘emb—↠ (M ∎) = _—↠´_.refl´
to∘emb—↠ {M} {N} (L —→⟨ L—→M ⟩ M—↠N) = trans´ (step´ L—→M) (to∘emb—↠ M—↠N)

from∘emb—↠ : ∀ {M N} → M —↠´ N → M —↠ N
from∘emb—↠ {M} {N} (step´ M—→N)             = M —→⟨ M—→N ⟩ N ∎
from∘emb—↠ {M} refl´                        = M ∎
from∘emb—↠ (trans´ {L} {M} {N} L—↠´M M—↠´N) = ↠-trans (from∘emb—↠ L—↠´M) (from∘emb—↠ M—↠´N)

from∘to—↠ : ∀ {M N} (p : M —↠ N) → from∘emb—↠ (to∘emb—↠ p) ≡ p
from∘to—↠ {M} {.M} (.M ∎) = refl
from∘to—↠ {M} {N} (.M —→⟨ x ⟩ p) = cong (λ z → M —→⟨ x ⟩ z) (from∘to—↠ p)

emb—↠ : ∀ {M N} → M —↠ N ≲ M —↠´ N
emb—↠ =
  record
  { to      = to∘emb—↠
  ; from    = from∘emb—↠
  ; from∘to = from∘to—↠
  }

_ : twoᶜ · sucᶜ · `zero —↠ `suc `suc `zero
_ =
  begin
    twoᶜ · sucᶜ · `zero
    —→⟨ ξ-·₁ (β-ƛ V-ƛ) ⟩
    (ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")) · `zero
    —→⟨ β-ƛ V-zero ⟩
    sucᶜ · (sucᶜ · `zero)
    —→⟨ ξ-·₂ V-ƛ (β-ƛ V-zero) ⟩
    sucᶜ · `suc `zero
    —→⟨ β-ƛ (V-suc V-zero) ⟩
    `suc (`suc `zero)
    ∎

_ : (ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")) · (twoᶜ · sucᶜ · `zero) —↠ `suc (`suc (`suc (`suc `zero)))
_ = (ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")) · (twoᶜ · sucᶜ · `zero)
  —→⟨ ξ-·₂ V-ƛ (ξ-·₁ (β-ƛ V-ƛ)) ⟩
    (ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")) · ((ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")) · `zero)
  —→⟨ ξ-·₂ V-ƛ (β-ƛ V-zero) ⟩
    (ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")) · (sucᶜ · (sucᶜ · `zero))
  —→⟨ ξ-·₂ V-ƛ (ξ-·₂ V-ƛ (β-ƛ V-zero)) ⟩
    (ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")) · (sucᶜ · (`suc `zero))
  —→⟨ ξ-·₂ V-ƛ (β-ƛ (V-suc V-zero)) ⟩
    (ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")) · (`suc `suc `zero)
  —→⟨ β-ƛ (V-suc (V-suc V-zero)) ⟩
    sucᶜ · (sucᶜ · `suc `suc `zero)
  —→⟨ ξ-·₂ V-ƛ (β-ƛ (V-suc (V-suc V-zero))) ⟩
    sucᶜ · (`suc `suc `suc `zero)
  —→⟨ β-ƛ (V-suc (V-suc (V-suc V-zero))) ⟩
   `suc (`suc (`suc (`suc `zero)))
  ∎

_ : plusᶜ · oneᶜ · oneᶜ · sucᶜ · `zero —↠ `suc `suc `zero
_ = begin
      (ƛ "m" ⇒ ƛ "n" ⇒ ƛ "s" ⇒ ƛ "z" ⇒ ` "m" · ` "s" · (` "n" · ` "s" · ` "z")) · oneᶜ · oneᶜ · sucᶜ · `zero
        —→⟨ ξ-·₁ (ξ-·₁ (ξ-·₁ (β-ƛ V-ƛ))) ⟩
      (ƛ "n" ⇒ ƛ "s" ⇒ ƛ "z" ⇒  oneᶜ · ` "s" · (`"n" · `"s" · ` "z")) · oneᶜ · sucᶜ · `zero
        —→⟨ ξ-·₁ (ξ-·₁ (β-ƛ V-ƛ)) ⟩
      (ƛ "s" ⇒ ƛ "z" ⇒ oneᶜ · ` "s" · (oneᶜ · ` "s" · ` "z")) · sucᶜ · `zero
        —→⟨ ξ-·₁ (β-ƛ V-ƛ) ⟩
      (ƛ "z" ⇒ oneᶜ · sucᶜ · (oneᶜ · sucᶜ · `"z") ) · `zero
        —→⟨ β-ƛ V-zero ⟩
      oneᶜ · sucᶜ · (oneᶜ · sucᶜ · `zero)
        —→⟨ ξ-·₁ (β-ƛ V-ƛ) ⟩
      (ƛ "z" ⇒ sucᶜ · (`"z")) · (oneᶜ · sucᶜ · `zero)
        —→⟨ ξ-·₂ V-ƛ (ξ-·₁ (β-ƛ V-ƛ)) ⟩
      (ƛ "z" ⇒ sucᶜ · ` "z") · ((ƛ "z" ⇒ sucᶜ · (` "z")) · `zero)
        —→⟨ ξ-·₂ V-ƛ ((β-ƛ V-zero)) ⟩
      (ƛ "z" ⇒ sucᶜ · ` "z") · (sucᶜ · `zero)
        —→⟨ ξ-·₂ V-ƛ (β-ƛ V-zero) ⟩
      (ƛ "z" ⇒ sucᶜ · ` "z") · (`suc `zero)
        —→⟨ β-ƛ (V-suc V-zero) ⟩
      sucᶜ · (`suc `zero)
        —→⟨ β-ƛ (V-suc V-zero) ⟩
      `suc (`suc `zero) ∎


infixr 7 _⇒_

data Type : Set where
 _⇒_ : Type → Type → Type
 `ℕ  : Type

-- Quiz (Typing) : 5, 6

infixl 5 _,_∶_

data Context : Set where
  ∅     : Context
  _,_∶_ : Context → Id → Type → Context

to₁ : Context → List (Id × Type)
to₁ ∅ = []
to₁ (C , x ∶ T) = ⟨ x ,  T ⟩ ∷ (to₁ C)

from₁ : List (Id × Type) → Context
from₁ [] = ∅
from₁ (⟨ x , T ⟩ ∷ L) = (from₁ L) , x ∶ T

to∘from₁ : ∀ (L : List (Id × Type)) → to₁ (from₁ L) ≡ L
to∘from₁ []              = refl
to∘from₁ (⟨ x , T ⟩ ∷ L) = cong (⟨ x , T ⟩ ∷_) (to∘from₁ L)

from∘to₁ : ∀ (C : Context) → from₁ (to₁ C) ≡ C
from∘to₁ ∅            = refl
from∘to₁ (C , x ∶ T) = cong (_, x ∶ T) (from∘to₁ C)

_ : Context ≃ List (Id × Type)
_ = record
     { to      = to₁
     ; from    = from₁
     ; to∘from = to∘from₁
     ; from∘to = from∘to₁
     }

infix 4 _∋_∶_

data _∋_∶_ : Context → Id → Type → Set where

  Z : ∀ {Γ x T}
    → Γ , x ∶ T ∋ x ∶ T

  S : ∀ {Γ x y T S}
    → x ≢ y
    → Γ ∋ x ∶ T
    ----------------------
    → Γ , y ∶ S ∋ x ∶ T

infix 4 _⊢_∶_

data _⊢_∶_ : Context → Term → Type → Set where

  ⊢´ : ∀ {Γ x T}
    → Γ ∋ x ∶ T
    -------------
    → Γ ⊢ ` x ∶ T

  ⊢ƛ : ∀ {Γ x N T U}
    → Γ , x ∶ T ⊢ N ∶ U
    -------------------------
    → Γ ⊢ ƛ x ⇒ N ∶ T ⇒ U

  _·_ : ∀ {Γ N M T U}
    → Γ ⊢ M ∶ T ⇒ U
    → Γ ⊢ N ∶ T
    ------------------
    → Γ ⊢ M · N ∶ U

  ⊢zero : ∀ {Γ}
    → Γ ⊢ `zero ∶ `ℕ

  ⊢suc : ∀ {Γ M}
    → Γ ⊢ M ∶ `ℕ
    -----------------------
    → Γ ⊢ `suc M ∶ `ℕ

  ⊢case : ∀ {Γ L M N U x}
    → Γ ⊢ L ∶ `ℕ
    → Γ ⊢ M ∶ U
    → Γ , x ∶ `ℕ ⊢ N ∶ U
    ---------------------------------------
    → Γ ⊢ case L [zero⇒ M |suc x ⇒ N ] ∶ U

  ⊢μ : ∀ {Γ M x T}
    → Γ , x ∶ T ⊢ M ∶ T
    --------------------
    → Γ ⊢ μ x ⇒ M ∶ T

Ch : Type → Type
Ch T = (T ⇒ T) ⇒ T ⇒ T

⊢twoᶜ : ∀ {Γ T} → Γ ⊢ twoᶜ ∶ Ch T
⊢twoᶜ {Γ} {T} = ⊢ƛ (⊢ƛ (_·_ (⊢´ (S (λ()) Z)) (_·_ (⊢´ (S (λ()) Z)) (⊢´ Z))))


-- ⊢twoᶜ : ∀ {Γ A} → Γ ⊢ twoᶜ ∶ Ch A
-- ⊢twoᶜ = ⊢ƛ (⊢ƛ (⊢´ ∋s · (⊢´ ∋s · ⊢´ ∋z)))
--   where
--     ∋s = S (λ()) Z
--     ∋z = Z


⊢two : ∀ {Γ} → Γ ⊢ two ∶ `ℕ
⊢two = ⊢suc (⊢suc ⊢zero)

⊢plus : ∀ {Γ} → Γ ⊢ plus ∶ `ℕ ⇒ `ℕ ⇒ `ℕ
⊢plus = ⊢μ (⊢ƛ (⊢ƛ (⊢case (⊢´ ∋m) (⊢´ ∋n)
         (⊢suc (⊢´ ∋+ · ⊢´ ∋m′ · ⊢´ ∋n′)))))
  where
  ∋+  = (S (λ()) (S (λ()) (S (λ()) Z)))
  ∋m  = (S (λ()) Z)
  ∋n  = Z
  ∋m′ = Z
  ∋n′ = (S (λ()) Z)

⊢2+2 : ∅ ⊢ plus · two · two ∶ `ℕ
⊢2+2 = ⊢plus · ⊢two · ⊢two

⊢plusᶜ : ∀ {Γ A} → Γ  ⊢ plusᶜ ∶ Ch A ⇒ Ch A ⇒ Ch A
⊢plusᶜ = ⊢ƛ (⊢ƛ (⊢ƛ (⊢ƛ (⊢´ ∋m · ⊢´ ∋s · (⊢´ ∋n · ⊢´ ∋s · ⊢´ ∋z)))))
  where
    ∋m = S (λ()) (S (λ()) (S (λ()) Z))
    ∋n = S (λ()) (S (λ()) Z)
    ∋s = S (λ()) Z
    ∋z = Z

⊢sucᶜ : ∀ {Γ} → Γ ⊢ sucᶜ ∶ `ℕ ⇒ `ℕ
⊢sucᶜ = ⊢ƛ (⊢suc (⊢´ ∋n))
  where
    ∋n = Z

⊢2+2ᶜ : ∅ ⊢ plusᶜ · twoᶜ · twoᶜ · sucᶜ · `zero ∶ `ℕ
⊢2+2ᶜ = ⊢plusᶜ · ⊢twoᶜ · ⊢twoᶜ · ⊢sucᶜ · ⊢zero

∋—injective : ∀ {Γ x T U} → Γ ∋ x ∶ T → Γ ∋ x ∶ U → T ≡ U
∋—injective  Z           Z         = refl
∋—injective  Z          (S x≢x _)  = ⊥-elim (x≢x refl)
∋—injective (S x≢x _)    Z         = ⊥-elim (x≢x refl)
∋—injective (S _ Wit₁)  (S _ Wit₂) = ∋—injective Wit₁ Wit₂


nope₁ : ∀ {T} → ¬ (∅ ⊢ `zero · (`suc `zero) ∶ T)
nope₁ (() · _)

nope₂ : ∀ {T} → ¬ (∅ ⊢ ƛ "x" ⇒ `"x" · `"x" ∶ T)
nope₂ (⊢ƛ (⊢´ x∶T⇒U · ⊢´ x∶T)) = ⊥-elim (contra (∋—injective x∶T⇒U x∶T))
  where
    contra : ∀ {A B} → ¬ (A ⇒ B ≡ A)
    contra ()

{-
  Quiz :
  1 - ∅ , "y" ⦂ `ℕ ⇒ `ℕ , "x" ⦂ `ℕ ⊢ ` "y" · ` "x" ⦂ A → A ≡ `ℕ
  2 - ∅ , "y" ⦂ `ℕ ⇒ `ℕ , "x" ⦂ `ℕ ⊢ ` "x" · ` "y" ⦂ A → impossible (x should have functional type)
  3 - ∅ , "y" ⦂ `ℕ ⇒ `ℕ ⊢ ƛ "x" ⇒ ` "y" · ` "x" ⦂ A   → A ≡ `ℕ ⇒ `ℕ

  1 - ∅ , "x" ⦂ A ⊢ ` "x" · ` "x" ⦂ B → impossible (see nope₂)
  2 - ∅ , "x" ⦂ A , "y" ⦂ B ⊢ ƛ "z" ⇒ ` "x" · (` "y" · ` "z") ⦂ C → B ≡ T ⇒ U , A ≡ U ⇒ V , C ≡ T ⇒ V
-}

{-

mul : Term 
mul = μ "×" ⇒ ƛ "m" ⇒ ƛ "n" ⇒
  case ` "m"
    [zero⇒ `zero
    |suc "m" ⇒ plus · (`"×" · `"m" · `"n") · `"n" ]

-}

{- TO FIX
mulWT : ∅ ⊢ mul ∶ `ℕ ⇒ `ℕ ⇒ `ℕ
mulWT = ⊢μ (⊢ƛ (⊢ƛ (⊢case (⊢´ (S (λ()) Z)) ⊢zero (⊢plus · (⊢´ (S (λ())) (S (λ()) (S (λ()) Z))) · ⊢´ Z · ⊢´ (S (λ()) Z)) · ⊢´ (S (λ()) Z))))
-}

{-
mulᶜ : Term
mulᶜ = ƛ "m" ⇒ ƛ "n" ⇒ ƛ "s" ⇒ ƛ "z" ⇒
       `"m" · (`"n" · `"s") · `"z"
-}


mulᶜWT : ∀ {T₁ T₂ T₃ T₄} → ∅ ⊢ mulᶜ ∶ (T₁ ⇒ T₂ ⇒ T₃) ⇒ (T₄ ⇒ T₁) ⇒ T₄ ⇒ T₂ ⇒ T₃
mulᶜWT = ⊢ƛ (⊢ƛ (⊢ƛ (⊢ƛ (⊢´ (S (λ()) (S (λ()) (S (λ()) Z))) · (⊢´ (S (λ()) (S (λ()) Z)) · ⊢´ (S (λ()) Z)) · ⊢´ Z))))



-- n-th : {A : Id} {B : Type} (C : Context) → ℕ → C ∋ A ∶ B → A ∶ B
-- n-th ∅ zero = {!!}
-- n-th {x} {x₁} (C , x ∶ x₁) zero = {!Z!}
-- n-th C (suc n) = {!!}

