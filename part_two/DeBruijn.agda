module plfa.part_two.DeBruijn where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Nullary using (¬_)

infix 4 _⊢_
infix 4 _∋_
infixl 5 _,_

infixr 7 _⇒_

infix 5 ƛ_
infix 5 μ_
infixl 7 _·_
infix 8 `suc_
infix 9 `_
infix 9 S_
infix 9 #_

data Type : Set where
  _⇒_ : Type → Type → Type
  `ℕ  : Type

data Context : Set where
  ∅ : Context
  _,_ : Context → Type → Context

_ : Context
_ = ∅ , `ℕ ⇒ `ℕ , `ℕ

data _∋_ : Context → Type → Set where

  Z : ∀ {Γ A}
    --------------
    → Γ , A ∋ A

  S_ : ∀ {Γ A B}
    → Γ ∋ A
    --------------
    → Γ , B ∋ A

data _⊢_ : Context → Type → Set where

  `_ : ∀ {Γ A}
    → Γ ∋ A
    ---------
    → Γ ⊢ A

  ƛ_ : ∀ {Γ A B}
    → Γ , A ⊢ B
    --------------
    → Γ ⊢ A ⇒ B

  _·_ : ∀ {Γ A B}
    → Γ ⊢ A ⇒ B
    → Γ ⊢ A
    --------------
    → Γ ⊢ B

  `zero : ∀ {Γ}
    -----------
    → Γ ⊢ `ℕ

  `suc_ : ∀ {Γ}
    → Γ ⊢ `ℕ
    -----------
    → Γ ⊢ `ℕ

  case : ∀ {Γ A}
    → Γ ⊢ `ℕ
    → Γ ⊢ A
    → Γ , `ℕ ⊢ A
    --------------
    → Γ ⊢ A

  μ_ : ∀ {Γ A}
    → Γ , A ⊢ A
    --------------
    → Γ ⊢ A

  `let : ∀ {Γ A B}
    → Γ ⊢ A
    → Γ , A ⊢ B
    -----------
    → Γ ⊢ B

lookup : Context → ℕ → Type
lookup (Γ , A) zero = A
lookup (Γ , _) (suc n) = lookup Γ n
lookup ∅ _ = ⊥-elim impossible
  where postulate impossible : ⊥

count : ∀ {Γ} → (n : ℕ) → Γ ∋ lookup Γ n
count {Γ , _} zero    = Z
count {Γ , _} (suc n) = S (count n)
count {∅}     _       = ⊥-elim impossible
  where postulate impossible : ⊥


#_ : ∀ {Γ} → (n : ℕ) → Γ ⊢ lookup Γ n
# n = ` count n


twoᶜ : ∅ ⊢ (`ℕ ⇒ `ℕ) ⇒ `ℕ ⇒ `ℕ
twoᶜ = ƛ ƛ (# 1 · (# 1 · # 0))

two : ∀ {Γ} → Γ ⊢ `ℕ
two = `suc `suc `zero

plus : ∀ {Γ} → Γ ⊢ `ℕ ⇒ `ℕ ⇒ `ℕ
plus = μ ƛ ƛ (case (# 1) (# 0) (`suc (# 3 · # 0 · # 1)))

2+2 : ∀ {Γ} → Γ ⊢ `ℕ
2+2 = plus · two · two

mul : ∀ {Γ} → Γ ⊢ `ℕ ⇒ `ℕ ⇒ `ℕ
mul = μ ƛ ƛ (case (# 1) (`zero) (plus · (# 3 · # 0 · # 1) · # 1) )

ext : ∀ {Γ Δ}
  → (∀ {A}   → Γ ∋ A     → Δ ∋ A)
  ---------------------------
  → (∀ {A B} → Γ , B ∋ A → Δ , B ∋ A)
ext p Z = Z
ext p (S x) = S (p x)

rename : ∀ {Γ Δ}
  → (∀ {A} → Γ ∋ A → Δ ∋ A)
  ---------------------------
  → (∀ {A} → Γ ⊢ A → Δ ⊢ A)

rename p (` x)             = ` p x
rename p (ƛ ⊢A)            = ƛ rename (ext p) ⊢A
rename p (⊢A · ⊢A₁)        = rename p ⊢A · rename p ⊢A₁
rename p `zero             = `zero
rename p (`suc ⊢A)         = `suc rename p ⊢A
rename p (case ⊢A ⊢A₁ ⊢A₂) = case (rename p ⊢A) (rename p ⊢A₁) (rename (ext p) ⊢A₂)
rename p (μ ⊢A)            = μ rename (ext p) ⊢A
rename ρ (`let M N)     =  `let (rename ρ M) (rename (ext ρ) N)

M₀ : ∅ , `ℕ ⇒ `ℕ ⊢ `ℕ ⇒ `ℕ
M₀ = ƛ (# 1 · (# 1 · # 0))

M₁ : ∅ , `ℕ ⇒ `ℕ , `ℕ ⊢ `ℕ ⇒ `ℕ
M₁ = ƛ (# 2 · (# 2 · # 0))

_ : rename S_ M₀ ≡ M₁
_ = refl


exts : ∀ {Γ Δ}
  → (∀ {A} → Γ ∋ A → Δ ⊢ A)
  ---------------------------
  → (∀ {A B} → Γ , B ∋ A → Δ , B ⊢ A)

exts σ Z     = ` Z
exts σ (S x) = rename S_ (σ x)

subst : ∀ {Γ Δ}
  → (∀ {A} → Γ ∋ A → Δ ⊢ A)
  ---------------------------
  → (∀ {A} → Γ ⊢ A → Δ ⊢ A)

subst σ (` x) = σ x
subst σ (ƛ ⊢A) = ƛ subst (exts σ) ⊢A
subst σ (⊢A · ⊢A₁) = subst σ ⊢A · subst σ ⊢A₁
subst σ `zero = `zero
subst σ (`suc ⊢A) = `suc subst σ ⊢A
subst σ (case ⊢A ⊢A₁ ⊢A₂) = case (subst σ ⊢A) (subst σ ⊢A₁) (subst (exts σ) ⊢A₂)
subst σ (μ ⊢A) = μ (subst (exts σ) ⊢A)
subst σ (`let M N)     =  `let (subst σ M) (subst (exts σ) N)

_[_] : ∀ {Γ A B}
  → Γ , B ⊢ A
  → Γ ⊢ B
  --------------
  → Γ ⊢ A

_[_] {Γ} {A} {B} N M = subst {Γ , B} {Γ} σ {A} N
  where
    σ : ∀ {A} → Γ , B ∋ A → Γ ⊢ A
    σ Z     = M
    σ (S x) = ` x

M₂ : ∅ , `ℕ ⇒ `ℕ ⊢ `ℕ ⇒ `ℕ
M₂ = ƛ # 1 · (# 1 · # 0)

M₃ : ∅ ⊢ `ℕ ⇒ `ℕ
M₃ = ƛ `suc # 0

M₄ : ∅ ⊢ `ℕ ⇒ `ℕ
M₄ = ƛ (ƛ `suc # 0) · ((ƛ `suc # 0) · # 0)

_ : M₂ [ M₃ ] ≡ M₄
_ = refl

M₅ : ∅ , `ℕ ⇒ `ℕ , `ℕ ⊢ (`ℕ ⇒ `ℕ) ⇒ `ℕ
M₅ = ƛ # 0 · # 1

M₆ : ∅ , `ℕ ⇒ `ℕ ⊢ `ℕ
M₆ = # 0 · `zero

M₇ : ∅ , `ℕ ⇒ `ℕ ⊢ (`ℕ ⇒ `ℕ) ⇒ `ℕ
M₇ = ƛ (# 0 · (# 1 · `zero))

_ : M₅ [ M₆ ] ≡ M₇
_ = refl

data Value : ∀ {Γ A} → Γ ⊢ A → Set where

  V-ƛ : ∀ {Γ A B} {N : Γ , A ⊢ B}
    ---------------------------
    → Value (ƛ N)

  V-zero : ∀ {Γ}
    -----------------
    → Value (`zero {Γ})

  V-suc : ∀ {Γ} {V : Γ ⊢ `ℕ}
    → Value V
    --------------
    → Value (`suc V)

infix 2 _—→_

data _—→_ : ∀ {Γ A} → (Γ ⊢ A) → (Γ ⊢ A) → Set where

  ξ-·₁ : ∀ {Γ A B} {L L′ : Γ ⊢ A ⇒ B} {M : Γ ⊢ A}
    → L —→ L′
    ---------------
    → L · M —→ L′ · M

  ξ-·₂ : ∀ {Γ A B} {V : Γ ⊢ A ⇒ B} {M M′ : Γ ⊢ A}
    → Value V
    → M —→ M′
    ---------------
    → V · M —→ V · M′

  β-ƛ : ∀ {Γ A B} {N : Γ , A ⊢ B} {W : Γ ⊢ A}
    → Value W
    --------------------
    → (ƛ N) · W —→ N [ W ]

  ξ-suc : ∀ {Γ} {M M′ : Γ ⊢ `ℕ}
    → M —→ M′
    -----------------
    → `suc M —→ `suc M′

  ξ-case : ∀ {Γ A} {L L′ : Γ ⊢ `ℕ} {M : Γ ⊢ A} {N : Γ , `ℕ ⊢ A}
    → L —→ L′
    -------------------------
    → case L M N —→ case L′ M N

  β-zero :  ∀ {Γ A} {M : Γ ⊢ A} {N : Γ , `ℕ ⊢ A}
    -------------------
    → case `zero M N —→ M

  β-suc : ∀ {Γ A} {V : Γ ⊢ `ℕ} {M : Γ ⊢ A} {N : Γ , `ℕ ⊢ A}
    → Value V
    ----------------------------
    → case (`suc V) M N —→ N [ V ]

  β-μ : ∀ {Γ A} {N : Γ , A ⊢ A}
    ----------------
    → μ N —→ N [ μ N ]


  ξ-let : ∀ {Γ A B} {M M′ : Γ ⊢ A} {N : Γ , A ⊢ B}
    → M —→ M′
    ---------------------
    → `let M N —→ `let M′ N

  β-let : ∀ {Γ A B} {V : Γ ⊢ A} {N : Γ , A ⊢ B}
    → Value V
    -------------------
    → `let V N —→ N [ V ]



infix  2 _—↠_
infix  1 begin_
infixr 2 _—→⟨_⟩_
infix  3 _∎

data _—↠_ : ∀ {Γ A} → (Γ ⊢ A) → (Γ ⊢ A) → Set where

  _∎ : ∀ {Γ A} (M : Γ ⊢ A)
    ------
    → M —↠ M

  _—→⟨_⟩_ : ∀ {Γ A} (L : Γ ⊢ A) {M N : Γ ⊢ A}
    → L —→ M
    → M —↠ N
    ------
    → L —↠ N

begin_ : ∀ {Γ A} {M N : Γ ⊢ A}
  → M —↠ N
  ------
  → M —↠ N
begin M—↠N = M—↠N

V¬—→ : ∀ {Γ A} {M N : Γ ⊢ A} → Value M → ¬ (M —→ N)
V¬—→ V-ƛ ()
V¬—→ V-zero ()
V¬—→ (V-suc VM) (ξ-suc M—→) = V¬—→ VM M—→

—→¬V : ∀ {Γ A} {M N : Γ ⊢ A} → M —→ N → ¬ Value M
—→¬V M—→ VM = V¬—→ VM M—→

data Progress {A} (M : ∅ ⊢ A) : Set where

  step : ∀ {N : ∅ ⊢ A}
    → M —→ N
    ----------
    → Progress M

  done :
    Value M
    ----------
    → Progress M
{-
progress : ∀ {A} → (M : ∅ ⊢ A) → Progress M
progress (` ())
progress (ƛ N)                          =  done V-ƛ
progress (L · M) with progress L
...    | step L—→L′                     =  step (ξ-·₁ L—→L′)
...    | done V-ƛ with progress M
...        | step M—→M′                 =  step (ξ-·₂ V-ƛ M—→M′)
...        | done VM                    =  step (β-ƛ VM)
progress (`zero)                        =  done V-zero
progress (`suc M) with progress M
...    | step M—→M′                     =  step (ξ-suc M—→M′)
...    | done VM                        =  done (V-suc VM)
progress (case L M N) with progress L
...    | step L—→L′                     =  step (ξ-case L—→L′)
...    | done V-zero                    =  step (β-zero)
...    | done (V-suc VL)                =  step (β-suc VL)
progress (μ N)                          =  step (β-μ)
-}

data Gas : Set where
  gas : ℕ → Gas

data Finished {Γ A} (N : Γ ⊢ A) : Set where

  done :
    Value N
    ----------
    → Finished N

  out-of-gas :
    ----------
    Finished N


data Steps : ∀ {A} → ∅ ⊢ A → Set where

  steps : ∀ {A} {L N : ∅ ⊢ A}
    → L —↠ N
    → Finished N
    ----------
    → Steps L
{-
eval : ∀ {A}
  → Gas
  → (L : ∅ ⊢ A)
  -----------
  → Steps L
eval (gas zero)    L                     =  steps (L ∎) out-of-gas
eval (gas (suc m)) L with progress L
... | done VL                            =  steps (L ∎) (done VL)
... | step {M} L—→M with eval (gas m) M
...    | steps M—↠N fin                  =  steps (L —→⟨ L—→M ⟩ M—↠N) fin

mulex : ∀ {Γ} → Γ ⊢ `ℕ
mulex = mul · two · two



infix  4 _~_
infix  5 ~ƛ_
infix  7 _~·_

data _~_ : ∀ {Γ A} → (Γ ⊢ A) → (Γ ⊢ A) → Set where

  ~` : ∀ {Γ A} {x : Γ ∋ A}
    ---------
    → ` x ~ ` x

  ~ƛ_ : ∀ {Γ A B} {N N† : Γ , A ⊢ B}
    → N ~ N†
    ----------
    → ƛ N ~ ƛ N†

  _~·_ : ∀ {Γ A B} {L L† : Γ ⊢ A ⇒ B} {M M† : Γ ⊢ A}
    → L ~ L†
    → M ~ M†
    ---------------
    → L · M ~ L† · M†

  ~let : ∀ {Γ A B} {M M† : Γ ⊢ A} {N N† : Γ , A ⊢ B}
    → M ~ M†
    → N ~ N†
    ----------------------
    → `let M N ~ (ƛ N†) · M†

_† : ∀ {Γ A} → Γ ⊢ A → Γ ⊢ A
(` x) † = ` x
(ƛ ⊢A) † = ƛ ⊢A
(⊢A · ⊢A₁) † = ⊢A · ⊢A₁
`zero † = `zero
(`suc ⊢A) † = `suc ⊢A
case ⊢A ⊢A₁ ⊢A₂ † = case ⊢A ⊢A₁ ⊢A₂
(μ ⊢A) † = μ ⊢A
`let ⊢A ⊢A₁ † = (ƛ ⊢A₁) · ⊢A

†→~ : ∀ {Γ A} {M N : Γ ⊢ A} → M † ≡ N → M ~ N
†→~ {Γ} {A} {` x} {.(` x)} refl = ~`
†→~ {Γ} {.(_ ⇒ _)} {ƛ M} {.(ƛ M)} refl = ~ƛ †→~ {!!}
†→~ {Γ} {A} {M · M₈} {.(M · M₈)} refl = {!!}
†→~ {Γ} {.`ℕ} {`zero} {.`zero} refl = {!!}
†→~ {Γ} {.`ℕ} {`suc M} {.(`suc M)} refl = {!!}
†→~ {Γ} {A} {case M M₈ M₉} {.(case M M₈ M₉)} refl = {!!}
†→~ {Γ} {A} {μ M} {.(μ M)} refl = {!!}
†→~ {Γ} {A} {`let M M₈} {.((ƛ M₈) · M)} refl = {!!}

-}
