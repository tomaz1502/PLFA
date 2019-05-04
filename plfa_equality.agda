module plfa_equality where

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

infix 4 _≡_

sym : ∀ {A : Set} {x y : A}
  → x ≡ y
  --------
  → y ≡ x

sym refl = refl

trans : ∀ {A : Set} {x y z : A}
  → x ≡ y
  → y ≡ z
  ---------
  → x ≡ z
trans refl refl = refl

cong : ∀ {A B : Set} {x y : A} (f : A → B)
  → x ≡ y
  ----------
  → f x ≡ f y
cong f refl = refl

cong-app : ∀ {A B : Set} {f g : A → B}
  → f ≡ g
  ---------------------
  → ∀ (x : A) → f x ≡ g x
cong-app refl x = refl

subst : ∀ {A : Set} {x y : A} (P : A → Set)
  → x ≡ y
  → P x
  ----------
  → P y
subst P refl px = px

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
zero + n  =  n
(suc m) + n  =  suc (m + n)

module ≡-Reasoning {A : Set} where

  infix  1 begin_
  infixr 2 _≡⟨⟩_ _≡⟨_⟩_
  infix  3 _∎

  begin_ : ∀ {x y : A}
    → x ≡ y
    -----
    → x ≡ y
  begin x≡y  =  x≡y

  _≡⟨⟩_ : ∀ (x : A) {y : A}
    → x ≡ y
    -----
    → x ≡ y
  x ≡⟨⟩ x≡y  =  x≡y

  _≡⟨_⟩_ : ∀ (x : A) {y z : A}
    → x ≡ y
    → y ≡ z
    -----
    → x ≡ z
  x ≡⟨ x≡y ⟩ y≡z  =  trans x≡y y≡z

  _∎ : ∀ (x : A)
    -----
    → x ≡ x
  x ∎  =  refl
 
open ≡-Reasoning


postulate
  +-identity : ∀ (m : ℕ) → m + zero ≡ m
  +-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n) 

+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm m zero =
  begin
    m + zero
  ≡⟨ +-identity m ⟩
    m
  ≡⟨⟩
    zero + m
  ∎

+-comm m (suc n) =
  begin
    m + (suc n)
  ≡⟨ +-suc m n ⟩
    suc (m + n)
  ≡⟨ cong suc (+-comm m n)⟩
    suc (n + m)
  ≡⟨⟩
    (suc n) + m ∎

module ≤-Reasoning where

  data _≤_ : ℕ → ℕ → Set where

    z≤n : ∀ {n : ℕ}
          -----------
          → zero ≤ n

    s≤s : ∀ {n m : ℕ}
          → n ≤ m
          ----------------
          → suc n ≤ suc m

  infix  4 _≤_
  infix  1 beginL_
  infixr 2 _≤⟨⟩_ _≤⟨_⟩_
  infix  3 _∎L

  postulate
    ≤-trans : ∀ {x y z : ℕ}
      → x ≤ y
      → y ≤ z
      -------
      → x ≤ z
    ≤-refl : ∀ {x : ℕ} → x ≤ x

  beginL_ : ∀ {x y : ℕ}
    → x ≤ y
    ------
    → x ≤ y
  beginL P = P

  _≤⟨⟩_ : ∀ (x : ℕ) {y : ℕ}
    → x ≤ y
    -------
    → x ≤ y
  x ≤⟨⟩ P = P

  _≤⟨_⟩_ : ∀ (x : ℕ) {y z : ℕ}
    → x ≤ y
    → y ≤ z
    --------
    → x ≤ z
  x ≤⟨ x≤y ⟩ y≤z = ≤-trans x≤y y≤z


  _∎L : ∀ (x : ℕ)
        ---------
        → x ≤ x
  _∎L x = ≤-refl {x}

open ≤-Reasoning

{-# BUILTIN EQUALITY _≡_ #-}

≡-implies-≤ : ∀ {x y : ℕ}
  → x ≡ y
  ---------
  → x ≤ y

≡-implies-≤ x≡y rewrite x≡y = ≤-refl

+-mono¹-≤ : ∀ (m p q : ℕ)
  → p ≤ q
  --------
  → m + p ≤ m + q

+-mono¹-≤ zero p q p≤q =
  beginL
    zero + p
  ≤⟨⟩
    p
  ≤⟨ p≤q ⟩
    q
  ≤⟨⟩
    zero + q
  ∎L

+-mono¹-≤ (suc m) p q p≤q =
  beginL
    (suc m) + p
  ≤⟨⟩
    suc (m + p)
  ≤⟨ s≤s (+-mono¹-≤ m p q p≤q) ⟩
    suc (m + q)
  ≤⟨⟩
    (suc m) + q
  ∎L

+-mono²-≤ : ∀ (m p q : ℕ)
  → p ≤ q
  ---------
  → p + m ≤ q + m

+-mono²-≤ zero p q p≤q =
  beginL
    p + zero
  ≤⟨ ≡-implies-≤ (+-identity p) ⟩
    p
  ≤⟨ p≤q ⟩
    q
  ≤⟨ ≡-implies-≤ (sym (+-identity q)) ⟩
    q + zero
  ∎L

+-mono²-≤ (suc m) p q p≤q =
  beginL
    p + (suc m)
  ≤⟨ ≡-implies-≤ (+-suc p m) ⟩
    suc (p + m)
  ≤⟨ s≤s (+-mono²-≤ m p q p≤q) ⟩
    suc (q + m)
  ≤⟨ ≡-implies-≤ (sym (+-suc q m)) ⟩
    q + (suc m)
  ∎L

+-mono-≤ : ∀ (m n p q : ℕ)
  → m ≤ n
  → p ≤ q
  ----------
  → m + p ≤ n + q

+-mono-≤ m n p q m≤n p≤q =
  beginL
    m + p
  ≤⟨ +-mono²-≤ p m n m≤n ⟩
    n + p
  ≤⟨ +-mono¹-≤ n p q p≤q ⟩
    n + q
  ∎L

_≐_ : ∀ {A : Set} (x y : A) → Set₁
_≐_ {A} x y = ∀ (P : A → Set) → P x → P y
