module plfa_lists where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)
open Eq.≡-Reasoning
open import plfa_decidable using (Bool; true; false; T; _∧_; _∨_; not; Dec; yes; no)
open import plfa_naturals using (ℕ; zero; suc; _+_; _*_; _∸_)
open import plfa_relations using (_≤_; s≤s; z≤n)
open import plfa_induction using (+-assoc; *-identityˡ; *-identityʳ; +-identity; *-assoc; *-comm; *-distr-+; +-comm; *-suc; +-suc; +-identityˡ)
open import plfa_negation using (¬_)
open import plfa_connectives using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; ∃; ∃-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Empty using (⊥-elim)
open import Function using (_∘_)
open import Level using (Level)
open import plfa_isomorphism using (_≃_; _⇔_; extensionality)

data List (A : Set) : Set where
 [] : List A
 _∷_ : A → List A → List A

infixr 5 _∷_

_ : List ℕ
_ = 2 ∷ []

data List′ : Set → Set where
  []′  : ∀ {A : Set} → List′ A
  _∷′_ : ∀ {A : Set} → A → List′ A → List′ A

_ : List ℕ
_ = _∷_ {ℕ} 0 (_∷_ {ℕ} 1 (_∷_ {ℕ} 2 ([] {ℕ})))


{-# BUILTIN LIST List #-}

pattern [_] z = z ∷ []
pattern [_,_] y z = y ∷ z ∷ []
pattern [_,_,_] x y z = x ∷ y ∷ z ∷ []
pattern [_,_,_,_] w x y z = w ∷ x ∷ y ∷ z ∷ []
pattern [_,_,_,_,_] v w x y z = v ∷ w ∷ x ∷ y ∷ z ∷ []
pattern [_,_,_,_,_,_] u v w x y z = u ∷ v ∷ w ∷ x ∷ y ∷ z ∷ []

infixr 5 _++_

_++_ : ∀ {A : Set} → List A → List A → List A
[]       ++ ys  =  ys
(x ∷ xs) ++ ys  =  x ∷ (xs ++ ys)

_ : [ 0 , 1 , 2 ] ++ [ 3 , 4 ] ≡ [ 0 , 1 , 2 , 3 , 4 ]
_ =
  begin
    0 ∷ 1 ∷ 2 ∷ [] ++ 3 ∷ 4 ∷ []
  ≡⟨⟩
    0 ∷ (1 ∷ 2 ∷ [] ++ 3 ∷ 4 ∷ [])
  ≡⟨⟩
    0 ∷ 1 ∷ (2 ∷ [] ++ 3 ∷ 4 ∷ [])
  ≡⟨⟩
    0 ∷ 1 ∷ 2 ∷ ([] ++ 3 ∷ 4 ∷ [])
  ≡⟨⟩
    0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ []
  ∎

++-assoc : ∀ {A : Set} (xs ys zs : List A) → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc [] ys zs =
  begin
    ([] ++ ys) ++ zs
  ≡⟨⟩
    ys ++ zs
  ≡⟨⟩
    [] ++ (ys ++ zs)
  ∎
++-assoc (x ∷ xs) ys zs =
  begin
    ((x ∷ xs) ++ ys) ++ zs
  ≡⟨⟩
    (x ∷ (xs ++ ys)) ++ zs
  ≡⟨⟩
    x ∷ ((xs ++ ys) ++ zs)
  ≡⟨ cong (x ∷_) (++-assoc xs ys zs)⟩
    x ∷ (xs ++ (ys ++ zs))
  ≡⟨⟩
    (x ∷ xs) ++ (ys ++ zs)
  ∎

++-identityˡ : ∀ {A : Set} (xs : List A) → [] ++ xs ≡ xs
++-identityˡ xs =
  begin
    [] ++ xs
  ≡⟨⟩
    xs
  ∎

++-identityʳ : ∀ {A : Set} (xs : List A) → xs ++ [] ≡ xs
++-identityʳ [] =
  begin
    [] ++ []
  ≡⟨⟩
    []
  ∎
++-identityʳ (x ∷ xs) =
  begin
    (x ∷ xs) ++ []
  ≡⟨⟩
    x ∷ (xs ++ [])
  ≡⟨ cong (x ∷_) (++-identityʳ xs) ⟩
    x ∷ xs
  ∎

length : ∀ {A : Set} → List A → ℕ
length [] = zero
length (x ∷ xs) = suc (length xs)

_ : length [ 0 , 1 , 2 ] ≡ 3
_ =
  begin
    length (0 ∷ 1 ∷ 2 ∷ [])
  ≡⟨⟩
    suc (length (1 ∷ 2 ∷ []))
  ≡⟨⟩
    suc (suc (length (2 ∷ [])))
  ≡⟨⟩
    suc (suc (suc (length {ℕ} [])))
  ≡⟨⟩
    suc (suc (suc zero))
  ∎

length-++ : ∀ {A : Set} (xs ys : List A) → length (xs ++ ys) ≡ length xs + length ys
length-++ {A} [] ys =
  begin
    length ([] ++ ys)
  ≡⟨⟩
    length ys
  ≡⟨⟩
    length {A} [] + length ys
  ∎
length-++ (x ∷ xs) ys =
  begin
    length ((x ∷ xs) ++ ys)
  ≡⟨⟩
    suc (length (xs ++ ys))
  ≡⟨ cong suc (length-++ xs ys) ⟩
    suc (length xs + length ys)
  ≡⟨⟩
    length (x ∷ xs) + length ys
  ∎

reverse : ∀ {A : Set} → List A → List A
reverse [] = []
reverse (x ∷ xs) = (reverse xs) ++ [ x ]

_ : reverse [ 0 , 1 , 2 ] ≡ [ 2 , 1 , 0 ]
_ =
  begin
    reverse (0 ∷ 1 ∷ 2 ∷ [])
  ≡⟨⟩
    reverse (1 ∷ 2 ∷ []) ++ [ 0 ]
  ≡⟨⟩
    (reverse (2 ∷ []) ++ [ 1 ]) ++ [ 0 ]
  ≡⟨⟩
    ((reverse [] ++ [ 2 ]) ++ [ 1 ]) ++ [ 0 ]
  ≡⟨⟩
    (([] ++ [ 2 ]) ++ [ 1 ]) ++ [ 0 ]
  ≡⟨⟩
    (([] ++ 2 ∷ []) ++ 1 ∷ []) ++ 0 ∷ []
  ≡⟨⟩
    (2 ∷ [] ++ 1 ∷ []) ++ 0 ∷ []
  ≡⟨⟩
    2 ∷ ([] ++ 1 ∷ []) ++ 0 ∷ []
  ≡⟨⟩
    (2 ∷ 1 ∷ []) ++ 0 ∷ []
  ≡⟨⟩
    2 ∷ (1 ∷ [] ++ 0 ∷ [])
  ≡⟨⟩
    2 ∷ 1 ∷ ([] ++ 0 ∷ [])
  ≡⟨⟩
    2 ∷ 1 ∷ 0 ∷ []
  ≡⟨⟩
    [ 2 , 1 , 0 ]
  ∎

reverse-++-commute : ∀ {A : Set} {xs ys : List A} → reverse (xs ++ ys) ≡ (reverse ys) ++ (reverse xs)
reverse-++-commute {A} {[]} {ys} =
  begin
    reverse ([] ++ ys)
  ≡⟨⟩
    reverse ys
  ≡⟨ sym (++-identityʳ (reverse ys)) ⟩
    (reverse ys) ++ []
  ≡⟨⟩
    (reverse ys) ++ (reverse [])
  ∎
reverse-++-commute {A} {x ∷ xs} {ys} = -- cong (_++ [ x ]) (reverse-++-commute {A} {xs} {ys})
  begin
    reverse ((x ∷ xs) ++ ys)
  ≡⟨⟩
    reverse (x ∷ (xs ++ ys))
  ≡⟨⟩
    (reverse (xs ++ ys)) ++ [ x ]
  ≡⟨ cong (_++ [ x ]) (reverse-++-commute {A} {xs} {ys}) ⟩
    ((reverse ys) ++ (reverse xs)) ++ [ x ]
  ≡⟨ ++-assoc (reverse ys) (reverse xs) [ x ] ⟩
    (reverse ys) ++ (reverse (x ∷ xs))
  ∎

reverse-involutive : ∀ {A : Set} {xs : List A} → reverse (reverse xs) ≡ xs
reverse-involutive {A} {[]} = refl
reverse-involutive {A} {x ∷ xs} =
  begin
    reverse (reverse (x ∷ xs))
  ≡⟨⟩
    reverse ((reverse xs) ++ [ x ])
  ≡⟨ reverse-++-commute {A} {reverse xs} {[ x ]} ⟩
    [ x ] ++ (reverse (reverse xs))
  ≡⟨ cong ([ x ] ++_) (reverse-involutive {A} {xs}) ⟩
    [ x ] ++ xs
  ≡⟨⟩
    x ∷ xs
  ∎

shunt : ∀ {A : Set} → List A → List A → List A
shunt [] ys = ys
shunt (x ∷ xs) ys = (shunt xs) (x ∷ ys)

shunt-reverse : ∀ {A : Set} (xs ys : List A)
  → shunt xs ys ≡ (reverse xs) ++ ys
shunt-reverse  []     ys = refl
shunt-reverse  (x ∷ xs) ys =
  begin
    shunt (x ∷ xs) ys
  ≡⟨⟩
    shunt xs (x ∷ ys)
  ≡⟨ shunt-reverse xs (x ∷ ys) ⟩
    (reverse xs) ++ (x ∷ ys)
  ≡⟨⟩
    (reverse xs) ++ ([ x ] ++ ys)
  ≡⟨ sym (++-assoc (reverse xs) ([ x ]) (ys)) ⟩
    ((reverse xs) ++ [ x ]) ++ ys
  ≡⟨⟩
    (reverse (x ∷ xs)) ++ ys
  ∎

reverse´ : ∀ {A : Set} → List A → List A
reverse´ xs = shunt xs []

reverses : ∀ {A : Set} (xs : List A) → reverse´ xs ≡ reverse xs
reverses xs =
  begin
    reverse´ xs
  ≡⟨⟩
    shunt xs []
  ≡⟨ shunt-reverse xs [] ⟩
    reverse xs ++ []
  ≡⟨ ++-identityʳ (reverse xs) ⟩
    reverse xs
  ∎

_ : reverse´ [ 0 , 1 , 2 ] ≡ [ 2 , 1 , 0 ]
_ =
  begin
    reverse´ (0 ∷ 1 ∷ 2 ∷ [])
  ≡⟨⟩
    shunt (0 ∷ 1 ∷ 2 ∷ []) []
  ≡⟨⟩
  shunt (1 ∷ 2 ∷ []) (0 ∷ [])
    ≡⟨⟩
    shunt (2 ∷ []) (1 ∷ 0 ∷ [])
  ≡⟨⟩
    shunt [] (2 ∷ 1 ∷ 0 ∷ [])
  ≡⟨⟩
    2 ∷ 1 ∷ 0 ∷ []
  ∎

map : ∀ {A B : Set} → (A → B) → List A → List B
map f []        =  []
map f (x ∷ xs)  =  f x ∷ map f xs

_ : map suc [ 0 , 1 , 2 ] ≡ [ 1 , 2 , 3 ]
_ =
  begin
    map suc (0 ∷ 1 ∷ 2 ∷ [])
  ≡⟨⟩
    suc 0 ∷ map suc (1 ∷ 2 ∷ [])
  ≡⟨⟩
    suc 0 ∷ suc 1 ∷ map suc (2 ∷ [])
  ≡⟨⟩
    suc 0 ∷ suc 1 ∷ suc 2 ∷ map suc []
  ≡⟨⟩
    suc 0 ∷ suc 1 ∷ suc 2 ∷ []
  ≡⟨⟩
    1 ∷ 2 ∷ 3 ∷ []
  ∎

sucs : List ℕ → List ℕ
sucs = map suc

_ : sucs [ 0 , 1 , 2 ] ≡ [ 1 , 2 , 3 ]
_ =
  begin
    sucs [ 0 , 1 , 2 ]
  ≡⟨⟩
    map suc [ 0 , 1 , 2 ]
  ≡⟨⟩
    [ 1 , 2 , 3 ]
  ∎

map-compose-ext : {A B C : Set} (f : A → B) (g : B → C) (xs : List A) → map (g ∘ f) xs ≡ (map g) ((map f) xs)
map-compose-ext f g [] = refl
map-compose-ext f g (x ∷ xs) =
  begin
    map (g ∘ f) (x ∷ xs)
  ≡⟨⟩
    ((g ∘ f) x) ∷ (map (g ∘ f) xs)
  ≡⟨ cong (((g ∘ f) x) ∷_) ( map-compose-ext f g xs) ⟩
    ((g ∘ f) x) ∷ ((map g) ((map f) xs))
  ∎

map-compose : ∀ {A B C : Set} (f : A → B) (g : B → C) → map (g ∘ f) ≡ (map g) ∘ (map f)
map-compose {A} {B} {C} f g = extensionality (map-compose-ext f g)

map-++-commute : ∀ {A B : Set} (f : A → B) (xs ys : List A) → map f (xs ++ ys) ≡ (map f xs) ++ (map f ys)
map-++-commute f []       ys = refl
map-++-commute f (x ∷ xs) ys =
  begin
    map f ((x ∷ xs) ++ ys)
  ≡⟨⟩
    map f (x ∷ (xs ++ ys))
  ≡⟨⟩
    (f x) ∷ (map f (xs ++ ys))
  ≡⟨ cong ((f x) ∷_) (map-++-commute f xs ys) ⟩
    (f x) ∷ ((map f xs) ++ (map f ys))
  ∎

data Tree (A B : Set) : Set where
  leaf : A → Tree A B
  node : Tree A B → B → Tree A B → Tree A B

map-Tree : ∀ {A B C D : Set} → (A → C) → (B → D) → Tree A B → Tree C D
map-Tree f g (leaf a)       = leaf (f a)
map-Tree f g (node ta b tb) = node (map-Tree f g ta) (g b) (map-Tree f g tb)

foldr : ∀ {A B : Set} → (A → B → B) → B → List A → B
foldr _⊗_ e []       = e
foldr _⊗_ e (x ∷ xs) = x ⊗ (foldr _⊗_ e xs)

_ : foldr _+_ 0 [ 1 , 2 , 3 , 4 ] ≡ 10
_ =
  begin
    foldr _+_ 0 (1 ∷ 2 ∷ 3 ∷ 4 ∷ [])
  ≡⟨⟩
    1 + foldr _+_ 0 (2 ∷ 3 ∷ 4 ∷ [])
  ≡⟨⟩
    1 + (2 + foldr _+_ 0 (3 ∷ 4 ∷ []))
  ≡⟨⟩
    1 + (2 + (3 + foldr _+_ 0 (4 ∷ [])))
  ≡⟨⟩
    1 + (2 + (3 + (4 + foldr _+_ 0 [])))
  ≡⟨⟩
    1 + (2 + (3 + (4 + 0)))
  ∎

sum : List ℕ → ℕ
sum = foldr _+_ 0

_ : sum [ 1 , 2 , 3 , 4 ] ≡ 10
_ =
  begin
    sum [ 1 , 2 , 3 , 4 ]
  ≡⟨⟩
    foldr _+_ 0 [ 1 , 2 , 3 , 4 ]
  ≡⟨⟩
    10
  ∎

product : List ℕ → ℕ
product = foldr _*_ 1

_ : product [ 1 , 2 , 3 , 4 ] ≡ 24
_ = refl

foldr-++ : ∀ {A B : Set} (_⊗_ : A → B → B) (e : B) (xs ys : List A) → foldr _⊗_ e (xs ++ ys) ≡ foldr _⊗_ (foldr _⊗_ e ys) xs
foldr-++ _⊗_ e []       ys = refl
foldr-++ _⊗_ e (x ∷ xs) ys =
  begin
    foldr _⊗_ e ((x ∷ xs) ++ ys)
  ≡⟨⟩
    foldr _⊗_ e (x ∷ (xs ++ ys))
  ≡⟨⟩
    x ⊗ (foldr _⊗_ e (xs ++ ys))
  ≡⟨ cong (x ⊗_) (foldr-++ _⊗_ e xs ys) ⟩
    x ⊗ (foldr _⊗_ (foldr _⊗_ e ys) xs)
  ∎


map-is-foldr_ext : ∀ {A B : Set} (f : A → B) (ys : List A) → map f ys ≡ foldr (λ x xs → f x ∷ xs) [] ys
map-is-foldr_ext f [] = refl
map-is-foldr_ext f (x ∷ xs) =
  begin
    map f (x ∷ xs)
  ≡⟨⟩
    (f x) ∷ (map f xs)
  ≡⟨ cong ((f x) ∷_ ) (map-is-foldr_ext f xs) ⟩
    (f x) ∷ (foldr (λ x xs → f x ∷ xs) [] xs)
  ∎

map-is-foldr : ∀ {A B : Set} {f : A → B} → map f ≡ foldr (λ x xs → f x  ∷ xs) []
map-is-foldr {A} {B} {f} = extensionality (map-is-foldr_ext f)

fold-Tree : ∀ {A B C : Set} → (A → C) → (C → B → C → C) → Tree A B → C

fold-Tree f g (leaf a)       = f a
fold-Tree f g (node T1 b T2) = g (fold-Tree f g T1) b (fold-Tree f g T2)


make-node : ∀ {B C D : Set} → (B → D) → Tree C D → B → Tree C D → Tree C D
make-node g t1 b t2 = node t1 (g b) t2

make-leaf : ∀ {A C D : Set} → (A → C) → A → Tree C D
make-leaf f a = leaf (f a)

node_part : ∀ {A B : Set} → B → Tree A B → Tree A B → Tree A B
node_part y z x = node x y z

map-is-fold-Tree_ext : ∀ {A B C D : Set} (f : A → C) (g : B → D) (T : Tree A B)
  → map-Tree f g T ≡ fold-Tree (make-leaf f) (make-node g) T
map-is-fold-Tree_ext f g (leaf a) = refl
map-is-fold-Tree_ext f g (node T1 b T2) =
  begin
    map-Tree f g (node T1 b T2)
  ≡⟨⟩
    node (map-Tree f g T1) (g b) (map-Tree f g T2)
  ≡⟨ cong (node (map-Tree f g T1) (g b)) (map-is-fold-Tree_ext f g T2) ⟩
    node (map-Tree f g T1) (g b) (fold-Tree (make-leaf f) (make-node g) T2)
 ≡⟨ cong ( λ {x → (node x (g b) (fold-Tree (make-leaf f) (make-node g) T2)) }) (map-is-fold-Tree_ext f g T1)  ⟩
    node (fold-Tree (make-leaf f) (make-node g) T1) (g b) (fold-Tree (make-leaf f) (make-node g) T2)
  ∎

-- ≡⟨ cong (node_part (g b) (fold-Tree (make-leaf f) (make-node g) T2)) (map-is-fold-Tree_ext f g T1) ⟩

map-is-fold-Tree : ∀ {A B C D : Set} {f : A → C} {g : B → D} → map-Tree f g ≡ fold-Tree (make-leaf f) (make-node g) -- troca C por Tree A B no fold
map-is-fold-Tree {A} {B} {C} {D} {f} {g} = extensionality (map-is-fold-Tree_ext {A} {B} {C} {D} f g)

downFrom : ℕ → List ℕ
downFrom zero    = []
downFrom (suc n) = n ∷ (downFrom n)

_ : (downFrom 3) ≡ [ 2 , 1 , 0 ]
_ = refl

n+n≡2n : ∀ (n : ℕ) → n * 2 ≡ n + n
n+n≡2n  zero = refl
n+n≡2n (suc n) rewrite n+n≡2n n = cong suc (sym (+-suc n n)) 

sum-downFrom : ∀ (n : ℕ) → sum (downFrom n) * 2 ≡ n * (n ∸ 1)
sum-downFrom zero       = refl
sum-downFrom (suc zero) = refl
sum-downFrom n'@(suc (suc n))    =
  begin
    sum (downFrom n') * 2
  ≡⟨⟩
    ((suc n) + sum (downFrom (suc n)) ) * 2
  ≡⟨ *-distr-+ (suc n) (sum (downFrom (suc n))) 2 ⟩
    (suc n) * 2 + (sum (downFrom (suc n))) * 2
  ≡⟨ cong (λ x → (suc n) * 2 + x) (sum-downFrom (suc n)) ⟩
    (suc n) * 2 + ((suc n) * n)
  ≡⟨⟩
    suc (suc (n * 2 + (n + n * n)))
  ≡⟨ cong (λ x → suc (suc (n * 2 + x))) (sym (*-suc n n)) ⟩
    suc (suc (n * 2 + n * (suc n)))
  ≡⟨ cong (λ x → suc (suc x + n * (suc n))) (n+n≡2n n) ⟩
    suc (suc ((n + n) + (n * (suc n))))
  ≡⟨ cong (λ x → suc (suc x)) (+-assoc n n (n * (suc n))) ⟩
    suc (suc (n + (n + (n * (suc n)))))
  ≡⟨ cong suc (sym (+-suc n (n + (n * (suc n))))) ⟩
    suc (n + suc (n + n * (suc n)))
  ∎



record IsMonoid {A : Set} (_⊗_ : A → A → A) (e : A) : Set where
  field
    assoc     : ∀ (x y z : A) → (x ⊗ y) ⊗ z ≡ x ⊗ (y ⊗ z)
    identityˡ : ∀ (x : A) → e ⊗ x ≡ x
    identityʳ : ∀ (x : A) → x ⊗ e ≡ x

open IsMonoid


+-monoid : IsMonoid _+_ 0
+-monoid =
  record
  { assoc     = +-assoc
  ; identityˡ = +-identityˡ
  ; identityʳ = +-identity
  }

*-monoid : IsMonoid _*_ 1
*-monoid =
  record
  { assoc     = *-assoc
  ; identityʳ = *-identityʳ
  ; identityˡ = *-identityˡ
  }

++-monoid : ∀ {A : Set} → IsMonoid {List A} _++_ []
++-monoid =
  record
  { assoc     = ++-assoc
  ; identityʳ = ++-identityʳ
  ; identityˡ = ++-identityˡ
  }

foldr-monoid : ∀ {A : Set} (_⊗_ : A → A → A) (e : A) → IsMonoid _⊗_ e →
  ∀ (xs : List A) (y : A) → foldr _⊗_ y xs ≡ foldr _⊗_ e xs ⊗ y
foldr-monoid _⊗_ e ⊗-monoid [] y =
  begin
    foldr _⊗_ y []
  ≡⟨⟩
    y
  ≡⟨ sym (identityˡ ⊗-monoid y) ⟩
    (e ⊗ y)
  ≡⟨⟩
    foldr _⊗_ e [] ⊗ y
  ∎
foldr-monoid _⊗_ e ⊗-monoid (x ∷ xs) y =
  begin
    foldr _⊗_ y (x ∷ xs)
  ≡⟨⟩
    x ⊗ (foldr _⊗_ y xs)
  ≡⟨ cong (x ⊗_) (foldr-monoid _⊗_ e ⊗-monoid xs y) ⟩
    x ⊗ (foldr _⊗_ e xs ⊗ y)
  ≡⟨ sym (assoc ⊗-monoid x (foldr _⊗_ e xs) y) ⟩
    (x ⊗ foldr _⊗_ e xs) ⊗ y
  ≡⟨⟩
    foldr _⊗_ e (x ∷ xs) ⊗ y
  ∎

foldr-monoid-++ : ∀ {A : Set} (_⊗_ : A → A → A) (e : A) → IsMonoid _⊗_ e →
  ∀ (xs ys : List A) → foldr _⊗_ e (xs ++ ys) ≡ foldr _⊗_ e xs ⊗ foldr _⊗_ e ys
foldr-monoid-++ _⊗_ e monoid-⊗ xs ys =
  begin
    foldr _⊗_ e (xs ++ ys)
  ≡⟨ foldr-++ _⊗_ e xs ys ⟩
    foldr _⊗_ (foldr _⊗_ e ys) xs
  ≡⟨ foldr-monoid _⊗_ e monoid-⊗ xs (foldr _⊗_ e ys) ⟩
    foldr _⊗_ e xs ⊗ foldr _⊗_ e ys
  ∎

foldl : ∀ {A B : Set} → (B → A → B) → B → List A → B
foldl _⊗_ y []       = y
foldl _⊗_ y (x ∷ xs) = foldl _⊗_ (y ⊗ x) xs


lemma-foldl-op : ∀ {A : Set} → (_⊗_ : A → A → A) → (e : A) → (xs : List A) → IsMonoid _⊗_ e → (y : A) →
  y ⊗ foldl _⊗_ e xs ≡ foldl _⊗_ y xs
lemma-foldl-op _⊗_ e []       ⊗-monoid y = identityʳ ⊗-monoid y
lemma-foldl-op _⊗_ e (x ∷ xs) ⊗-monoid y =
  begin
    y ⊗ foldl _⊗_ (e ⊗ x) xs
  ≡⟨ cong (λ z → y ⊗ foldl _⊗_ z xs) (identityˡ ⊗-monoid x) ⟩
    y ⊗ foldl _⊗_ x xs
  ≡⟨ cong (y ⊗_) (sym (lemma-foldl-op _⊗_ e xs ⊗-monoid x)) ⟩
    y ⊗ (x ⊗ foldl _⊗_ e xs)
  ≡⟨ sym (assoc ⊗-monoid y x (foldl _⊗_ e xs)) ⟩
    (y ⊗ x) ⊗ foldl _⊗_ e xs
  ≡⟨ lemma-foldl-op _⊗_ e xs ⊗-monoid (y ⊗ x) ⟩
    foldl _⊗_ (y ⊗ x) xs
  ∎

{- achei que ia precisar, não precisou -}
lemma-foldl-conc : ∀ {A : Set} → (_⊗_ : A → A → A) → (e : A) → (xs : List A) → (y : A) → IsMonoid _⊗_ e →
  y ⊗ (foldl _⊗_ e xs) ≡ foldl _⊗_ e (y ∷ xs)

lemma-foldl-conc _⊗_ e xs y ⊗-monoid rewrite identityˡ ⊗-monoid y | identityʳ ⊗-monoid y | lemma-foldl-op _⊗_ e xs ⊗-monoid y = refl

foldr-monoid-foldl : ∀ {A : Set} → (_⊗_ : A → A → A) → (e : A) → (xs : List A) → IsMonoid _⊗_ e →
  foldr _⊗_ e xs ≡ foldl _⊗_ e xs
foldr-monoid-foldl _⊗_ e []       monoid-⊗ = refl
foldr-monoid-foldl _⊗_ e (x ∷ xs) monoid-⊗ rewrite identityˡ monoid-⊗ x =
  begin
    foldr _⊗_ e (x ∷ xs)
  ≡⟨⟩
    x ⊗ (foldr _⊗_ e xs)
  ≡⟨ cong (x ⊗_) (foldr-monoid-foldl _⊗_ e xs monoid-⊗) ⟩
    x ⊗ (foldl _⊗_ e xs)
  ≡⟨ lemma-foldl-op _⊗_ e xs monoid-⊗ x ⟩
    foldl _⊗_ x xs
  ∎

data All {A : Set} (P : A → Set) : List A → Set where
  []  : All P []
  _∷_ : ∀ {x : A} {xs : List A} → P x → All P xs → All P (x ∷ xs)

data Any {A : Set} (P : A → Set) : List A → Set where
  here  : ∀ {x : A} {xs : List A} → P x → Any P (x ∷ xs)
  there : ∀ {x : A} {xs : List A} → Any P xs → Any P (x ∷ xs)

infix 4 _∈_ _∉_

_∈_ : ∀ {A : Set} (x : A) (xs : List A) → Set
x ∈ xs = Any (x ≡_) xs

_∉_ : ∀ {A : Set} (x : A) (xs : List A) → Set
x ∉ xs = ¬ (x ∈ xs)

_ : 0 ∈ [ 0 , 1 , 0 , 2 ]
_ = here refl

_ : 0 ∈ [ 0 , 1 , 0 , 2 ]
_ = there (there (here refl))

not-in : 3 ∉ [ 0 , 1 , 0 , 2 ]
not-in (here ())
not-in (there (here ()))
not-in (there (there (here ())))
not-in (there (there (there (here ()))))
not-in (there (there (there (there ()))))



Any-++-⇔ : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
  Any P (xs ++ ys) ⇔ (Any P xs ⊎ Any P ys)
Any-++-⇔ xs ys =
  record
    { to    = to xs ys
    ; from  = from xs ys
    }
  where

  to : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
    Any P (xs ++ ys) → (Any P xs ⊎ Any P ys)
  to []       ys Pxs++ys = inj₂ Pxs++ys
  to (x ∷ xs) ys (here x₁)       = inj₁ (here x₁)
  to (x ∷ xs) ys (there Pxs++ys) with (to xs ys Pxs++ys)
  ... | inj₁ AnyPxs = inj₁ (there AnyPxs)
  ... | inj₂ AnyPys = inj₂ AnyPys

  from : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
    (Any P xs ⊎ Any P ys) → Any P (xs ++ ys)

  from []       ys (inj₁ ())
  from []       ys (inj₂ Pys)            = Pys
  from (x ∷ xs) ys (inj₁ (here Px))      = here Px
  from (x ∷ xs) ys (inj₁ (there AnyPxs)) = there (from xs ys (inj₁ AnyPxs))
  from (x ∷ xs) ys (inj₂ AnyPys)         = there (from xs ys (inj₂ AnyPys))

All-++-≃ : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
  All P (xs ++ ys) ≃ (All P xs × All P ys)

All-++-≃ xs ys =
  record
  { to      = to xs ys
  ; from    = from xs ys
  ; from∘to = from-to xs ys
  ; to∘from = to-from xs ys
  }
  where

  to : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
    All P (xs ++ ys) → (All P xs × All P ys)
  to [] ys Pys = ⟨ [] , Pys ⟩
  to (x ∷ xs) ys (Px ∷ Pxs++ys) with to xs ys Pxs++ys
  ... | ⟨ Pxs , Pys ⟩ = ⟨ Px ∷ Pxs , Pys ⟩

  from : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
    All P xs × All P ys → All P (xs ++ ys)
  from [] ys ⟨ [] , Pys ⟩ = Pys
  from (x ∷ xs) ys ⟨ Px ∷ Pxs , Pys ⟩ =  Px ∷ from xs ys ⟨ Pxs , Pys ⟩

  from-to : ∀ {A : Set} {P : A → Set} (xs ys : List A) (all : All P (xs ++ ys)) →
    (from xs ys (to xs ys all)) ≡ all
  from-to []       ys all        = refl
  from-to (x ∷ xs) ys (Px ∷ all) = cong (Px ∷_) (from-to xs ys all)

  to-from : ∀ {A : Set} {P : A → Set} (xs ys : List A) (AllPxsys : (All P xs) × (All P ys)) →
    (to xs ys (from xs ys AllPxsys)) ≡ AllPxsys
  to-from [] ys ⟨ [] , _ ⟩               = refl
  to-from (x ∷ xs) ys ⟨ Px ∷ Pxs , Pys ⟩ with to-from xs ys ⟨ Pxs , Pys ⟩
  ... | IH =
    begin
      ⟨ Px ∷ proj₁ (to xs ys (from xs ys ⟨ Pxs , Pys ⟩)) , proj₂ (to xs ys (from xs ys ⟨ Pxs , Pys ⟩)) ⟩
    ≡⟨ cong (λ x → ⟨ Px ∷ (proj₁ x) , proj₂ x ⟩) IH ⟩
      ⟨ Px ∷ Pxs , Pys ⟩
    ∎

_∘´_ : ∀ {ℓ₁ ℓ₂ ℓ₃ : Level} {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ₃}
  → (B → C) → (A → B) → A → C
(g ∘´ f) x  =  g (f x)


¬Any≃All¬-to : ∀ {A : Set} (P : A → Set) (xs : List A)
  → (¬_ ∘´ Any P) xs → All (¬_ ∘´ P) xs

¬Any≃All¬-to P []       _ = []
¬Any≃All¬-to P (x ∷ xs) AnyPxxs→⊥ = (AnyPxxs→⊥ ∘ here) ∷ ¬Any≃All¬-to P xs (λ Pxs → AnyPxxs→⊥ (there Pxs))

¬Any≃All¬-from : ∀ {A : Set} (P : A → Set) (xs : List A)
  → All (¬_ ∘´ P) xs → (¬_ ∘´ Any P) xs

¬Any≃All¬-from P []       All¬Pxs      = λ()
¬Any≃All¬-from P (x ∷ xs) (¬Px ∷ ¬Pxs) = λ { (here Px) → ¬Px Px ; (there Pxs) → (¬Any≃All¬-from P xs ¬Pxs) Pxs }

¬Any≃All¬-from∘to : ∀ {A : Set} (P : A → Set) (xs : List A) (Z : (¬_ ∘´ Any P) xs)
  → ¬Any≃All¬-from P xs (¬Any≃All¬-to P xs Z) ≡ Z

¬Any≃All¬-from∘to P []       _       = extensionality (λ ())
¬Any≃All¬-from∘to P (x ∷ xs) ¬AnyPxs = extensionality λ { (here Px) → refl ; (there Pxs) → ⊥-elim (¬AnyPxs (there Pxs)) }

¬Any≃All¬-to∘from : ∀ {A : Set} (P : A → Set) (xs : List A) (Z : All (¬_ ∘´ P) xs)
  → ¬Any≃All¬-to P xs (¬Any≃All¬-from P xs Z) ≡ Z

¬Any≃All¬-to∘from P []      []            = refl
¬Any≃All¬-to∘from P (x ∷ xs) (¬Px ∷ ¬Pxs) = cong (¬Px ∷_) (¬Any≃All¬-to∘from P xs ¬Pxs) -- cong (_∷_ ¬Px) (¬Any≃All¬-to∘from P xs ¬Pxs)

¬Any≃All¬ : ∀ {A : Set} (P : A → Set) (xs : List A) →
  (¬_ ∘´ Any P) xs ≃ All (¬_ ∘´ P) xs
¬Any≃All¬ P xs =
  record
  { to      = ¬Any≃All¬-to P xs
  ; from    = ¬Any≃All¬-from P xs
  ; from∘to = ¬Any≃All¬-from∘to P xs
  ; to∘from = ¬Any≃All¬-to∘from P xs
  }

postulate
  ¬All≃Any¬ : ∀ {A : Set} (P : A → Set) (xs : List A)
    → (¬_ ∘´ All P) xs ≃ Any (¬_ ∘´ P) xs
-- doesn't seen right to me...

all : ∀ {A : Set} (P : A → Bool) → List A → Bool
all P = foldr _∧_ true ∘ (map P)

Decidable : ∀ {A : Set} → (A → Set) → Set
Decidable {A} P  =  ∀ (x : A) → Dec (P x)

All? : ∀ {A : Set} {P : A → Set} → Decidable P → Decidable (All P)
All? P? []                                 =  yes []
All? P? (x ∷ xs) with P? x   | All? P? xs
...                 | yes Px | yes Pxs     =  yes (Px ∷ Pxs)
...                 | no ¬Px | _           =  no λ{ (Px ∷ Pxs) → ¬Px Px   }
...                 | _      | no ¬Pxs     =  no λ{ (Px ∷ Pxs) → ¬Pxs Pxs }

any : ∀ {A : Set} (P : A → Bool) → List A → Bool
any P = foldr _∨_ false ∘ (map P)

Any? : ∀ {A : Set} {P : A → Set} → Decidable P → Decidable (Any P)
Any? P? [] = no λ()
Any? P? (x ∷ xs) with P? x   | Any? P? xs
...                 | yes Px | _            = yes (here Px)
...                 | _      | yes Pxs      = yes (there Pxs)
...                 | no ¬Px | no ¬Pxs      = no λ { (here Px) → ¬Px Px ; (there Pxs) → ¬Pxs Pxs }


All-∀-to : ∀ {A : Set} (P : A → Set) (xs : List A) →
  All P xs → ∀ {x} → x ∈ xs → P x

All-∀-to P []        []         = λ()
All-∀-to P (y ∷ ys)  (Py ∷ Pys) = λ { (here refl) → Py ; (there ys≡) → All-∀-to P ys Pys ys≡}

All-∀-from : ∀ {A : Set} (P : A → Set) (xs : List A) →
  (∀ {x} → x ∈ xs → P x) → All P xs

All-∀-from P []       _    = []
All-∀-from P (x ∷ xs) F    = F (here refl) ∷ All-∀-from P xs (λ z → F (there z))

All-∀-from-to : ∀ {A : Set} (P : A → Set) (xs : List A) (AllPxs : All P xs) →
  All-∀-from P xs (All-∀-to P xs AllPxs) ≡ AllPxs

All-∀-from-to P []       []         = refl
All-∀-from-to P (x ∷ xs) (Px ∷ Pxs) = cong (Px ∷_) (All-∀-from-to P xs Pxs)

-- <Stolen from Maurício>
cong-app2 : ∀ {A : Set} {B : A → Set} {C : A → Set} {f g : {x : A} → B x → C x}
            -- Agda tries to eagerly compute the value for the implicit argument
            -- for f. (λ {x} → f {x}) means "keep {x} as a variable". This will
            -- appear below.
  → (λ {x} → f {x}) ≡ (λ {x} → g {x})
  -------------------------------------
  → ∀ {x} (y : B x) → (f {x} y ≡ g {x} y)
cong-app2 refl x = refl

postulate
  extensionality2 : ∀ {A : Set} {B : A → Set} {C : A → Set} {f g : {x : A} → B x → C x}
    → (∀ {x : A} (bx : B x) → f {x} bx ≡ g {x} bx)
    --------------------------------------------
    → (λ {x} → f {x}) ≡ (λ {x} → g {x})
-- </Stolen from Maurício>

All-∀-to-from : ∀ {A : Set} (P : A → Set) (xs : List A) (Pxs : ∀ {x} → x ∈ xs → P x) →
  (λ {x} → All-∀-to P xs (All-∀-from P xs Pxs) {x}) ≡ (λ {x} → Pxs {x})

All-∀-to-from P []       Pxs = extensionality2 λ()
All-∀-to-from P (x ∷ xs) Pxs = extensionality2 λ { (here refl) → refl ; (there ys≡) → cong-app2 (All-∀-to-from P xs (λ x∈xs → Pxs (there x∈xs))) ys≡ }

All-∀ : ∀ {A : Set} (P : A → Set) (xs : List A) →
  All P xs ≃ ∀ {x} → x ∈ xs → P x

All-∀ P xs =
  record
  { to      = All-∀-to P xs
  ; from    = All-∀-from P xs
  ; from∘to = All-∀-from-to P xs
  ; to∘from = All-∀-to-from P xs
  }

Any-∃-to : ∀ {A : Set} (P : A → Set) (xs : List A)
  → Any P xs → ∃[ x ] (x ∈ xs × (P x))
Any-∃-to P []       ()
Any-∃-to P (x ∷ xs) (here Px)      = ⟨ x , ⟨ here refl , Px ⟩ ⟩
Any-∃-to P (x ∷ xs) (there AnyPxs) with Any-∃-to P xs AnyPxs
... | y = ⟨ proj₁ y , ⟨ there ((proj₁ ∘ proj₂) y)  , (proj₂ ∘ proj₂) y ⟩ ⟩

Any-∃-from : ∀ {A : Set} (P : A → Set) (xs : List A)
  → ∃[ x ] (x ∈ xs × (P x)) → Any P xs
Any-∃-from P [] ⟨ _ , ⟨ () , _ ⟩ ⟩
Any-∃-from P (x ∷ xs) ⟨ y , ⟨ here refl  , Py ⟩ ⟩ = here Py
Any-∃-from P (x ∷ xs) ⟨ y , ⟨ there y∈xs , Py ⟩ ⟩ = there (Any-∃-from P xs ⟨ y , ⟨ y∈xs , Py ⟩ ⟩)

Any-∃-from-to : ∀ {A : Set} (P : A → Set) (xs : List A) (AnyPxs : Any P xs) →
  Any-∃-from P xs (Any-∃-to P xs AnyPxs) ≡ AnyPxs
Any-∃-from-to P [] ()
Any-∃-from-to P (x ∷ xs) (here Px)      = refl
Any-∃-from-to P (x ∷ xs) (there AnyPxs) with Any-∃-from-to P xs AnyPxs
... | IH = cong there IH

Any-∃-to-from : ∀ {A : Set} (P : A → Set) (xs : List A) (∃x : ∃[ x ] (x ∈ xs × (P x))) →
  Any-∃-to P xs (Any-∃-from P xs ∃x) ≡ ∃x
Any-∃-to-from P []       ⟨ y , ⟨ () , Py ⟩ ⟩
Any-∃-to-from P (x ∷ xs) ⟨ y , ⟨ here refl , Py ⟩ ⟩  = refl
Any-∃-to-from P (x ∷ xs) ⟨ y , ⟨ there y∈xs , Py ⟩ ⟩  with Any-∃-to-from P xs ⟨ y , ⟨ y∈xs , Py ⟩ ⟩
... | IH = cong (λ z → ⟨ proj₁ z , ⟨ there (proj₁ (proj₂ z)) , (proj₂ (proj₂ z)) ⟩ ⟩) IH

Any-∃ : ∀ {A : Set} (P : A → Set) (xs : List A)
  → Any P xs ≃ ∃[ x ] (x ∈ xs × (P x))
Any-∃ P xs =
  record
  { to      = Any-∃-to P xs
  ; from    = Any-∃-from P xs
  ; from∘to = Any-∃-from-to P xs
  ; to∘from = Any-∃-to-from P xs
  }

filter? : ∀ {A : Set} {P : A → Set} → (P? : Decidable P) → List A
  → ∃[ ys ] (All P ys)
filter? P? []       = ⟨ [] , [] ⟩
filter? P? (x ∷ xs) with P? x | filter? P? xs
...                  | yes Px | ⟨ ys , Pys ⟩ = ⟨ x ∷ ys , Px ∷ Pys  ⟩
...                  | no  _  | ⟨ ys , Pys ⟩ = ⟨ ys , Pys ⟩



