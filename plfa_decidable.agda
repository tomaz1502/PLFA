-- 𝕋𝕠𝕞𝕒𝕫 𝔾𝕠𝕞𝕖𝕤 𝕄𝕒𝕤𝕔𝕒𝕣𝕖𝕟𝕙𝕒𝕤


module plfa_decidable where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning
open import plfa_naturals using (ℕ; zero; suc; _∸_)
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩)
open import Data.Empty using (⊥; ⊥-elim)
open import plfa_negation using (¬_; ¬¬-intro; contraposition)
open import plfa_connectives using (_⊎_; inj₁; inj₂;
                                    ⊤; tt)
open import plfa_relations using (_≤_; z≤n; s≤s;
                                  _<_; z<s; s<s)
open import plfa_isomorphism using (_⇔_; _∘_)

data Bool : Set where
  true  : Bool
  false : Bool

infix 4 _≤ᵇ_

_≤ᵇ_ : ℕ → ℕ → Bool
zero  ≤ᵇ n     = true
suc m ≤ᵇ zero  = false
suc m ≤ᵇ suc n = m ≤ᵇ n

T : Bool → Set
T true  = ⊤
T false = ⊥

T→≡ : ∀ (b : Bool) → T b → b ≡ true
T→≡ true tt   =  refl
T→≡ false ()

≡→T : ∀ {b : Bool} → b ≡ true → T b
≡→T refl  =  tt

≤ᵇ→≤ : ∀ (m n : ℕ) → T (m ≤ᵇ n) → m ≤ n
≤ᵇ→≤ zero     n   tt = z≤n
≤ᵇ→≤ (suc m) zero ()
≤ᵇ→≤ (suc m) (suc n) t = s≤s (≤ᵇ→≤ m n t)

≤→≤ᵇ : ∀ {m n : ℕ} → m ≤ n → T (m ≤ᵇ n)
≤→≤ᵇ z≤n       = tt
≤→≤ᵇ (s≤s m≤n) = ≤→≤ᵇ m≤n

data Dec (A : Set) : Set where
  yes :   A → Dec A
  no  : ¬ A → Dec A

¬s≤z : ∀ {m : ℕ} → ¬ (suc m ≤ zero)
¬s≤z ()

¬s≤s : ∀ {m n : ℕ} → ¬ (m ≤ n) → ¬ (suc m ≤ suc n)
¬s≤s ¬m≤n (s≤s m≤n) = ¬m≤n m≤n

_≤?_ : ∀ (m n : ℕ) → Dec (m ≤ n)
zero  ≤? n                   =  yes z≤n
suc m ≤? zero                =  no ¬s≤z
suc m ≤? suc n with m ≤? n
...               | yes m≤n  =  yes (s≤s m≤n)
...               | no ¬m≤n  =  no  (¬s≤s ¬m≤n)

¬n<z : ∀ {n : ℕ} → ¬ (n < zero)
¬n<z ()

¬s<s : ∀ {m n : ℕ} → ¬ (m < n) → ¬ (suc m < suc n)
¬s<s ¬m<n (s<s m<n) = ¬m<n m<n

_<?_ : ∀ (m n : ℕ) → Dec (m < n)
zero <? zero = no ¬n<z
zero <? suc m = yes z<s
suc n <? zero = no ¬n<z
suc n <? suc m with n <? m
...             | yes n<m  = yes (s<s n<m)
...             | no  ¬n<m = no (¬s<s ¬n<m)

¬z≡sn : ∀ {n : ℕ} → ¬ (zero ≡ suc n)
¬z≡sn ()

¬sn≡z : ∀ {n : ℕ} → ¬ (suc n ≡ zero)
¬sn≡z ()

pred-≡ : ∀ {m n : ℕ} → suc m ≡ suc n → m ≡ n
pred-≡ = Eq.cong (_∸ 1)

¬n≡m→¬sn≡sm : ∀ {n m : ℕ} → (¬ (n ≡ m)) → (¬ ((suc n) ≡ (suc m)))
¬n≡m→¬sn≡sm n≢m = λ { sn≡sm  → n≢m ((pred-≡ sn≡sm))}

_≡ℕ?_ : ∀ (m n : ℕ) → Dec (m ≡ n)
zero ≡ℕ? zero = yes refl
zero ≡ℕ? suc n = no ¬z≡sn
suc m ≡ℕ? zero = no ¬sn≡z
suc m ≡ℕ? suc n with m ≡ℕ? n
...              | yes n≡m = yes (Eq.cong suc n≡m)
...              | no  n≢m = no (¬n≡m→¬sn≡sm n≢m)

_≤?′_ : ∀ (m n : ℕ) → Dec (m ≤ n)
m ≤?′ n with m ≤ᵇ n | ≤ᵇ→≤ m n | ≤→≤ᵇ {m} {n}
...        | true   | p        | _            = yes (p tt)
...        | false  | _        | ¬p           = no ¬p



⌊_⌋ : {A : Set} → Dec A → Bool
⌊ yes a ⌋ = true
⌊ no ¬a ⌋ = false

_≤ᵇ´_ : ℕ → ℕ → Bool
_≤ᵇ´_ m n = ⌊ m ≤? n ⌋

toWitness : ∀ {A : Set} {D : Dec A} → T ⌊ D ⌋ → A
toWitness {A} {yes x} tt  =  x
toWitness {A} {no ¬x} ()

fromWitness : ∀ {A : Set} {D : Dec A} → A → T ⌊ D ⌋
fromWitness {A} {yes x} _  =  tt
fromWitness {A} {no ¬x} x  =  ¬x x

≤ᵇ´→≤ : ∀ {m n : ℕ} → T (m ≤ᵇ´ n) → m ≤ n
≤ᵇ´→≤  =  toWitness

≤→≤ᵇ´ : ∀ {m n : ℕ} → m ≤ n → T (m ≤ᵇ´ n)
≤→≤ᵇ´  =  fromWitness

infix 6 _∧_

_∧_ : Bool → Bool → Bool
true ∧ true = true
false ∧ _   = false
_   ∧ false = false

infixr 6 _×-dec_

_×-dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A × B)
yes a ×-dec yes b = yes ⟨ a , b ⟩
no ¬a ×-dec _     = no λ{ ⟨ a , b ⟩ → ¬a a }
_     ×-dec no ¬b = no λ{ ⟨ a , b ⟩ → ¬b b }

infixr 5 _∨_

_∨_ : Bool → Bool → Bool
true  ∨ _      = true
_     ∨ true   = true
false ∨ false  = false

infixr 5 _⊎-dec_

_⊎-dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A ⊎ B)

yes a ⊎-dec _     = yes (inj₁ a)
_     ⊎-dec yes b = yes (inj₂ b)
no ¬a ⊎-dec no ¬b = no λ{ (inj₁ a) → ¬a a ; (inj₂ b) → ¬b b }

not : Bool → Bool
not true  = false
not false = true

¬? : ∀ {A : Set} → Dec A → Dec (¬ A)
¬? (yes a) = no (¬¬-intro a)
¬? (no ¬a) = yes ¬a

_⊃_ : Bool → Bool → Bool
_     ⊃ true     = true
false ⊃ _    = true
true  ⊃ false = false

_→-dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A → B)
_     →-dec yes b = yes λ { _ → b }
no ¬a →-dec no ¬b = yes λ{ a → ⊥-elim (¬a a) }
yes a →-dec no ¬b = no λ { a→b → ¬b (a→b a) }

∧-× : ∀ {A B : Set} (x : Dec A) (y : Dec B) → ⌊ x ⌋ ∧ ⌊ y ⌋ ≡ ⌊ x ×-dec y ⌋
∧-× (yes a) (yes b) = refl
∧-× (no ¬a) _       = refl
∧-× (yes a) (no ¬b) = refl

∨-⊎ : ∀ {A B : Set} (x : Dec A) (y : Dec B) → ⌊ x ⌋ ∨ ⌊ y ⌋ ≡ ⌊ x ⊎-dec y ⌋
∨-⊎ (yes a) _       = refl
∨-⊎ (no ¬a) (yes b) = refl
∨-⊎ (no ¬a) (no ¬b) = refl

not-¬ : ∀ {A : Set} (x : Dec A) → not ⌊ x ⌋ ≡ ⌊ ¬? x ⌋
not-¬ (yes a) = refl
not-¬ (no ¬a) = refl

_iff_ : Bool → Bool → Bool
true  iff true  = true
false iff true  = false
true  iff false = false
false iff false = true

_⇔-dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A ⇔ B)
yes a ⇔-dec yes b = yes record { to = λ{ _ → b} ; from  = λ{ _ → a} }
yes a ⇔-dec no ¬b = no λ{ a⇔b → ¬b (_⇔_.to a⇔b a)}
no ¬a ⇔-dec yes b = no λ{ a⇔b → ¬a (_⇔_.from a⇔b b)}
no ¬a ⇔-dec no ¬b = yes record { to = λ { a → ⊥-elim (¬a a) } ; from = λ { b → ⊥-elim (¬b b) } }

iff-⇔ : ∀ {A B : Set} (x : Dec A) (y : Dec B) → ⌊ x ⌋ iff ⌊ y ⌋ ≡ ⌊ x ⇔-dec y ⌋
iff-⇔ (yes a) (yes b) = refl
iff-⇔ (yes a) (no ¬b) = refl
iff-⇔ (no ¬a) (yes b) = refl
iff-⇔ (no ¬a) (no ¬b) = refl
