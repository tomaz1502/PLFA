module plfa.part_one.Negation where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong)
open Eq.≡-Reasoning
open import plfa.part_one.Naturals using (ℕ; zero; suc; _∸_)
open import plfa.part_one.Relations using (_<_; z<s; s<s; _>_)
open import Data.Empty using (⊥; ⊥-elim)
open import plfa.part_one.Connectives using (_×_; ⟨_,_⟩; proj₁; proj₂; _⊎_; inj₁; inj₂; →-distrib-⊎)
open import Function using (_∘_)
open import plfa.part_one.Isomorphism using (_≃_; extensionality; ≃-refl; _≲_)
open plfa.part_one.Isomorphism.≃-Reasoning

¬_ : Set → Set
¬ A = A → ⊥

¬-elim : ∀ {A : Set}
  → ¬ A
  → A
  --------
  → ⊥
¬-elim ¬x x = ¬x x

infix 3 ¬_

¬¬-intro : ∀ {A : Set}
  → A
  --------
  → ¬ ¬ A
¬¬-intro x = λ {¬x → ¬x x}

¬¬-intro´ : ∀ {A : Set}
  → A
  --------
  → ¬ ¬ A

¬¬-intro´ x ¬x = ¬x x

¬¬¬-elim : ∀ {A : Set}
  → ¬ ¬ ¬ A
  -----------
  → ¬ A

¬¬¬-elim ¬¬¬x = λ{x → ¬¬¬x (¬¬-intro x)} -- x has type A

contraposition : ∀ {A B : Set}
  → (A → B)
  -----------
  → (¬ B → ¬ A)

contraposition f ¬y x = ¬y (f x)

_≢_ : ∀ {A : Set} → A → A → Set
A ≢ B = ¬ (A ≡ B)

peano : ∀ {m : ℕ} → zero ≢ suc m
peano = λ ()

id : ⊥ → ⊥
id x = x

id´ : ⊥ → ⊥
id´ = λ ()

id≡id´ : id ≡ id´
id≡id´ = extensionality (λ())

assimilation : ∀ {A : Set} (¬x ¬x´ : ¬ A) → ¬x ≡ ¬x´
assimilation x ¬x´ = extensionality (λ {x → ⊥-elim (¬x´ x)} )

<-irreflexive : ∀ (n : ℕ) → ¬ (n < n)
<-irreflexive (suc n) (s<s n<n) = <-irreflexive n n<n

pred-≡ : ∀ {m n : ℕ}
  → (suc m ≡ suc n)
  -------------------
  → m ≡ n
pred-≡ s≡s = cong (_∸ 1) (s≡s)

pred-< : ∀ {m n : ℕ}
  → (suc m < suc n)
  -------------------
  → m < n

pred-< (s<s m<n) = m<n

data RealTrichotomy (m n : ℕ) : Set where
  Less :
    (m < n) × ((¬ (m ≡ n)) × (¬ (n < m)))
    ----------------------------------
    → RealTrichotomy m n

  Equal :
    (¬ m < n) × ((m ≡ n) × (¬ n < m))
    ----------------------------------
    → RealTrichotomy m n

  Greater :
    (¬ m < n) × ((¬ m ≡ n) × (n < m))
    ----------------------------------
    → RealTrichotomy m n

realtrichotomy : ∀ (m n : ℕ) → RealTrichotomy m n
realtrichotomy zero zero = Equal ⟨ (λ()) , ⟨ refl , (λ()) ⟩ ⟩
realtrichotomy zero (suc n) = Less ⟨ z<s , ⟨ (λ()) , (λ()) ⟩ ⟩
realtrichotomy (suc m) zero = Greater ⟨ (λ()) , ⟨ (λ()) , z<s ⟩ ⟩
realtrichotomy (suc m) (suc n) with realtrichotomy m n
...  | Less ⟨ m<n , ⟨ ¬m≡n , ¬n<m ⟩ ⟩ = Less ⟨ (s<s (m<n)) , ⟨ ¬m≡n ∘ pred-≡ , ¬n<m ∘ pred-< ⟩ ⟩
...  | Equal ⟨ ¬m<n , ⟨ m≡n , ¬n<m ⟩ ⟩ = Equal ⟨ ¬m<n ∘ pred-< , ⟨ cong suc m≡n , ¬n<m ∘ pred-< ⟩ ⟩
...  | Greater ⟨ ¬m<n , ⟨ ¬m≡n , n<m ⟩ ⟩ = Greater ⟨ ¬m<n ∘ pred-< , ⟨ ¬m≡n ∘ pred-≡ , (s<s n<m) ⟩ ⟩


⊎-dual-× : ∀ (A B : Set) → ¬ (A ⊎ B) ≃ (¬ A) × (¬ B)
⊎-dual-× A B =
  ≃-begin
    (¬ (A ⊎ B))
  ≃⟨ ≃-refl ⟩
    ((A ⊎ B) → ⊥)
  ≃⟨ →-distrib-⊎ ⟩
    ((A → ⊥) × (B → ⊥))
  ≃⟨ ≃-refl ⟩
    ((¬ A) × (¬ B))
  ≃-∎

×-dual-⊎ : ∀ {A B : Set} → ((¬ A) ⊎ (¬ B)) → ¬ (A × B)
×-dual-⊎ = λ { (inj₁ ¬A) → λ { ⟨ A , B ⟩ → ¬A A }
             ; (inj₂ ¬B) → λ { ⟨ A , B ⟩ → ¬B B } }

postulate
  EM : ∀ {A : Set} → A ⊎ ¬ A -- Excluded Middle

EM-irrefutable : ∀ {A : Set} → ¬ ¬ (A ⊎ ¬ A)
EM-irrefutable k = k (inj₂ λ {x → k (inj₁ x)})

EM-imp-DN : ∀ {A : Set}
  → A ⊎ ¬ A
  ----------------
  → (¬ ¬ A → A)

EM-imp-DN (inj₁ A)  _   = A
EM-imp-DN (inj₂ ¬A) ¬¬A = ⊥-elim (¬-elim ¬¬A ¬A)


⊥-imp-any : ∀ {A B : Set}
  → ¬ A
  ----------------
  → (A → B)

⊥-imp-any ¬A A = ⊥-elim (¬A A)


DN-imp-PL : ∀ {A B : Set}
  → (∀ {C : Set} → ¬ ¬ C → C)
  ---------------
  → ((A → B) → A) → A

DN-imp-PL ¬¬C→C A→B→A = ¬¬C→C  λ { ¬A → ¬A (A→B→A (⊥-imp-any ¬A)) }

PL-imp-IaD : ∀ {A B : Set}
   → (∀{C D : Set} → ((C → D) → C) → C)
   -----------------------
   → ((A → B) → (¬ A ⊎ B))

PL-imp-IaD A→B→A→A A→B = A→B→A→A (λ z → inj₁ (λ x → z (inj₂ (A→B x))))


¬¬A×B-imp-¬¬A : ∀ (A B : Set)
  → (¬ (¬ (A × B)))
  -------------------
  → ¬ ¬ A

¬¬A×B-imp-¬¬A A B ¬¬A×B = λ { (¬A) → ¬¬A×B λ {⟨ A , B ⟩ → ¬A A}}

¬¬A×B-imp-¬¬B : ∀ (A B : Set)
  → (¬ (¬ (A × B)))
  -------------------
  → ¬ ¬ B

¬¬A×B-imp-¬¬B A B ¬¬A×B = λ { (¬B) → ¬¬A×B λ {⟨ A , B ⟩ → ¬B B}}

IaD-imp-DM : ∀ {A B : Set}
  → (∀ {C D : Set} → ((C → D) → (¬ C ⊎ D)))
  -------------------------
  → ¬ (¬ A × ¬ B) → A ⊎ B

IaD-imp-DM {A} {B} IaD ¬¬A×¬B with IaD λ{ a⊎b → a⊎b }
...                              | (inj₁ ¬a⊎b) = ⊥-elim (¬¬A×¬B ⟨ (¬a⊎b ∘ inj₁) , (¬a⊎b ∘ inj₂) ⟩)
...                              | (inj₂ a⊎b) = a⊎b

DM-imp-EM : ∀ {A : Set}
  → (∀ {B C : Set } → (¬ (¬ B × ¬ C) → B ⊎ C))
  ------------------------------------
  → (A ⊎ ¬ A)

DM-imp-EM {A} dm = dm λ {⟨ ¬A , ¬¬A ⟩ → ¬¬A ¬A}

Stable : Set → Set
Stable A = (¬ ¬ A → A)

¬-Stable : ∀ (A : Set) → Stable (¬ A)
¬-Stable A = ¬¬¬-elim



×-Stable : ∀ (A B : Set)
  → Stable A
  → Stable B
  -------------------
  → Stable (A × B)

×-Stable A B SA SB = λ {¬¬A×B → ⟨ SA (¬¬A×B-imp-¬¬A A B (¬¬A×B)) , SB ((¬¬A×B-imp-¬¬B A B ¬¬A×B)) ⟩}




