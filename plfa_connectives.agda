module plfa_connectives where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning
open import plfa_naturals using (ℕ)
open import plfa_isomorphism using (_∘_; _≃_; _≲_; extensionality; _⇔_)
open plfa_isomorphism.≃-Reasoning

data _×_ (A B : Set) : Set where

  ⟨_,_⟩ :
      A
    → B
    --------
    → A × B

proj₁ : ∀ {A B : Set}
  → A × B
  ---------
  → A

proj₁ ⟨ x , y ⟩ = x

proj₂ : ∀ {A B : Set}
  → A × B
  ---------
  → B

proj₂ ⟨ x , y ⟩ = y

record _×´_ (A B : Set) : Set where
  field
    proj₁´ : A
    proj₂´ : B

open _×´_

η-× : ∀ {A B : Set} (w : A × B) → ⟨ proj₁ w , proj₂ w ⟩ ≡ w
η-× ⟨ x , y ⟩ = refl

infixr 2 _×_

data Bool : Set where
  true  : Bool
  false : Bool

data Tri : Set where
  aa : Tri
  bb : Tri
  cc : Tri

×-count : Bool × Tri → ℕ
×-count ⟨ true  , aa ⟩  =  1
×-count ⟨ true  , bb ⟩  =  2
×-count ⟨ true  , cc ⟩  =  3
×-count ⟨ false , aa ⟩  =  4
×-count ⟨ false , bb ⟩  =  5
×-count ⟨ false , cc ⟩  =  6

×-comm : ∀ {A B : Set} → A × B ≃ B × A
×-comm =
  record
  { to       = λ { ⟨ x , y ⟩ → ⟨ y , x ⟩ }
  ; from     = λ { ⟨ y , x ⟩ → ⟨ x , y ⟩ }
  ; from∘to  = λ { ⟨ x , y ⟩ → refl }
  ; to∘from  = λ { ⟨ y , x ⟩ → refl }
  }

×-assoc : ∀ {A B C : Set} → A × (B × C) ≃ (A × B) × C
×-assoc =
  record
  { to       = λ { ⟨ x , ⟨ y , z ⟩ ⟩ → ⟨ ⟨ x , y ⟩ , z ⟩}
  ; from     = λ { ⟨ ⟨ x , y ⟩ , z ⟩ → ⟨ x , ⟨ y , z ⟩ ⟩}
  ; from∘to  = λ { ⟨ x , ⟨ y , z ⟩ ⟩ → refl}
  ; to∘from  = λ { ⟨ ⟨ x , y ⟩ , z ⟩ → refl}
  }

open _≃_

⇔≃× : ∀ {A B : Set} → A ⇔ B ≃ (A → B) × (B → A)
⇔≃× =
  record
  { to       = λ {A⇔B → ⟨ _⇔_.to A⇔B , _⇔_.from A⇔B ⟩ }
  ; from     = λ { ⟨ AB , BA ⟩ → record{to = AB; from = BA} }
  ; from∘to  = λ {A⇔B → refl}
  ; to∘from  = λ {⟨ AB , BA ⟩ → refl}
  }

data ⊤ : Set where
  tt :
    --
    ⊤

η-⊤ : ∀ (w : ⊤) → w ≡ tt
η-⊤ tt = refl

⊤-identity¹ : ∀ {A : Set} → ⊤ × A ≃ A
⊤-identity¹ =
  record
  { to      = λ { ⟨ tt , A ⟩ → A }
  ; from    = λ { A → ⟨ tt , A ⟩ }
  ; from∘to = λ { ⟨ tt , A ⟩ → refl }
  ; to∘from = λ { A → refl }
  }

⊤-identity² : ∀ {A : Set} → A × ⊤ ≃ A
⊤-identity² {A} =
  ≃-begin
    (A × ⊤)
  ≃⟨ ×-comm ⟩
    (⊤ × A)
  ≃⟨ ⊤-identity¹ ⟩
    A
  ≃-∎

data _⊎_ (A B : Set) : Set where

  inj₁ :
    A
    -------
    → A ⊎ B

  inj₂ :
    B
    -------
    → A ⊎ B

case-⊎ : ∀ {A B C : Set}
  → (A → C)
  → (B → C)
  → A ⊎ B
  -----------
  → C
case-⊎ f g (inj₁ x) = f x
case-⊎ f g (inj₂ y) = g y

η-⊎ : ∀ {A B : Set} (w : A ⊎ B) → case-⊎ inj₁ inj₂ w ≡ w
η-⊎ (inj₁ x) = refl
η-⊎ (inj₂ y) = refl

uniq-⊎ : ∀ {A B C : Set} (h : A ⊎ B → C) (w : A ⊎ B) →
  case-⊎ (h ∘ inj₁) (h ∘ inj₂) w ≡ h w
uniq-⊎ h (inj₁ x) = refl
uniq-⊎ h (inj₂ y) = refl

infix 1 _⊎_

⊎-count : Bool ⊎ Tri → ℕ
⊎-count (inj₁ true)   =  1
⊎-count (inj₁ false)  =  2
⊎-count (inj₂ aa)     =  3
⊎-count (inj₂ bb)     =  4
⊎-count (inj₂ cc)     =  5

⊎-comm : ∀ {A B : Set} → A ⊎ B ≃ B ⊎ A
⊎-comm =
  record
  { to      = λ {(inj₁ A) → inj₂ A; (inj₂ B) → inj₁ B }
  ; from    = λ {(inj₁ B) → inj₂ B; (inj₂ A) → inj₁ A}
  ; from∘to = λ {(inj₁ A) → refl; (inj₂ B) → refl}
  ; to∘from = λ {(inj₁ B) → refl; (inj₂ A) → refl}
  }

⊎-assoc : ∀ {A B C : Set} → A ⊎ (B ⊎ C) ≃ (A ⊎ B) ⊎ C
⊎-assoc =
  record
  { to      = λ {(inj₁ A) → (inj₁ (inj₁ A)); (inj₂ (inj₁ B)) → (inj₁ (inj₂ B)); (inj₂ (inj₂ C)) → inj₂ C }
  ; from    = λ {(inj₁ (inj₁ A)) → inj₁ A; (inj₁ (inj₂ B)) → (inj₂ (inj₁ B)); (inj₂ C) → (inj₂ (inj₂ C))}
  ; from∘to = λ {(inj₁ A) → refl; (inj₂ (inj₁ B)) → refl; (inj₂ (inj₂ C)) → refl}
  ; to∘from = λ {(inj₁ (inj₁ A)) → refl; (inj₁ (inj₂ B)) → refl; (inj₂ C) → refl}
  }

data ⊥ : Set where
  -- empty

⊥-elim : {A : Set}
  → ⊥
  ------
  → A

⊥-elim ()

uniq-⊥ : ∀ {C : Set} (h : ⊥ → C) (w : ⊥) → ⊥-elim w ≡ w
uniq-⊥ h ()

⊥-identity¹ : ∀ {A : Set} → A ⊎ ⊥ ≃ A
⊥-identity¹ =
  record
  { to      = λ { (inj₁ A) → A; (inj₂ ()) }
  ; from    = λ {A → (inj₁ A)}
  ; from∘to = λ {(inj₁ A) → refl; (inj₂ ())}
  ; to∘from = λ {A → refl}
  }

⊥-identity² : ∀ {A : Set} → ⊥ ⊎ A ≃ A
⊥-identity² =
  record
    { to      = λ { (inj₂ A) → A; (inj₁ ()) }
    ; from    = λ {A → (inj₂ A)}
    ; from∘to = λ {(inj₂ A) → refl; (inj₁ ())}
    ; to∘from = λ {A → refl}
    }

--modus ponens
→-elim : ∀ {A B : Set}
  → (A → B)
  → A
  -------
  → B
→-elim L M = L M

η-→ : ∀ {A B : Set} (f : A → B) → (λ (x : A) → f x) ≡ f
η-→ f = refl

currying : ∀ {A B C : Set} → (A → B → C) ≃ (A × B → C)
currying =
  record
    { to      = λ {f → (λ {⟨ x , y ⟩ → f x y})}
    ; from    = λ {g → λ {x → λ{y → g ⟨ x , y ⟩}}}
    ; from∘to = λ {f → refl}
    ; to∘from = λ {g → extensionality λ { ⟨ x , y ⟩ → refl }}
    }

→-distrib-⊎ : ∀ {A B C : Set} → ((A ⊎ B) → C) ≃ ((A → C) × (B → C))
→-distrib-⊎ =
  record
  { to      = λ {f → ⟨ f ∘ inj₁ , f ∘ inj₂ ⟩ }
  ; from    = λ {⟨ g , h ⟩ → λ{(inj₁ x) → g x; (inj₂ y) → h y} }
  ; from∘to = λ {f → extensionality λ {(inj₁ x) → refl; (inj₂ y) → refl}}
  ; to∘from = λ {⟨ g , h ⟩ → refl}
  }

→-distrib-× : ∀ {A B C : Set} → (A → B × C) ≃ ((A → B) × (A → C))
→-distrib-× =
  record
  { to      = λ {f → ⟨ proj₁ ∘ f , proj₂ ∘ f ⟩ }
  ; from    = λ {⟨ g , h ⟩ → λ{x → ⟨ g x , h x ⟩ } }
  ; from∘to = λ {f → extensionality λ{x → η-× (f x) } }
  ; to∘from = λ {⟨ g , h ⟩ → refl}
  }

×-distrib-⊎ : ∀ {A B C : Set} → (A ⊎ B) × C ≃ (A × C) ⊎ (B × C)
×-distrib-⊎ =
  record
  { to      = λ{ ⟨ inj₁ x , z ⟩ → (inj₁ ⟨ x , z ⟩)
  ; ⟨ inj₂ y , z ⟩ → (inj₂ ⟨ y , z ⟩)
  }
  ; from    = λ{ (inj₁ ⟨ x , z ⟩) → ⟨ inj₁ x , z ⟩
  ; (inj₂ ⟨ y , z ⟩) → ⟨ inj₂ y , z ⟩
  }
  ; from∘to = λ{ ⟨ inj₁ x , z ⟩ → refl
  ; ⟨ inj₂ y , z ⟩ → refl
  }
  ; to∘from = λ{ (inj₁ ⟨ x , z ⟩) → refl
  ; (inj₂ ⟨ y , z ⟩) → refl
  }
  }

⊎-distrib-× : ∀ {A B C : Set} → (A × B) ⊎ C ≲ (A ⊎ C) × (B ⊎ C)
⊎-distrib-× =
  record
  { to      = λ{ (inj₁ ⟨ x , y ⟩) → ⟨ inj₁ x , inj₁ y ⟩
  ; (inj₂ z)         → ⟨ inj₂ z , inj₂ z ⟩
  }
  ; from    = λ{ ⟨ inj₁ x , inj₁ y ⟩ → (inj₁ ⟨ x , y ⟩)
  ; ⟨ inj₁ x , inj₂ z ⟩ → (inj₂ z)
  ; ⟨ inj₂ z , _      ⟩ → (inj₂ z)
  }
  ; from∘to = λ{ (inj₁ ⟨ x , y ⟩) → refl
  ; (inj₂ z)         → refl
  }
  }

⊎-weak-× : ∀ {A B C : Set} → (A ⊎ B) × C → A ⊎ (B × C)
⊎-weak-× ⟨ inj₁ x , z ⟩ = inj₁ x
⊎-weak-× ⟨ inj₂ x , z ⟩ = inj₂ ⟨ x , z ⟩

-- ⊎-another-× : ∀ {A B C : Set} → A ⊎ (B × C) → (A ⊎ B) × C
-- ⊎-another-×

⊎×-implies-×⊎ : ∀ {A B C D : Set} → (A × B) ⊎ (C × D) → (A ⊎ C) × (B ⊎ D)
⊎×-implies-×⊎ (inj₁ A×B) = ⟨ inj₁ (proj₁ (A×B)) , inj₁ (proj₂ (A×B)) ⟩
⊎×-implies-×⊎ (inj₂ C×D) = ⟨ inj₂ (proj₁ C×D) , inj₂ (proj₂ C×D) ⟩

--the converse is false. For instance, in logic terms, one could have A ⊎ B and C ⊎ D simply by having B and C, which can't be used to construct
-- A × C or B × D.
