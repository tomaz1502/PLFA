module plfa_quantifiers where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; trans)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import plfa_naturals using (ℕ; zero; suc; _+_; _*_;
                                 To; From; x0_; x1_; nil; Bin)
open import plfa_negation using (¬_)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import plfa_connectives using (_⊎_; inj₁; inj₂)
open import plfa_isomorphism using (_≃_; extensionality)
open import plfa_induction using (Bin-Law2; +-assoc; +-comm)
open import plfa_relations using (_≤_; s≤s; z≤n;
                                  even; odd;
                                  One; prim; ox0; ox1;
                                  Can; one; can-predicate; can-to)
open import Function using (_∘_)


∀-distrib-× : ∀ {A : Set} {B C : A → Set} →
  (∀ (x : A) → B x × C x) ≃ (∀ (x : A) → B x) × (∀ (x : A) → C x)

∀-distrib-× =
  record
  { to       = λ { x→BxCx →  ⟨ proj₁ ∘ x→BxCx , proj₂ ∘ x→BxCx ⟩ }
  ; from     = λ { ⟨ x→Bx , x→Cx ⟩ → λ {x → ⟨ x→Bx x , x→Cx x ⟩}  }
  ; from∘to  = λ {f → refl}
  ; to∘from  = λ {⟨ f , g ⟩ → refl}
  }

⊎∀-implies-∀⊎ : ∀ {A : Set} {B C : A → Set} →
  ((∀ (x : A) → B x) ⊎ (∀ (x : A) → C x))  →  (∀ (x : A) → B x ⊎ C x)

⊎∀-implies-∀⊎ (inj₁ A→B) = λ {x → inj₁ (A→B x)}
⊎∀-implies-∀⊎ (inj₂ A→C) = λ {x → inj₂ (A→C x)}

-- the converse is false. to have an object of type (A→B)⊎(A→C) we must say which one we have. The function A→B⊎C doesn't specify which one it will gives us

data Tri : Set where
  aa : Tri
  bb : Tri
  cc : Tri

∀-iso-× : ∀ {B : Tri → Set} → (∀ (x : Tri) → B x) ≃ ((B aa) × (B bb) × (B cc))
∀-iso-× =
  record
  { to      = λ {f → ⟨ f aa , ⟨ f bb , f cc ⟩ ⟩}
  ; from    = λ { ⟨ Baa , ⟨ Bbb , Bcc ⟩ ⟩ → λ {aa → Baa ; bb → Bbb ; cc → Bcc} }
  ; from∘to = λ {f → extensionality λ {aa → refl ; bb → refl ; cc → refl}}
  ; to∘from = λ {⟨ Baa , ⟨ Bbb , Bcc ⟩ ⟩ → refl}
  }

data Σ (A : Set) (B : A → Set) : Set where
  ⟨_,_⟩ : (x : A) → B x → Σ A B

Σ-syntax = Σ
infix 2 Σ-syntax
syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B

∃ : ∀ {A : Set} (B : A → Set) → Set
∃ {A} B = Σ A B

∃-syntax = ∃
syntax ∃-syntax (λ x → B) = ∃[ x ] B

∃-elim : ∀ {A : Set} {B : A → Set} {C : Set}
 → (∀ x → B x → C)
 → ∃[ x ] B x
 -------------------
 → C

∃-elim f ⟨ x , y ⟩ = f x y

∃∀-currying : ∀ {A : Set} {B : A → Set} {C : Set}
  → (∀ x → B x → C) ≃ (∃[ x ] B x → C)

∃∀-currying =
  record
  { to      = ∃-elim
  ; from    = λ {g → λ {a → λ {Ba → g ⟨ a , Ba ⟩}}}
  ; from∘to = λ {f → refl}
  ; to∘from = λ {g → extensionality λ {⟨ x , y ⟩ → refl}}
  }

∃-distrib-⊎ : ∀ {A : Set} {B C : A → Set} →
  ∃[ x ] (B x ⊎ C x) ≃ ((∃[ x ] B x) ⊎ (∃[ x ] C x))

∃-distrib-⊎ =
  record
  { to      = λ { ⟨ x , inj₁ Bx ⟩ → inj₁ ⟨ x , Bx ⟩ ; ⟨ x , inj₂ Cx ⟩ → inj₂ ⟨ x , Cx ⟩ }
  ; from    = λ {(inj₁ ⟨ x , Bx ⟩) → ⟨ x , inj₁ Bx ⟩ ; (inj₂ ⟨ x , Cx ⟩) → ⟨ x , inj₂ Cx ⟩}
  ; from∘to = λ {⟨ x , inj₁ Bx ⟩ → refl ; ⟨ y , inj₂ Cy ⟩ → refl}
  ; to∘from = λ {(inj₁ ⟨ x , Bx ⟩) → refl ; (inj₂ ⟨ y , Cy ⟩ ) → refl}
  }

∃×-implies-×∃ : ∀ {A : Set} {B C : A → Set} →
  (∃[ x ] (B x × C x)) → ((∃[ x ] B x) × (∃[ x ] C x))

∃×-implies-×∃ ⟨ x , ⟨ Bx , Cx ⟩ ⟩ = ⟨ ⟨ x , Bx ⟩ , ⟨ x , Cx ⟩ ⟩

-- O converso não é valido. O x que faz B ser verdadeiro não precisa ser o mesmo que o x do C

∃-⊎ : ∀ {B : Tri → Set} →
  (∃[ x ] B x) ≃ ((B aa) ⊎ (B bb) ⊎ (B cc))

∃-⊎ = ?
