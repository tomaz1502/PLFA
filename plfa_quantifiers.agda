module plfa_quantifiers where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; trans; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import plfa_naturals using (ℕ; zero; suc; _+_; _*_;
                                 To; From; x0_; x1_; nil; Bin)
open import plfa_negation using (¬_)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import plfa_connectives using (_⊎_; inj₁; inj₂)
open import plfa_isomorphism using (_≃_; extensionality)
open import plfa_induction using (Bin-Law2; +-assoc; +-comm; +-identity; +-suc)
open import plfa_relations using (_≤_; s≤s; z≤n;
                                  even; odd; e-zero; e-suc; o-suc;
                                  One; prim; ox0; ox1;
                                  Can; one; can-predicate; can-to; ≤-refl)
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
  (∃[ x ] B x) ≃ ((B aa) ⊎ ((B bb) ⊎ (B cc)))

_≃_.to ∃-⊎      = λ{⟨ aa , Baa ⟩ → inj₁ Baa; ⟨ bb , Bbb ⟩ → (inj₂ (inj₁ Bbb)); ⟨ cc , Bcc ⟩ → (inj₂ (inj₂ Bcc))}
_≃_.from ∃-⊎    = λ{ (inj₁ Baa) → ⟨ aa , Baa ⟩ ; (inj₂ (inj₁ Bbb)) → ⟨ bb , Bbb ⟩ ; (inj₂ (inj₂ Bcc)) → ⟨ cc , Bcc ⟩}
_≃_.from∘to ∃-⊎ = λ{⟨ aa , Baa ⟩ → refl ; ⟨ bb , Bbb ⟩ → refl ; ⟨ cc , Bcc ⟩ → refl} 
_≃_.to∘from ∃-⊎ = λ{(inj₁ Baa) → refl ; (inj₂ (inj₁ Bbb)) → refl ; (inj₂ (inj₂ Bcc)) → refl}

even-∃ : ∀ {n : ℕ}
  → even n
  -----------
  → ∃[ x ] (x * 2 ≡ n)

odd-∃ : ∀ {n : ℕ}
  → odd n
  -----------
  → ∃[ x ] (1 + x * 2 ≡ n)


even-∃ e-zero = ⟨ zero , refl ⟩
even-∃ (e-suc oddn) with odd-∃ oddn
...                  | ⟨ m , refl ⟩ = ⟨ suc m , refl ⟩

odd-∃ (o-suc evn) with even-∃ evn
...                | ⟨ m , refl ⟩ = ⟨ m , refl ⟩

∃-even : ∀ {n : ℕ}
  → ∃[ m ] (m * 2 ≡ n)
  ----------------------
  → even n

∃-odd : ∀ {n : ℕ}
  → ∃[ m ] (1 + m * 2 ≡ n)
  ---------------------------
  → odd n

∃-even ⟨ zero , refl ⟩    = e-zero
∃-even ⟨ suc m , refl ⟩   = e-suc (∃-odd ⟨ m ,  refl ⟩)
∃-odd  ⟨ m , refl ⟩       = o-suc (∃-even ⟨ m , refl ⟩)

even-∃' : ∀ {n : ℕ}
  → even n
  ------------
  → ∃[ m ] (2 * m ≡ n)

odd-∃' : ∀ {n : ℕ}
  → odd n
  -------------
  → ∃[ m ] ( suc ( 2 * m ) ≡ n)

even-∃' e-zero            = ⟨ zero , refl ⟩
even-∃' (e-suc x) with odd-∃' x
...                | ⟨ m , refl ⟩ = ⟨ suc m , cong suc (+-suc m (m + 0)) ⟩
odd-∃' (o-suc x)  with even-∃' x
...                | ⟨ m , refl ⟩ = ⟨ m , refl ⟩

-- ∃-even' : ∀ {n : ℕ}
--   → ∃[ m ] (2 * m ≡ n)
--   ----------------------
--   → even n

-- ∃-odd' : ∀ {n : ℕ}
--   → ∃[ m ] (2 * m + 1 ≡ n)
--   --------------------------
--   → odd n

-- suc-lemma : ∀ (n : ℕ) → n + 1 ≡ suc n
-- suc-lemma zero = refl
-- suc-lemma (suc n) = cong suc (suc-lemma n)

-- ∃-even' ⟨ zero , refl ⟩ = e-zero
-- ∃-even' ⟨ suc m , refl ⟩ rewrite +-identity m | +-suc m m = e-suc (∃-odd' ⟨ m , {!(suc-lemma (m + (m + zero)))!} ⟩)
-- ∃-odd'  ⟨ m , refl ⟩ = {!!}

≤-+-∃ : ∀ (y z : ℕ)
  → y ≤ z
  --------
  → ∃[ x ] (y + x ≡ z)

≤-+-∃ y z z≤n       = ⟨ z , refl ⟩
≤-+-∃ (suc y) (suc z) (s≤s y≤z) with (≤-+-∃ y z y≤z)
...                              | ⟨ m , refl ⟩ = ⟨ m , refl ⟩

∃-+-≤ : ∀ (y z : ℕ)
  → ∃[ x ] (y + x ≡ z)
  ------
  → y ≤ z

∃-+-≤ zero _ ⟨ _ ,  refl ⟩ = z≤n
∃-+-≤ (suc y) z ⟨ x , refl ⟩ = s≤s (∃-+-≤ y (y + x) ⟨ x , refl ⟩)

¬∃≃∀¬ : ∀ {A : Set} {B : A → Set}
  → (¬ ∃[ x ] B x) ≃ ∀ x → ¬ B x
¬∃≃∀¬ =
  record
  { to      = λ {¬∃xBx x Bx → ¬∃xBx ⟨ x , Bx ⟩}
  ; from    = λ{x¬Bx ⟨ x , Bx ⟩ → x¬Bx x Bx}
  ; from∘to = λ{ ¬∃xBx → extensionality λ{ ⟨ x , y ⟩ → refl}} 
  ; to∘from = λ {x¬Bx → refl}
  }

∃¬-implies-¬∀ : ∀ {A : Set} {B : A → Set}
  → ∃[ x ] (¬ B x)
  -------------------
  → ¬ (∀ x → B x)

∃¬-implies-¬∀ ⟨ x , ¬Bx ⟩ = λ { x→Bx → ¬Bx (x→Bx x) }

-- the converse does not hold. The assumption that ¬ (∀ x → B x) tells us nothing about what x isn't a valid argument for B. To construct an object
-- of type ∃[ x ] (¬ B x) we must say explicitly which x makes B x false. This fact is equivalent to ¬ (A × B) isn't the same as (¬ A ⊎ ¬ B).

ℕ-iso-∃xCanx :  ℕ ≃ (∃[ x ] (Can x))

_≃_.to      ℕ-iso-∃xCanx = λ { n → ⟨ To n , can-to n ⟩}
_≃_.from    ℕ-iso-∃xCanx = λ{⟨ x , canx ⟩ → From x}
_≃_.from∘to ℕ-iso-∃xCanx = λ {n → Bin-Law2 n}
_≃_.to∘from ℕ-iso-∃xCanx = λ {⟨ x , canx ⟩ → {!can-predicate x canx!}  }

