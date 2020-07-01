module plfa.part_two.Properties where

open import plfa.part_two.Lambda
open import plfa.part_one.Isomorphism

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; cong; cong₂)
open import Data.String using (String; _≟_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_×_; proj₁; proj₂; ∃; ∃-syntax)
                                renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Function using (_∘_)

V¬—→ : ∀ {M N} → Value M → ¬ (M —→ N)
V¬—→ V-ƛ ()
V¬—→ V-zero ()
V¬—→ (V-suc x) (ξ-suc suc—→) = V¬—→ x suc—→

—→¬V : ∀ {M N} → (M —→ N) → ¬ (Value M)
—→¬V M—→N VM = V¬—→ VM M—→N

infix 4 Canonical_∶_

data Canonical_∶_ : Term → Type → Set where

  C—ƛ : ∀ {x M T U}
    → ∅ , x ∶ T ⊢ M ∶ U
    ------------------
    → Canonical (ƛ x ⇒ M) ∶ T ⇒ U

  C—zero :
    -------------------------
    Canonical `zero ∶ `ℕ

  C—suc : ∀ {M}
    → Canonical M ∶ `ℕ
    --------------------------
    → Canonical `suc M ∶ `ℕ

canonical : ∀ {V A}
  → ∅ ⊢ V ∶ A
  → Value V
  -------------------
  → Canonical V ∶ A

canonical (⊢ƛ V∶A) V-ƛ          = C—ƛ V∶A
canonical ⊢zero V-zero          = C—zero
canonical (⊢suc V∶A) (V-suc VV) = C—suc (canonical V∶A VV)

value : ∀ {M A}
  → Canonical M ∶ A
  ----------------
  → Value M

value (C—ƛ ⊢M)   = V-ƛ
value C—zero     = V-zero
value (C—suc CM) = V-suc (value CM)

typed : ∀ {M A}
  → Canonical M ∶ A
  -------------------
  → ∅ ⊢ M ∶ A

typed (C—ƛ x∶A)   = ⊢ƛ x∶A
typed  C—zero      = ⊢zero
typed (C—suc x∶A) = ⊢suc (typed x∶A)

data Progress (M : Term) : Set where

  step : ∀ {N}
    → M —→ N
    ------------
    → Progress M

  done :
    Value M
    ------------
    → Progress M

progress : ∀ {M T}
  → ∅ ⊢ M ∶ T
  --------------
  → Progress M

progress (⊢´ ())
progress (⊢ƛ M∶T) = done V-ƛ
progress {M · N} (M∶T⇒U · N∶T) with progress M∶T⇒U | progress N∶T
... | step M—→ | _        = step (ξ-·₁ M—→)
... | done VM  | step N—→ = step (ξ-·₂ VM N—→)
... | done VM  | done VN with canonical M∶T⇒U VM
...                       | C—ƛ _ = step (β-ƛ VN)
progress ⊢zero = done V-zero
progress {`suc M} (⊢suc M∶T) with progress M∶T
... | step M—→ = step (ξ-suc M—→)
... | done VM  = done (V-suc VM)
progress (⊢case L∶ℕ M∶T₁ N∶T₂) with progress L∶ℕ
...                            | step L—→ = step (ξ-case L—→)
progress (⊢case () M∶T₁ N∶T₂)  | done V-ƛ
progress (⊢case L∶ℕ M∶T₁ N∶T₂) | done V-zero = step β-zero
progress (⊢case L∶ℕ M∶T₁ N∶T₂) | done (V-suc VL) = step (β-suc VL)
progress (⊢μ M∶T) = step β-μ


open _≃_

Progress-≃ : ∀ {M} → Progress M ≃ Value M ⊎ ∃[ N ](M —→ N)
to Progress-≃ (step {N} M—→N)       = inj₂ ⟨ N , M—→N ⟩
to Progress-≃ (done VM)             = inj₁ VM

from Progress-≃ (inj₁ VM)           = done VM
from Progress-≃ (inj₂ ⟨ N , M—→N ⟩) = step M—→N

from∘to Progress-≃ (done VM)        = refl
from∘to Progress-≃ (step M—→)       = refl

to∘from Progress-≃ (inj₁ VM)        = refl
to∘from Progress-≃ (inj₂ M—→)       = refl


progress´ : ∀ M {A} → ∅ ⊢ M ∶ A → Value M ⊎ ∃[ N ](M —→ N)
progress´ .(` _) (⊢´ ())
progress´ .(ƛ _ ⇒ _) (⊢ƛ M∶A) = inj₁ V-ƛ
progress´ (M · N) (M∶T⇒A · N∶T) with progress´ M M∶T⇒A | progress´ N N∶T
... | inj₂ ⟨ M´ , M—→M´ ⟩ | _         = inj₂ ⟨ M´ · N , ξ-·₁ M—→M´ ⟩
... | inj₁ VM             | inj₂ ⟨ N´ , N—→N´ ⟩ = inj₂ ⟨ M · N´ , ξ-·₂ VM N—→N´ ⟩
... | inj₁ VM             | inj₁ VN with canonical M∶T⇒A VM
progress´ ((ƛ x ⇒ M) · N) (M∶T⇒A · N∶T) | inj₁ VM | inj₁ VN | C—ƛ _ = inj₂ ⟨ M [ x := N ] , β-ƛ VN ⟩
progress´ .`zero ⊢zero = inj₁ V-zero
progress´ (`suc M) (⊢suc M∶A) with progress´ M M∶A
... | inj₁ VM = inj₁ (V-suc VM)
... | inj₂ ⟨ M´ , M—→M´ ⟩ = inj₂ ⟨ `suc M´ , ξ-suc M—→M´ ⟩
progress´ (case L [zero⇒ M |suc x ⇒ N ]) (⊢case L∶ℕ M∶A N∶A)        with progress´ L L∶ℕ
progress´ (case L [zero⇒ M |suc x ⇒ N ]) (⊢case L∶ℕ M∶A N∶A)        | inj₁ V-zero = inj₂ ⟨ M , β-zero ⟩
progress´ (case (`suc z) [zero⇒ M |suc x ⇒ N ]) (⊢case L∶ℕ M∶A N∶A) | inj₁ (V-suc Vz) = inj₂ ⟨ N [ x := z ] , β-suc Vz ⟩
progress´ (case L [zero⇒ M |suc x ⇒ N ]) (⊢case () M∶A N∶A)         | inj₁ V-ƛ
progress´ (case L [zero⇒ M |suc x ⇒ N ]) (⊢case L∶ℕ M∶A N∶A)        | inj₂ ⟨ L´ , L—→L´ ⟩ = inj₂ ⟨ case L´ [zero⇒ M |suc x ⇒ N ] , ξ-case L—→L´ ⟩
progress´ (μ x ⇒ M) (⊢μ M∶A) = inj₂ ⟨ M [ x := μ x ⇒ M ] , β-μ ⟩

value? : ∀ {A M} → ∅ ⊢ M ∶ A → Dec (Value M)
value? {A} {M} M∶A with progress M∶A
... | step M—→M´ = no (—→¬V M—→M´)
... | done VM    = yes VM


ext : ∀ {Γ Δ}
  → (∀ {x A}     →         Γ ∋ x ∶ A →         Δ ∋ x ∶ A)
  -----------------------------------------------------
  → (∀ {x y A B} → Γ , y ∶ B ∋ x ∶ A → Δ , y ∶ B ∋ x ∶ A)
ext Γ→Δ Z           = Z
ext Γ→Δ (S x≢y Γ∋x) = S x≢y (Γ→Δ Γ∋x)

rename : ∀ {Γ Δ}
  → (∀ {x A} → Γ ∋ x ∶ A → Δ ∋ x ∶ A)
  ----------------------------------
  → (∀ {M A} → Γ ⊢ M ∶ A → Δ ⊢ M ∶ A)
rename Γ→Δ (⊢´ ∋x) = ⊢´ (Γ→Δ ∋x)
rename Γ→Δ (⊢ƛ Γ⊢M) = ⊢ƛ (rename (ext Γ→Δ) Γ⊢M)
rename Γ→Δ (Γ⊢M · Γ⊢N) = rename Γ→Δ Γ⊢M · rename Γ→Δ Γ⊢N
rename Γ→Δ ⊢zero = ⊢zero
rename Γ→Δ (⊢suc Γ⊢M) = ⊢suc (rename Γ→Δ Γ⊢M)
rename Γ→Δ (⊢case Γ⊢L Γ⊢M Γ⊢N) = ⊢case (rename Γ→Δ Γ⊢L) (rename Γ→Δ Γ⊢M) (rename (ext Γ→Δ) Γ⊢N)
rename Γ→Δ (⊢μ Γ⊢M) = ⊢μ (rename (ext Γ→Δ) Γ⊢M)

weaken : ∀ {Γ M A}
  → ∅ ⊢ M ∶ A
  ----------
  → Γ ⊢ M ∶ A
weaken {Γ} ⊢M = rename ρ ⊢M
  where
  ρ : ∀ {z C}
    → ∅ ∋ z ∶ C
    ---------
    → Γ ∋ z ∶ C
  ρ ()

drop : ∀ {Γ x M A B C}
  → Γ , x ∶ A , x ∶ B ⊢ M ∶ C
  --------------------------
  → Γ , x ∶ B ⊢ M ∶ C

drop {Γ} {x} {M} {A} {B} {C} ⊢M = rename p ⊢M
  where
  p : ∀ {z C} → Γ , x ∶ A , x ∶ B ∋ z ∶ C → Γ , x ∶ B ∋ z ∶ C
  p Z                = Z
  p (S x≢x Z)        = ⊥-elim (x≢x refl)
  p (S z≢x (S _ ∋z)) = S z≢x ∋z

swap : ∀ {Γ x y M A B C}
  → x ≢ y
  → Γ , y ∶ B , x ∶ A ⊢ M ∶ C
  --------------------------
  → Γ , x ∶ A , y ∶ B ⊢ M ∶ C

swap {Γ} {x} {y} {M} {A} {B} {C} x≢y ⊢M = rename p ⊢M
  where
  p : ∀ {z C} → Γ , y ∶ B , x ∶ A ∋ z ∶ C → Γ , x ∶ A , y ∶ B ∋ z ∶ C
  p Z = S x≢y Z
  p (S x₁ Z) = Z
  p (S z≢x (S z≢y ∋z)) = S z≢y (S z≢x ∋z)

subst : ∀ {Γ x N V A B}
  → ∅ ⊢ V ∶ A
  → Γ , x ∶ A ⊢ N ∶ B
  --------------------
  → Γ ⊢ N [ x := V ] ∶ B
subst {x = y} ⊢V (⊢´ {x = x} Z) with x ≟ y
... | yes _           =  weaken ⊢V
... | no  x≢y         =  ⊥-elim (x≢y refl)
subst {x = y} ⊢V (⊢´ {x = x} (S x≢y ∋x)) with x ≟ y
... | yes refl        =  ⊥-elim (x≢y refl)
... | no  _           =  ⊢´ ∋x
subst {x = y} ⊢V (⊢ƛ {x = x} ⊢N) with x ≟ y
... | yes refl        =  ⊢ƛ (drop ⊢N)
... | no  x≢y         =  ⊢ƛ (subst ⊢V (swap x≢y ⊢N))
subst ⊢V (⊢L · ⊢M)    =  (subst ⊢V ⊢L) · (subst ⊢V ⊢M)
subst ⊢V ⊢zero        =  ⊢zero
subst ⊢V (⊢suc ⊢M)    =  ⊢suc (subst ⊢V ⊢M)
subst {x = y} ⊢V (⊢case {x = x} ⊢L ⊢M ⊢N) with x ≟ y
... | yes refl        =  ⊢case (subst ⊢V ⊢L) (subst ⊢V ⊢M) (drop ⊢N)
... | no  x≢y         =  ⊢case (subst ⊢V ⊢L) (subst ⊢V ⊢M) (subst ⊢V (swap x≢y ⊢N))
subst {x = y} ⊢V (⊢μ {x = x} ⊢M) with x ≟ y
... | yes refl        =  ⊢μ (drop ⊢M)
... | no  x≢y         =  ⊢μ (subst ⊢V (swap x≢y ⊢M))


subst´ : ∀ {Γ x N V A B}
  → ∅ ⊢ V ∶ A
  → Γ , x ∶ A ⊢ N ∶ B
  -----------------------
  → Γ ⊢ N [ x ::= V ] ∶ B

subst´ ⊢V ⊢N = {!!}

preserve : ∀ {M N A}
  → ∅ ⊢ M ∶ A
  → M —→ N
  ----------
  → ∅ ⊢ N ∶ A

preserve (⊢´ ())
preserve (⊢ƛ ⊢M) ()
preserve (⊢M · ⊢N) (ξ-·₁ M—→M´)               = preserve ⊢M M—→M´ · ⊢N
preserve (⊢M · ⊢N) (ξ-·₂ x N—→N´)             = ⊢M · preserve ⊢N N—→N´
preserve (⊢ƛ ⊢M · ⊢N) (β-ƛ VN)                = subst ⊢N ⊢M
preserve ⊢zero ()
preserve (⊢suc ⊢M) (ξ-suc M—→N)               = ⊢suc (preserve ⊢M M—→N)
preserve (⊢case ⊢L ⊢M₁ ⊢M₂) (ξ-case L—→L´)    = ⊢case (preserve ⊢L L—→L´) ⊢M₁ ⊢M₂
preserve (⊢case ⊢zero ⊢M₁ ⊢M₂) β-zero         = ⊢M₁
preserve (⊢case (⊢suc ⊢M) ⊢M₁ ⊢M₂) (β-suc VV) = subst ⊢M ⊢M₂
preserve (⊢μ ⊢M) β-μ                          = subst (⊢μ ⊢M) ⊢M

data Gas : Set where
  gas : ℕ → Gas

data Finished (N : Term) : Set where
  done :
    Value N
    ----------
    → Finished N

  out-of-gas :
    --------------
    Finished N

data Steps (L : Term) : Set where

  steps : ∀ {N}
    → L —↠ N
    → Finished N
    --------------
    → Steps L

eval : ∀ {L A}
  → Gas
  → ∅ ⊢ L ∶ A
  --------------
  → Steps L

eval {L} (gas zero)    ⊢L = steps (L ∎) out-of-gas
eval {L} (gas (suc n)) ⊢L with progress ⊢L
... | done VL     = steps (L ∎) (done VL)
... | step L—→L´  with eval (gas n) (preserve ⊢L L—→L´)
...               | steps L´—↠M fin  = steps (L —→⟨ L—→L´ ⟩ L´—↠M) fin


⊢sucμ : ∅ ⊢ μ "x" ⇒ `suc ` "x" ∶ `ℕ
⊢sucμ = ⊢μ (⊢suc (⊢´ ∋x))
  where
  ∋x = Z


{-_ : eval (gas 3) ⊢sucμ ≡
  steps
  (μ "x" ⇒ `suc ` "x"
  —→⟨ β-μ ⟩
  `suc (μ "x" ⇒ `suc ` "x")
  —→⟨ ξ-suc β-μ ⟩
  `suc (`suc (μ "x" ⇒ `suc ` "x"))
  —→⟨ ξ-suc (ξ-suc β-μ) ⟩
  `suc (`suc (`suc (μ "x" ⇒ `suc ` "x")))
  ∎)
  out-of-gas
_ = refl
-}

⊢mul : ∅ ⊢ (mul · two · two) ∶ `ℕ
⊢mul = ⊢μ (⊢ƛ (⊢ƛ (⊢case (⊢´ ∋m) ⊢zero (⊢plus · (⊢´ ∋× · ⊢´ Z · ⊢´ ∋n) · ⊢´ ∋n)))) · ⊢suc (⊢suc ⊢zero) · ⊢suc (⊢suc ⊢zero)
  where
    ∋m = S (λ ()) Z
    ∋n = S (λ ()) Z
    ∋× = S (λ ()) (S (λ ()) (S (λ ()) Z))

-- to see that 2 × 2 is 4 just do ctrl-c ctrl-n and put "eval (gas 100) ⊢mul"

{-
We say that M reduces to N if M —→ N, but we can also describe the same situation by saying that N expands to M. The preservation property is sometimes called subject reduction. Its opposite is subject expansion, which holds if M —→ N and ∅ ⊢ N ⦂ A imply ∅ ⊢ M ⦂ A. Find two counter-examples to subject expansion, one with case expressions and one not involving case expressions.
-}

-- Exemplo 1:

M₀ : Term
M₀ = case (`suc `zero) [zero⇒ (ƛ "x" ⇒ `"x") |suc "n" ⇒ `zero ]

N₀ : Term
N₀ = `zero

¬⊢M₀ : ∀ (T : Type) → ¬ (∅ ⊢ M₀ ∶ T)
¬⊢M₀ (T ⇒ T₁) (⊢case ⊢M₀ _ ())
¬⊢M₀ `ℕ       (⊢case ⊢M₀ () _)

⊢N₀ : ∅ ⊢ N₀ ∶ `ℕ
⊢N₀ = ⊢zero

M₀—→N : M₀ —→ N₀
M₀—→N = β-suc V-zero

-- Exemplo 2

M₁ : Term
M₁ = (ƛ "x" ⇒ `zero) · (ƛ "x" ⇒ `"x" · `"x")

¬⊢M₁ : ∀ (T : Type) → ¬ (∅ ⊢ M₁ ∶ T)
¬⊢M₁ T (⊢M₁ · ⊢M₂) = ⊥-elim (nope₂ ⊢M₂)

N₁ : Term
N₁ = `zero

⊢N₁ : ∅ ⊢ N₁ ∶ `ℕ
⊢N₁ = ⊢zero

M₁—→N₁ : M₁ —→ N₁
M₁—→N₁ = β-ƛ V-ƛ


-- A term is Normal if it cannot reduce:

Normal : Term → Set
Normal T = ∀ {M N} → ¬ (M —→ N)

Stuck : Term → Set
Stuck T = (Normal T) × (¬ Value T)

{-
postulate
  unstuck : ∀ {M A}
    → ∅ ⊢ M ∶ A
    ------------
    → ¬ Stuck M

postulate
  preserves : ∀ {M N A}
    → ∅ ⊢ M ∶ A
    → M —↠ N
    ------------
    → ∅ ⊢ N ∶ A

postulate
  wttdgs : ∀ {M N A}
    → ∅ ⊢ M ∶ A
    → M —↠ N
    -------------
    → ¬ Stuck N
-}


-- Example of an ill typed term that does get stuck:

ILL : Term
ILL = (`zero) · (`suc `zero)

-- Proof the 3 statements above

unstuck : ∀ {M A}
  → ∅ ⊢ M ∶ A
  --------------
  → ¬ Stuck M

unstuck ⊢M ⟨ NorM , ¬ValM ⟩ with progress ⊢M
... | step M—→N = ⊥-elim (NorM M—→N)
... | done ValM = ⊥-elim (¬ValM ValM)

preserves : ∀ {M N A}
  → ∅ ⊢ M ∶ A
  → M —↠ N
  --------------
  → ∅ ⊢ N ∶ A

preserves ⊢M (M ∎) = ⊢M
preserves ⊢L (L —→⟨ L—→M ⟩ M—↠N) = preserves (preserve ⊢L L—→M) M—↠N

wttdgs : ∀ {M N A}
  → ∅ ⊢ M ∶ A
  → M —↠ N
  --------------
  → ¬ Stuck N

wttdgs ⊢M M—↠N StN = unstuck (preserves ⊢M M—↠N) StN

cong₄ : ∀ {A B C D E : Set} (f : A → B → C → D → E)
  {s w : A} {t x : B} {u y : C} {v z : D}
  → s ≡ w → t ≡ x → u ≡ y → v ≡ z → f s t u v ≡ f w x y z
cong₄ f refl refl refl refl = refl


deterministic : ∀ {M M´ M´´}
  → (M —→ M´)
  → (M —→ M´´)
  ----------------
  → M´ ≡ M´´

deterministic (ξ-·₁ L—→L´) (ξ-·₁ L—→L₁´) = cong₂ (_·_) (deterministic L—→L´ L—→L₁´) refl
deterministic (ξ-·₁ L—→L´) (ξ-·₂ VL M—→M´) = ⊥-elim (V¬—→ VL L—→L´)
deterministic (ξ-·₁ ()) (β-ƛ _)
deterministic (ξ-·₂ VV M—→M´) (ξ-·₁ V—→L´) = ⊥-elim (V¬—→ VV V—→L´)
deterministic (ξ-·₂ _ M—→M´) (ξ-·₂ _ M—→M´´) = cong₂ (_·_) refl (deterministic M—→M´ M—→M´´)
deterministic (ξ-·₂ _ M—→M´) (β-ƛ VM) = ⊥-elim (V¬—→ VM M—→M´)
deterministic (β-ƛ _) (ξ-·₁ ())
deterministic (β-ƛ VV) (ξ-·₂ _ V—→M´) = ⊥-elim (V¬—→ VV V—→M´)
deterministic (β-ƛ _) (β-ƛ _) = refl
deterministic (ξ-suc M—→M´) (ξ-suc M—→M´´) = cong `suc_ (deterministic M—→M´ M—→M´´)
deterministic (ξ-case M—→M´) (ξ-case M—→M´´) = cong₄ case_[zero⇒_|suc_⇒_] (deterministic M—→M´ M—→M´´) refl refl refl
deterministic (ξ-case ()) β-zero
deterministic (ξ-case sucV—→) (β-suc VV) = ⊥-elim (V¬—→ (V-suc VV) sucV—→)
deterministic β-zero (ξ-case ())
deterministic β-zero β-zero = refl
deterministic (β-suc VV) (ξ-case sucV—→) = ⊥-elim (V¬—→ (V-suc VV) sucV—→)
deterministic (β-suc _) (β-suc _) = refl
deterministic β-μ β-μ = refl

-- zap
{-
  Determinism of step : Becomes False (anything can evalute as usual AND to zap)
  Progress : Becomes False (zap is well typed but doesn't reduce and is not a value)
  Preservation : Remains Ture
-}

-- foo
{-
  Determinism of Step : Remains true (ƛ x ⇒ x não avalia pra ninguém)
  Progress : Remains true (ƛ x ⇒ x é um valor e tem um passo de avaliação, mas acho que não tem problema)
  Preservation : False (ƛ x ⇒ x é bem tipado mas avalia para um termo sem tipo)
-}

-- Remove ξ-·₁
{-
  Determinism of Step : Remains true
  Progress : False. Now we can't take a step in terms that were evaluated by this rule, and they still well typed
  Preservation : Remains True
-}

-- Add that weird construction that associates naturals with functions
{-
  Determinism of Step : Remains True
  Progress : Remains True
  Preservation : Remains True
-}
