-- Exercises from Isomorphism module
-- Separated to eliminate conflicts with ℕ module

module IsoEx where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong-app)
open Eq.≡-Reasoning

import Naturals
import InductionT
open Naturals using (ℕ; zero; suc; _+_; _*_; _∸_;
                     Bin; x0_; x1_; nil; inc; To; From; mul2)
open InductionT using (+-comm; Bin-Law2)

open import Isomorphism


_+'_ : ℕ → ℕ → ℕ
m +' zero = m
m +' (suc n) = suc (m +' n)



same-app : ∀ (m n : ℕ) → m +' n ≡ m + n
same-app m n rewrite +-comm m n = helper m n
  where
  helper : ∀ (m n : ℕ) → m +' n ≡ n + m
  helper m zero = refl
  helper m (suc n) = cong suc (helper m n)

same : _+'_ ≡ _+_
same = extensionality (λ x → extensionality (λ y → same-app x y))



Bin-embedding : ℕ ≲ Bin
Bin-embedding =
  record
    { to   = To
    ; from = From
    ; from∘to = λ {n → Bin-Law2 n}
    }
