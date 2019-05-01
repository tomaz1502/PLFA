module plfa_induction where

import Relation.Binary.PropositionalEquality as Eq
import plfa_naturals

open plfa_naturals using (ℕ; zero; suc; _+_; _*_; _∸_; Bin; inc; From; To)
open plfa_naturals.Bin using (nil; x0_; x1_)
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)


-- operator that is commutative, associative and distributive: union, intersection of sets
-- operator that is not commutative: ∸

+-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc zero n p =
  begin (zero + n) + p
    ≡⟨⟩  n + p
    ≡⟨⟩  zero + (n + p) ∎
+-assoc (suc m) n p = 
  begin
    (suc m + n) + p
  ≡⟨⟩
    suc ((m + n) + p)
  ≡⟨ cong suc (+-assoc m n p) ⟩
    suc (m + (n + p))
  ≡⟨⟩
    suc m + (n + p) ∎

+-identity : ∀ (m : ℕ) → m + zero ≡ m
+-identity zero = 
   begin
     zero + zero
   ≡⟨⟩
     zero ∎
+-identity (suc m') =
  begin
    (suc m') + zero
  ≡⟨⟩
    suc (m' + zero)
  ≡⟨ cong suc (+-identity m')⟩
    suc m' ∎

+-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc zero n =
  begin
    zero + suc n
  ≡⟨⟩
    suc n ∎
+-suc (suc m') n =
  begin
    (suc m') + (suc n)
  ≡⟨⟩
    suc (m' + suc n)
  ≡⟨ cong suc (+-suc m' n) ⟩
    suc (suc (m' + n))
  ≡⟨⟩
    suc (suc m' + n) ∎

+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm m zero =
  begin
    m + zero
  ≡⟨ +-identity m ⟩
    m
  ≡⟨⟩
    zero + m ∎
+-comm m (suc n) =
  begin
    m + (suc n)
  ≡⟨ +-suc m n ⟩
    suc (m + n)
  ≡⟨ cong suc (+-comm m n)⟩
    suc (n + m)
  ≡⟨⟩
    (suc n) + m ∎

+-rearrange : ∀ (m n p q : ℕ) → (m + n) + (p + q) ≡ m + (n + p) + q
+-rearrange m n p q =
  begin
    (m + n) + (p + q)
  ≡⟨ +-assoc m n (p + q) ⟩
    m + (n + (p + q))
  ≡⟨ cong (m +_) (sym (+-assoc n p q)) ⟩
    m + ((n + p) + q)
  ≡⟨ sym (+-assoc m (n + p) q) ⟩
    (m + (n + p)) + q ∎

+-assoc' : ∀ (m n p : ℕ) → m + (n + p) ≡ (m + n) + p
+-assoc' zero n p = refl
+-assoc' (suc m) n p rewrite +-assoc' m n p = refl

+-identity' : ∀ (n : ℕ) → n + zero ≡ n
+-identity' zero = refl
+-identity' (suc n) rewrite +-identity' n = refl

+-suc' : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc' zero n = refl
+-suc' (suc m) n rewrite +-suc' m n = refl

+-comm' : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm' m zero rewrite +-identity' m = refl
+-comm' m (suc n) rewrite +-suc' m n | +-comm m n = refl

+-assoc'' : ∀ (m n p : ℕ) → m + (n + p) ≡ (m + n) + p
+-assoc'' zero n p = refl
+-assoc'' (suc m) n p rewrite +-assoc'' m n p = refl

+-swap : ∀ (m n p : ℕ) → m + (n + p) ≡ n + (m + p)
+-swap m n p rewrite sym (+-assoc m n p) | +-comm m n | +-assoc n m p = refl
 
*-distr-+ : ∀ (m n p : ℕ) → (m + n) * p ≡ m * p + n * p
*-distr-+ zero n p = refl
*-distr-+ (suc m) n p rewrite *-distr-+ m n p | +-assoc p (m * p) (n * p) = refl

*-identity : ∀ (n : ℕ) → n * zero ≡ zero
*-identity zero = refl
*-identity (suc n) rewrite *-identity n = refl

*-suc : ∀ (m n : ℕ) → m * (suc n) ≡ m + m * n
*-suc zero n = refl
*-suc (suc m) n rewrite *-suc m n | +-swap n m (m * n)= refl

*-comm : ∀ (m n : ℕ) → m * n ≡ n * m
*-comm zero n rewrite *-identity n = refl
*-comm (suc m) n rewrite *-comm m n | sym (*-suc n m)= refl

∸-zero : ∀ (n : ℕ) → zero ∸ n ≡ zero
∸-zero zero = refl
∸-zero (suc n) = refl

∸-+-assoc : ∀ (m n p : ℕ) → m ∸ n ∸ p ≡ m ∸ (n + p)
∸-+-assoc zero n p rewrite ∸-zero n | ∸-zero p | ∸-zero (n + p) = refl
∸-+-assoc (suc m) zero p = refl
∸-+-assoc (suc m) (suc n) p rewrite ∸-+-assoc m n p = refl

Bin-Law1 : ∀ (x : Bin) → From (inc x) ≡ suc (From x)
Bin-Law1 nil = refl
Bin-Law1 (x0 x) = refl
Bin-Law1 (x1 x) rewrite Bin-Law1 x | +-suc (From x) (From x) = refl

-- to (from x) = x -> False! -> x = x1 x1 x0 nil
-- from x = suc (From x1 x0 nil + From x1 x0 nil) = 3
-- to 3 = inc (inc (inc nil)) = inc (inc x1 nil) = inc (x0 x1 nil) = x1 x1 nil ‌!= x1 x1 x0 nil

Bin-Law2 : ∀ (n : ℕ) → From (To n) ≡ n
Bin-Law2 zero = refl
Bin-Law2 (suc n) rewrite Bin-Law1 (To n) | Bin-Law2 n = refl


-- From (inc (x1 b)) = From (x0 (inc b)) = From (inc b) + From (inc b) = suc (From b) + suc (From b) = suc (From (x1 b))
