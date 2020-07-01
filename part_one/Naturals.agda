module Naturals where

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)

infixl 6 _+_

_+_ : ℕ → ℕ → ℕ
zero + n = n
suc m + n = suc (m + n)


_ : 2 + 3 ≡ 5
_ =
  begin 2 + 3
    ≡⟨⟩ suc (suc zero) + (suc (suc (suc zero))) -- definition of 2 and 3
    ≡⟨⟩ suc ((suc zero) + (suc (suc (suc zero)))) -- inductive case of _+_
    ≡⟨⟩ suc (suc (zero + (suc (suc (suc zero))))) -- inductive case of _+_
    ≡⟨⟩ suc (suc (suc (suc (suc zero)))) -- base case of _+_
    ≡⟨⟩ 5 ∎ -- definition of 5

_ : 2 + 3 ≡ 5
_ = refl

_ =

  begin 3 + 4
    ≡⟨⟩ suc (2 + 4)
    ≡⟨⟩ suc (suc (1 + 4))
    ≡⟨⟩ suc (suc (suc (0 + 4)))
    ≡⟨⟩ suc (suc (suc 4))
    ≡⟨⟩ 7 ∎

infixl 7 _*_

_*_ : ℕ → ℕ → ℕ
zero  * n = zero
suc m * n = n + m * n

_ : 3 * 4 ≡ 12
_ =
  begin 3 * 4
    ≡⟨⟩ (suc 2) * 4
    ≡⟨⟩ 4 + (2 * 4)
    ≡⟨⟩ 4 + ((suc 1) * 4)
    ≡⟨⟩ 4 + (4 + (1 * 4))
    ≡⟨⟩ 4 + (4 + ((suc 0) * 4))
    ≡⟨⟩ 4 + (4 + (4 + (0 * 4)))
    ≡⟨⟩ 4 + (4 + 4)
    ≡⟨⟩ 12 ∎

infixl 8 _^_

_^_ : ℕ → ℕ → ℕ
n ^ 0 = 1
n ^ suc m = n * n ^ m

_ : 3 ^ 4 ≡ 81
_ =
  begin 3 ^ 4
    ≡⟨⟩ 3 ^ (suc 3)
    ≡⟨⟩ 3 * (3 ^ 3)
    ≡⟨⟩ 3 * (3 ^ (suc 2))
    ≡⟨⟩ 3 * 3 * (3 ^ 2)
    ≡⟨⟩ 3 * 3 * 3 * (3 ^ 1)
    ≡⟨⟩ 3 * 3 * 3 * 3 * (3 ^ 0)
    ≡⟨⟩ 3 * 3 * 3 * 3 * 1
    ≡⟨⟩ 81 ∎

infixl 6 _∸_
_∸_ : ℕ → ℕ → ℕ
m             ∸ 0 = m
0         ∸ suc n = 0
suc m ∸ suc n = m ∸ n

_ =
  begin 5 ∸ 3
    ≡⟨⟩ suc 4 ∸ suc 2
    ≡⟨⟩ 4 ∸ 2
    ≡⟨⟩ 3 ∸ 1
    ≡⟨⟩ 2 ∸ 0
    ≡⟨⟩ 2 ∎

{-# BUILTIN NATPLUS _+_ #-}
{-# BUILTIN NATTIMES _*_ #-}
{-# BUILTIN NATMINUS _∸_ #-}

data Bin : Set where
  nil : Bin
  x0_ : Bin → Bin
  x1_ : Bin → Bin

inc : Bin → Bin
inc nil = x1 nil
inc (x0 b) = x1 b
inc (x1 b) = (x0 (inc b))

_ : inc (x1 x1 x0 x1 nil) ≡ x0 x0 x1 x1 nil
_ =
  begin inc (x1 x1 x0 x1 nil)
  ≡⟨⟩ (x0 inc(x1 x0 x1 nil))
  ≡⟨⟩ (x0 x0 inc(x0 x1 nil))
  ≡⟨⟩ x0 x0 x1 x1 nil ∎

_ : inc (x0 nil) ≡ x1 nil
_ = refl

_ : inc (x1 nil) ≡ x0 x1 nil
_ = refl

_ : inc (x0 x1 nil) ≡ x1 x1 nil
_ = refl

_ : inc (x1 x1 nil) ≡ x0 x0 x1 nil
_ = refl

mul2 : ℕ → ℕ
mul2 0 = 0
mul2 (suc n) = suc (suc (mul2 n))

To : ℕ → Bin
To zero = nil
To (suc n) = inc (To n)

From : Bin → ℕ
From nil = 0
From (x0 b) = mul2 (From b)
From (x1 b) = suc (mul2 (From b))

_ : To 1 ≡ x1 nil
_ = refl

_ : To 6 ≡ x0 x1 x1 nil
_ = refl

_ : From (x0 x0 x1 nil) ≡ 4
_ =
  begin From (x0 x0 x1 nil)
    ≡⟨⟩ From (x0 x1 nil) + From (x0 x1 nil)
    ≡⟨⟩ From (x1 nil) + From (x1 nil) + From (x1 nil) + From (x1 nil)
    ≡⟨⟩ 1 + From (x0 nil) + 1 + From (x0 nil) + 1 + From (x0 nil) + 1 + From (x0 nil)
    ≡⟨⟩ 4 ∎
