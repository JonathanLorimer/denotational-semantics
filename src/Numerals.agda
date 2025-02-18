module Numerals where

open import Data.Nat
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _∎; step-≡; step-≡-⟩)
import Data.Product as P
open P using (_×_; _,_) 
open import Function.Base using (_∘_)

module NonCanonical where

  data Bin : Set where
    𝕆 : Bin
    𝕀 : Bin
    O_ : Bin -> Bin
    I_ : Bin -> Bin

  -- 1. Show that every numeral represents a single number.
  bin_to_nat : Bin → ℕ  
  bin_to_nat 𝕆 = 0 
  bin_to_nat 𝕀 = 1
  bin_to_nat (O x) = 2 * (bin_to_nat x)
  bin_to_nat (I x) = 2 * (bin_to_nat x) + 1

  OI≡2 : bin_to_nat (O 𝕀) ≡ 2 
  OI≡2 = refl

  OII≡6 : bin_to_nat (O I 𝕀) ≡ 6 
  OII≡6 = refl

  OOIIIOOI≡156 : bin_to_nat (O O I I I O O 𝕀) ≡ 156
  OOIIIOOI≡156 = refl

  data D2 : Set where
    One : ℕ → D2
    Zero : ℕ → D2

  _→D2_ : (ℕ → ℕ) → D2 → D2
  f →D2 One x = One (f x)
  f →D2 Zero x = Zero (f x)

  div2 : ℕ → D2 
  div2 0 = Zero 0
  div2 1 = One 0 
  div2 (suc (suc n)) = suc →D2 (div2 n)

  -- 2. Show that every number represents a single number.
  {-# TERMINATING #-}
  nat_to_bin : ℕ → Bin
  nat_to_bin 0 = 𝕆
  nat_to_bin 1 = 𝕀
  nat_to_bin x with div2 x
  ... | Zero n = O (nat_to_bin n)
  ... | One n = I (nat_to_bin n)

  156≡OOIIIOOI : nat_to_bin 156 ≡ O O I I I O O 𝕀 
  156≡OOIIIOOI = refl

module Canonical where
  data Bin : Set where
    𝕀 : Bin
    O_ : Bin -> Bin
    I_ : Bin -> Bin

  data N : Set where 
    𝕆 : N
    𝔹 : Bin → N

  _→N_ : (Bin → Bin) → N → N
  _ →N 𝕆 = 𝕆
  f →N (𝔹 b) = 𝔹 (f b)

  bin_to_nat : N → ℕ  
  bin_to_nat 𝕆 = 0 
  bin_to_nat (𝔹 𝕀) = 1
  bin_to_nat (𝔹 (O x)) = 2 * (bin_to_nat (𝔹 x))
  bin_to_nat (𝔹 (I x)) = 2 * (bin_to_nat (𝔹 x)) + 1

  open NonCanonical using (div2; D2; Zero; One; _→D2_)

  {-# TERMINATING #-}
  nat_to_bin : ℕ → N
  nat_to_bin 0 = 𝕆 
  nat_to_bin 1 = 𝔹 𝕀
  nat_to_bin x with div2 x
  ... | Zero n = O_ →N (nat_to_bin n)
  ... | One n = I_ →N (nat_to_bin n)

  156≡OOIIIOOI : nat_to_bin 156 ≡ 𝔹 (O O I I I O O 𝕀)
  156≡OOIIIOOI = refl

  155≡OOIIIOOI : nat_to_bin 155 ≡ 𝔹 (I I O I I O O 𝕀)
  155≡OOIIIOOI = refl
  
  open import Data.Nat.Properties

  div2n+n≡Zeron : (n : ℕ) → (div2 (n + n) ≡ Zero n)
  div2n+n≡Zeron zero = refl
  div2n+n≡Zeron (suc n) = 
    begin
    div2 (suc n + suc n)
    ≡⟨ cong (div2 ∘ suc) (+-comm n (suc n)) ⟩
    div2 (suc (suc (n + n)))
    ≡⟨ refl ⟩
    suc →D2 (div2 (n + n))
    ≡⟨ cong (suc →D2_) (div2n+n≡Zeron n) ⟩
    suc →D2 (Zero n)
    ≡⟨ refl ⟩
    Zero (suc n)
    ∎
  
  nat_to_bin-Zero : (n m : ℕ) → (div2 (2 + n) ≡ Zero m) → nat_to_bin (2 + n) ≡ O_ →N (nat_to_bin m)
  nat_to_bin-Zero n m eq with div2 n | eq
  ... | Zero m | refl = refl

  div2-zero-step : {n m : ℕ} → (div2 n ≡ Zero m) → (div2 (2 + n) ≡ Zero (suc m))
  div2-zero-step {n} eq with div2 n | eq 
  ... | Zero x | refl = refl

  power-of-2→O : (n : ℕ) → nat_to_bin (2 * n) ≡ O_ →N (nat_to_bin n)
  power-of-2→O zero = refl
  power-of-2→O (suc n) = 
    begin
    nat_to_bin (1 + (n + (1 + (n + zero))))
    ≡⟨ cong (nat_to_bin ∘ suc ∘ (n +_)) (*-identityˡ (suc n)) ⟩
    nat_to_bin (suc (n + (1 + n)))
    ≡⟨ cong (nat_to_bin ∘ suc) (+-comm n (1 + n)) ⟩
    nat_to_bin (suc (suc n + n))
    ≡⟨ cong (nat_to_bin ∘ suc) (+-assoc 1 n n) ⟩
    nat_to_bin (2 + (n + n))
    ≡⟨ nat_to_bin-Zero (n + n) (suc n) (div2-zero-step { n = n + n } (div2n+n≡Zeron n)) ⟩
    (O_ →N nat_to_bin (suc n))
    ∎

  power-of-2+1→I : (n : ℕ) → nat_to_bin (2 * (suc n) + 1) ≡ I_ →N (nat_to_bin (suc n))
  power-of-2+1→I zero = refl
    -- begin
    -- nat_to_bin (2 *  + 1)
    -- ≡⟨ cong (nat_to_bin ∘ (_+ 1)) (*-zeroʳ 2) ⟩
    -- nat_to_bin 1
    -- ≡⟨ {!   !} ⟩
    -- {!   !}
    -- ∎
  power-of-2+1→I (suc n) = 
    begin
    nat_to_bin (2 * (2 + n) + 1)
    ≡⟨ {!   !} ⟩
    (I_ →N nat_to_bin (2 + n))
    ∎

  -- {-# TERMINATING #-}
  -- nat_to_bin : ℕ → N
  -- nat_to_bin 0 = 𝕆 
  -- nat_to_bin 1 = 𝔹 𝕀
  -- nat_to_bin x with div2 x
  -- ... | Zero n = O_ →N (nat_to_bin n)
  -- ... | One n = I_ →N (nat_to_bin n)


    -- begin
    -- nat_to_bin (1 + (n + (1 + (n + zero))))
    -- ≡⟨ cong (nat_to_bin ∘ suc ∘ (n +_)) (*-identityˡ (suc n)) ⟩
    -- nat_to_bin (suc (n + (1 + n)))
    -- ≡⟨ cong (nat_to_bin ∘ suc) (+-comm n (1 + n)) ⟩
    -- nat_to_bin (suc (suc n + n))
    -- ≡⟨ cong (nat_to_bin ∘ suc) (+-assoc 1 n n) ⟩
    -- nat_to_bin (2 + (n + n))
    -- ≡⟨ nat_to_bin-Zero (n + n) (suc n) (div2-zero-step { n = n + n } (div2n+n≡Zeron n)) ⟩
    -- (O_ →N nat_to_bin (suc n))
    -- ∎

  N→ℕ→N≡ : (n : N) → nat_to_bin (bin_to_nat n) ≡ n 
  N→ℕ→N≡ 𝕆 = refl 
  N→ℕ→N≡ (𝔹 𝕀) = refl 
  N→ℕ→N≡ (𝔹 (O x)) = 
    begin 
    nat_to_bin (bin_to_nat (𝔹 (O x))) 
    ≡⟨ refl ⟩
    nat_to_bin (2 * (bin_to_nat (𝔹 x)))
    ≡⟨ power-of-2→O (bin_to_nat (𝔹 x)) ⟩
    (O_ →N nat_to_bin (bin_to_nat (𝔹 x)))
    ≡⟨ cong (O_ →N_) (N→ℕ→N≡ (𝔹 x)) ⟩
    (O_ →N (𝔹 x))
    ≡⟨ refl ⟩
    O_ →N (𝔹 x)
    ≡⟨ refl ⟩
    𝔹 (O x)
    ∎   
  N→ℕ→N≡ (𝔹 (I x)) =  
    begin
    nat_to_bin (bin_to_nat (𝔹 (I x)))
    ≡⟨ refl ⟩
    nat_to_bin (2 * (bin_to_nat (𝔹 x)) + 1)
    ≡⟨ {!   !} ⟩
    𝔹 (I x)
    ∎