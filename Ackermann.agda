module Ackermann where

import Algebra
import Algebra.Structures
import Data.Nat.Properties as ℕProp
import Relation.Binary
import Relation.Binary.PropositionalEquality as ≡

open import Data.Nat using (ℕ; zero; suc;
  _≤_; z≤n; s≤s;
  _+_; _*_)
open ℕProp.≤-Reasoning
open import Data.Product using (proj₁)
open import Function using (_$_; _∘′_)
open Relation.Binary using (_Preserves_⟶_)
open ≡ using (cong; _≡_)

private
  module ≤ = Relation.Binary.DecTotalOrder ℕProp.≤-decTotalOrder

open Relation.Binary.StrictTotalOrder ℕProp.strictTotalOrder
  using (_<_; compare)
open Algebra.CommutativeSemiring ℕProp.commutativeSemiring
  using (+-comm; *-comm; distrib)

open import Lemmae

-- Ackermann function.
ack : ℕ → ℕ → ℕ
ack zero    n       = suc n
ack (suc m) zero    = ack m (suc zero)
ack (suc m) (suc n) = ack m (ack (suc m) n)

ack-positive : (m n : ℕ) → 0 < ack m n
ack-positive zero n = s≤s z≤n
ack-positive (suc m) zero = ack-positive m 1
ack-positive (suc m) (suc n) = ack-positive m _

ack-superlinear : (m : ℕ) {n : ℕ} → n < ack m n
ack-superlinear zero            = s≤s ≤.refl
ack-superlinear (suc m) {zero}  = ≤.trans (s≤s z≤n) (ack-superlinear m)
ack-superlinear (suc m) {suc n} = begin
  suc n
    <⟨ s≤s (ack-superlinear (suc m)) ⟩
  suc (ack (suc m) n)
    ≤⟨ ack-superlinear m ⟩
  ack m (ack (suc m) n) ∎

ack-monotonic₂ : (m : ℕ) → ack m Preserves _<_ ⟶ _<_
ack-monotonic₂ zero lt = s≤s lt
ack-monotonic₂ (suc m) {zero} {1} (s≤s z≤n) = ack-superlinear m
ack-monotonic₂ (suc m) {zero} {suc (suc n)} (s≤s z≤n) = ack-monotonic₂ m $ begin
  1
    <⟨ s≤s (s≤s z≤n) ⟩
  suc (suc n)
    ≤⟨ ack-superlinear (suc m) ⟩
  ack (suc m) (suc n) ∎
ack-monotonic₂ (suc m) {suc _} {suc _} (s≤s lt) =
  ack-monotonic₂ m (ack-monotonic₂ (suc m) lt)

ack-nondecreasing₂ : (m : ℕ) → ack m Preserves _≤_ ⟶ _≤_
ack-nondecreasing₂ m = weaken-monotonic (ack-monotonic₂ m)

-- Note that the < case is not true.
ack-₁dom₂ : (m n : ℕ) → ack m (suc n) ≤ ack (suc m) n
ack-₁dom₂ m zero = ≤.refl
ack-₁dom₂ m (suc n) = ack-nondecreasing₂ m $ begin
  suc n
    <⟨ ack-superlinear m ⟩
  ack m (suc n)
    ≤⟨ ack-₁dom₂ m n ⟩
  ack (suc m) n ∎

ack-₁dom₂-iterated : (m n k : ℕ) → ack m (k + n) ≤ ack (k + m) n
ack-₁dom₂-iterated m n zero = ≤.refl
ack-₁dom₂-iterated m n (suc k) = begin
  ack m (suc k + n)
    ≤⟨ ack-₁dom₂ m (k + n) ⟩
  ack (suc m) (k + n)
    ≤⟨ ack-₁dom₂-iterated (suc m) n k ⟩
  ack (k + suc m) n
    ≡⟨ cong (λ x → ack x n) (suc-push k m) ⟩
  ack (suc k + m) n ∎

ack-monotonic₁ : (n : ℕ) → (λ m → ack m n) Preserves _<_ ⟶ _<_
ack-monotonic₁ n {zero} {suc q} (s≤s lt) = begin
  suc n
    <⟨ ack-superlinear q ⟩
  ack q (suc n)
    ≤⟨ ack-₁dom₂ q n ⟩
  ack (suc q) n ∎
ack-monotonic₁ zero {suc _} {suc (suc _)} (s≤s (s≤s le)) = ack-monotonic₁ 1 (s≤s le)
ack-monotonic₁ (suc n) {suc p} {suc (suc q)} (s≤s (s≤s le)) = begin
  ack p (ack (suc p) n)
    <⟨ ack-monotonic₂ p (ack-monotonic₁ n (s≤s (s≤s le))) ⟩
  ack p (ack (suc (suc q)) n)
    ≤⟨ ℕProp.≤⇒pred≤ (ack-monotonic₁ _ (s≤s le)) ⟩
  ack (suc q) (ack (suc (suc q)) n) ∎

ack-nondecreasing₁ : (n : ℕ) → (λ m → ack m n) Preserves _≤_ ⟶ _≤_
ack-nondecreasing₁ n = weaken-monotonic (ack-monotonic₁ n)

-- maybe needs a better name
ack-fastgrowing : (m n : ℕ) → ack m (2 * n) < ack (2 + m) n
ack-fastgrowing zero zero = s≤s (s≤s z≤n)
ack-fastgrowing zero (suc n) = begin
  suc (ack 0 (2 * suc n))
    ≡⟨ ≡.refl ⟩
  2 + (2 * (1 + n))
    ≡⟨ cong (suc ∘′ suc) (proj₁ distrib 2 1 n) ⟩
  4 + 2 * n
    ≡⟨ ≡.refl ⟩
  2 + ack 0 (1 + 2 * n)
    ≤⟨ s≤s (s≤s (ack-₁dom₂ 0 (2 * n))) ⟩
  2 + ack 1 (2 * n)
    ≡⟨ ≡.refl ⟩
  1 + ack 1 (ack 0 (2 * n))
    ≤⟨ ack-monotonic₂ 1 (ack-fastgrowing 0 n) ⟩
  ack 1 (ack 2 n) ∎
ack-fastgrowing (suc m) zero = begin
  suc (ack (suc m) zero)
    ≡⟨ ≡.refl ⟩
  suc (ack m 1)
    ≤⟨ ack-superlinear m ⟩
  ack m (ack m 1)
    ≤⟨ ℕProp.≤⇒pred≤ (ack-superlinear (suc m)) ⟩
  ack (suc m) (ack m (ack m 1))
    ≡⟨ ≡.refl ⟩
  ack (3 + m) 0 ∎
ack-fastgrowing (suc m) (suc n) = begin
  suc (ack (1 + m) (2 * suc n))
    ≡⟨ cong (suc ∘′ ack (1 + m)) (proj₁ distrib 2 1 n) ⟩
  suc (ack (1 + m) (2 + 2 * n))
    ≡⟨ ≡.refl ⟩
  suc (ack m (ack m (ack (1 + m) (2 * n))))
    ≤⟨ ack-monotonic₂ m (ack-monotonic₂ m (ack-fastgrowing (1 + m) n)) ⟩
  ack m (ack m (ack (3 + m) n))
    ≤⟨ ℕProp.≤⇒pred≤ (ack-monotonic₂ m (ack-monotonic₁ (ack (3 + m) n) ≤.refl)) ⟩
  ack m (ack (1 + m) (ack (3 + m) n))
    ≡⟨ ≡.refl ⟩
  ack (1 + m) (1 + ack (3 + m) n)
    ≤⟨ ack-₁dom₂ (1 + m) (ack (3 + m) n) ⟩
  ack (2 + m) (ack (3 + m) n) ∎
