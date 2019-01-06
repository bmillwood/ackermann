module Lemmae where

import Algebra
import Algebra.Structures
import Data.Nat.Properties as ℕProp
import Relation.Binary.PropositionalEquality as ≡

open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (ℕ; zero; suc;
  _≤_; _<_; z≤n; s≤s;
  pred; _+_; _∸_; _⊔_)
open import Data.Product using (proj₂)
open ℕProp using (m≤m⊔n)
open import Data.Vec using (Vec; []; _∷_; foldr; map; lookup)
open import Function using (_$_; _∘′_; const)
open import Relation.Binary
open ≡ using (cong; _≡_; _≢_; module ≡-Reasoning)

private
  module ≤ = Relation.Binary.DecTotalOrder ℕProp.≤-decTotalOrder

open Relation.Binary.StrictTotalOrder ℕProp.strictTotalOrder using (compare)
open Algebra.CommutativeSemiring ℕProp.commutativeSemiring
  using (+-comm; *-comm; distrib)

-- Increasing implies nondecreasing.
weaken-monotonic : {f : ℕ → ℕ}
  → f Preserves _<_ ⟶ _<_
  → f Preserves _≤_ ⟶ _≤_
weaken-monotonic _ {n} {m} _ with compare n m
weaken-monotonic strong _     | tri< lt _ _ = ℕProp.≤⇒pred≤ (strong lt)
weaken-monotonic _ {n} {.n} _ | tri≈ _ ≡.refl _ = ≤.refl
weaken-monotonic _ le         | tri> _ ne gt = ⊥-elim (ne (≤.antisym le (ℕProp.≤⇒pred≤ gt)))

<⇒≢ : ∀ {m n} → m < n → m ≢ n
<⇒≢ le ≡.refl = ℕProp.1+n≰n le

suc-push : (x y : ℕ) → x + suc y ≡ suc (x + y)
suc-push zero y = _≡_.refl
suc-push (suc x) y = cong suc (suc-push x y)

pred-∸-suc : (m n : ℕ) → pred (m ∸ n) ≡ m ∸ suc n
pred-∸-suc zero zero = ≡.refl
pred-∸-suc zero (suc n) = ≡.refl
pred-∸-suc (suc m) zero = ≡.refl
pred-∸-suc (suc m) (suc n) = pred-∸-suc m n

module ⊔ = Algebra.Structures.IsCommutativeMonoid
  (Algebra.CommutativeSemiringWithoutOne.+-isCommutativeMonoid ℕProp.⊔-⊓-0-commutativeSemiringWithoutOne)

m≤n⊔m : (m n : ℕ) → m ≤ n ⊔ m
m≤n⊔m m n = begin
  m ≤⟨ m≤m⊔n m n ⟩
  m ⊔ n ≡⟨ ⊔.comm m n ⟩
  n ⊔ m ∎
 where
  open ℕProp.≤-Reasoning

_⊔-mono_ : _⊔_ Preserves₂ _≤_ ⟶ _≤_ ⟶ _≤_
_⊔-mono_ {zero}{y}{u}{v} z≤n u≤v = begin
  0 ⊔ u ≤⟨ u≤v ⟩
  v     ≤⟨ m≤n⊔m v y ⟩
  y ⊔ v ∎
 where
  open ℕProp.≤-Reasoning
_⊔-mono_ {x}{y}{zero}{v} x≤y z≤n = begin
  x ⊔ 0 ≡⟨ proj₂ ⊔.identity x ⟩
  x     ≤⟨ x≤y ⟩
  y     ≤⟨ m≤m⊔n y v ⟩
  y ⊔ v ∎
 where
  open ℕProp.≤-Reasoning
s≤s x≤y ⊔-mono s≤s u≤v = s≤s (x≤y ⊔-mono u≤v)

x⊔x≡x : (x : ℕ) → x ⊔ x ≡ x
x⊔x≡x zero = ≡.refl
x⊔x≡x (suc n) = cong suc (x⊔x≡x n)

≤-⊔ : (m n : ℕ) → m ≤ n → m ⊔ n ≡ n
≤-⊔ zero _ _ = ≡.refl
≤-⊔ (suc m) (suc n) (s≤s le) = cong suc (≤-⊔ m n le)

⊔-universal : {x y z : ℕ} → x ≤ z → y ≤ z → x ⊔ y ≤ z
⊔-universal z≤n y≤z = y≤z
⊔-universal (s≤s x≤z) z≤n = s≤s x≤z
⊔-universal (s≤s x≤z) (s≤s y≤z) = s≤s (⊔-universal x≤z y≤z)

mono-⊔ : {f : ℕ → ℕ}
  → f Preserves _≤_ ⟶ _≤_
  → {x y : ℕ} → f (x ⊔ y) ≡ f x ⊔ f y
mono-⊔ mono {x} {y} with compare x y
mono-⊔ {f} mono {x} {y} | tri< x<y _ _ = ≡.trans lemma₁ lemma₂
 where
  lemma₁ : f (x ⊔ y) ≡ f y
  lemma₂ : f y ≡ f x ⊔ f y
  lemma₁ = cong f (≤-⊔ x y (ℕProp.≤⇒pred≤ x<y))
  lemma₂ = ≡.sym (≤-⊔ (f x) (f y) (mono (ℕProp.≤⇒pred≤ x<y)))
mono-⊔ {f} mono {x} {.x} | tri≈ _ ≡.refl _ = ≡.trans (cong f (x⊔x≡x x)) (≡.sym (x⊔x≡x (f x)))
mono-⊔ {f} mono {x} {y} | tri> _ _ y<x = ≡.trans lemma₁ lemma₂
 where
  lemma₁ : f (x ⊔ y) ≡ f x
  lemma₂ : f x ≡ f x ⊔ f y
  lemma₁ = cong f (≡.trans (⊔.comm x y) (≤-⊔ y x (ℕProp.≤⇒pred≤ y<x)))
  lemma₂ = ≡.sym (≡.trans (⊔.comm (f x) (f y)) (≤-⊔ (f y) (f x) (mono (ℕProp.≤⇒pred≤ y<x))))

maximum : {n : ℕ} → Vec ℕ n → ℕ
maximum = foldr (const ℕ) _⊔_ 0

maximum-is : {n : ℕ} → (xs : Vec ℕ n) → (i : Fin n) → lookup i xs ≤ maximum xs
maximum-is [] ()
maximum-is (x ∷ xs) zero = m≤m⊔n x _
maximum-is (x ∷ xs) (suc i) = begin
  lookup (suc i) (x ∷ xs)
    ≡⟨ ≡.refl ⟩
  lookup i xs
    ≤⟨ maximum-is xs i ⟩
  maximum xs
    ≤⟨ m≤n⊔m _ x ⟩
  x ⊔ maximum xs
    ≡⟨ ≡.refl ⟩
  maximum (x ∷ xs) ∎
 where
  open ℕProp.≤-Reasoning

maximum-universal : {n : ℕ} → (xs : Vec ℕ n) → (m : ℕ) → ((i : Fin n) → lookup i xs ≤ m) → maximum xs ≤ m
maximum-universal [] _ _ = z≤n
maximum-universal (x ∷ xs) m f = ⊔-universal (f zero) (maximum-universal xs m (λ i → f (suc i)))

maximum-universal< : {n : ℕ} → (xs : Vec ℕ n) → (m : ℕ) → 0 < m → ((i : Fin n) → lookup i xs < m) → maximum xs < m
maximum-universal< [] _ le _ = le
maximum-universal< (x ∷ xs) (suc m) (s≤s m≤n) f = s≤s (maximum-universal (x ∷ xs) m (λ i → ℕProp.pred-mono (f i)))

-- I think this is unused.
maximum-map-mono : {n : ℕ}{f : ℕ → ℕ}
  → (f Preserves _≤_ ⟶ _≤_)
  → (xs : Vec ℕ (suc n))
  → maximum (map f xs) ≡ f (maximum xs)
maximum-map-mono {zero}{f} mono (x ∷ []) = begin
  f x ⊔ 0
    ≡⟨ proj₂ ⊔.identity (f x) ⟩
  f x
    ≡⟨ cong f (≡.sym (proj₂ ⊔.identity x)) ⟩
  f (x ⊔ 0) ∎
 where
  open ≡-Reasoning
maximum-map-mono {suc _}{f} mono (x ∷ xs) = ≡.sym $ begin
  f (x ⊔ maximum xs)
    ≡⟨ mono-⊔ mono ⟩
  f x ⊔ f (maximum xs)
    ≡⟨ cong (λ y → f x ⊔ y) (≡.sym (maximum-map-mono mono xs)) ⟩
  f x ⊔ (maximum (map f xs)) ∎
 where
  open ≡-Reasoning

map-map : {A B C : Set}{n : ℕ}
  → (g : B → C)(f : A → B)(xs : Vec A n)
  → map g (map f xs) ≡ map (g ∘′ f) xs
map-map g f [] = ≡.refl
map-map g f (x ∷ xs) = cong (_∷_ (g (f x))) (map-map g f xs)
