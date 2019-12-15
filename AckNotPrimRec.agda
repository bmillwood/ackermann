module AckNotPrimRec where

import Algebra
import Relation.Binary
import Data.Nat.Properties as ℕProp

open import Data.Nat using (ℕ; zero; suc;
  _≤_; _<_; z≤n; s≤s;
  pred; _+_; _*_; _⊔_)
open import Data.Fin using (Fin; zero; suc)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.Vec using (Vec; _∷_; []; [_];
  lookup; map)
open import Function using (_∘_; _∘′_; _$_)
open ℕProp using (m≤m⊔n)
module ≡ where
  open import Relation.Binary.PropositionalEquality public
  open ≡-Reasoning public
open ≡ using (_≡_; _≢_; cong)

open import Ackermann
open import Lemmae
open import PrimitiveRecursion

private
  module ≤ = Relation.Binary.DecTotalOrder ℕProp.≤-decTotalOrder

open Algebra.CommutativeSemiring ℕProp.*-+-commutativeSemiring
  using (+-comm)

-- ack-bound f is the proposition that f xs < ack c (maximum xs) for some c
ack-bound : {n : ℕ} → (Vec ℕ n → ℕ) → Set
ack-bound {n} f = Σ ℕ (λ c → (xs : Vec ℕ n) → f xs < ack c (maximum xs))

ack-dominates-psuc : (args : Vec ℕ 1) → ⟦ psuc ⟧ args < ack 1 (maximum args)
ack-dominates-psuc (x ∷ []) = begin
  suc (suc x)
    ≡⟨ ≡.refl ⟩
  ack 0 (suc x)
    ≤⟨ ack-₁dom₂ 0 x ⟩
  ack 1 x
    ≡⟨ cong (ack 1) (≡.sym (proj₂ ⊔.identity x)) ⟩
  ack 1 (x ⊔ 0)
    ≡⟨ ≡.refl ⟩
  ack 1 (maximum [ x ]) ∎
 where
  open ℕProp.≤-Reasoning

ack-dominates-primrec : {n : ℕ}
  → (p : PrimRec n)
  → ack-bound ⟦ p ⟧
ack-dominates-primrec pzero = 0 , λ _ → s≤s z≤n
ack-dominates-primrec psuc = 1 , ack-dominates-psuc
ack-dominates-primrec (pproj i) = 0 , λ args → s≤s (maximum-is args i)
ack-dominates-primrec (pcomp {i}{o} g hs) with ack-dominates-primrec g
... | cg , pg = cf , ccomp
 where
  open ℕProp.≤-Reasoning
  prec-bound : Set
  prec-bound = Σ (PrimRec i) (λ p → ack-bound ⟦ p ⟧)
  -- chs is a map, but writing it as one fails the termination checker
  chs : {o : ℕ} → Vec (PrimRec i) o → Vec prec-bound o
  chs [] = []
  chs (f ∷ fs) = (f , ack-dominates-primrec f) ∷ chs fs
  outputs : Vec ℕ i → Vec ℕ o
  outputs xs = map (λ p → ⟦ proj₁ p ⟧ xs) (chs hs)
  biggest-output : Vec ℕ i → ℕ
  biggest-output xs = maximum (outputs xs)
  lemma : ack-bound biggest-output
  lemma = c (chs hs) , c-works
   where
    c : {n : ℕ} → Vec prec-bound n → ℕ
    c hs = maximum (map (proj₁ ∘ proj₂) hs)
    c-works : (args : Vec ℕ i) → biggest-output args < ack (c (chs hs)) (maximum args)
    c-works args = maximum-universal<
      (outputs args)
      (ack (c (chs hs)) (maximum args))
      (ack-positive (c (chs hs)) (maximum args))
      (each-c-works (chs hs))
     where
      c-mono : {n : ℕ}(b : prec-bound)(bs : Vec prec-bound n) → c bs ≤ c (b ∷ bs)
      c-mono b bs = begin
        c bs
          ≤⟨ m≤n⊔m (c bs) (proj₁ (proj₂ b)) ⟩
        proj₁ (proj₂ b) ⊔ c bs
          ≡⟨ ≡.refl ⟩
        c (b ∷ bs) ∎
      each-c-works : {n : ℕ} (hs : Vec prec-bound n) → (ix : Fin n)
        → lookup (map (λ p → ⟦ proj₁ p ⟧ args) hs) ix < ack (c hs) (maximum args)
      each-c-works [] ()
      each-c-works (h ∷ hs′) zero with proj₂ h
      ... | ch , ph = begin
        suc (⟦ proj₁ h ⟧ args)
          ≤⟨ ph args ⟩
        ack ch (maximum args)
          ≤⟨ ack-nondecreasing₁ (maximum args) (m≤m⊔n ch (c hs′)) ⟩
        ack (ch ⊔ c hs′) (maximum args) ∎
      each-c-works (h ∷ hs′) (suc ix) = begin
        suc (lookup (map (λ p → ⟦ proj₁ p ⟧ args) hs′) ix)
          ≤⟨ each-c-works hs′ ix ⟩
        ack (c hs′) (maximum args)
          ≤⟨ ack-nondecreasing₁ (maximum args) (c-mono h hs′) ⟩
        ack (c (h ∷ hs′)) (maximum args) ∎
  proj-chs : {o : ℕ} → (fs : Vec (PrimRec i) o) → fs ≡ map proj₁ (chs fs)
  proj-chs [] = ≡.refl
  proj-chs (f ∷ fs) = cong (_∷_ f) (proj-chs fs)
  ch : ℕ
  ch = proj₁ lemma
  cf-2 cf-1 cf : ℕ
  cf-2 = cg ⊔ pred ch
  cf-1 = suc cf-2
  cf = 2 + cf-2
  ch≤cf-1 : ch ≤ suc cf-2
  ch≤cf-1 with ch
  ... | zero = z≤n
  ... | suc n = s≤s (m≤n⊔m n cg)
  ccomp : (args : Vec ℕ i) → ⟦ pcomp g hs ⟧ args < ack cf (maximum args)
  ccomp args = begin
    suc (⟦ g ⟧ (⟦ hs ⟧* args))
      ≡⟨ cong (suc ∘′ ⟦ g ⟧) $ ≡.begin
          ⟦ hs ⟧* args
            ≡.≡⟨ cong (λ hs → ⟦ hs ⟧* args) (proj-chs hs) ⟩
          ⟦ map proj₁ (chs hs) ⟧* args
            ≡.≡⟨ ⟦-⟧*-map (map proj₁ (chs hs)) args ⟩
          map (λ h → ⟦ h ⟧ args) (map proj₁ (chs hs))
            ≡.≡⟨ map-map (λ h → ⟦ h ⟧ args) proj₁ (chs hs) ⟩
          map (λ p → ⟦ proj₁ p ⟧ args) (chs hs) ≡.∎ ⟩
    suc (⟦ g ⟧ (map (λ p → ⟦ proj₁ p ⟧ args) (chs hs)))
      ≤⟨ pg (map (λ p → ⟦ proj₁ p ⟧ args) (chs hs)) ⟩
    ack cg (maximum (map (λ p → ⟦ proj₁ p ⟧ args) (chs hs)))
      ≤⟨ ack-nondecreasing₂ cg (ℕProp.≤⇒pred≤ (proj₂ lemma args)) ⟩
    ack cg (ack ch (maximum args))
      ≤⟨ ack-nondecreasing₂ cg (ack-nondecreasing₁ (maximum args) ch≤cf-1) ⟩
    ack cg (ack cf-1 (maximum args))
      ≤⟨ ack-nondecreasing₁ (ack cf-1 (maximum args)) (m≤m⊔n cg (pred ch)) ⟩
    ack cf-2 (ack cf-1 (maximum args))
      ≡⟨ ≡.refl ⟩
    ack cf-1 (suc (maximum args))
      ≤⟨ ack-₁dom₂ cf-1 (maximum args) ⟩
    ack cf (maximum args) ∎
ack-dominates-primrec (prec g h) with ack-dominates-primrec g | ack-dominates-primrec h
... | cg , pg | ch , ph = cf , crec
 where
  open ℕProp.≤-Reasoning
  m-1 m : ℕ
  m-1 = pred cg ⊔ ch
  m = suc m-1
  cf : ℕ
  cf = 2 + m
  helper : (m n : ℕ) → m ≤ suc (pred m ⊔ n)
  helper zero n = z≤n
  helper (suc pm) n = s≤s (m≤m⊔n pm n)
  cg≤m : cg ≤ m
  cg≤m = helper cg ch
  ack-term-wins : (y : ℕ)(xs : Vec ℕ _) → maximum (ack m (y + maximum xs) ∷ y ∷ xs) ≤ ack m (y + maximum xs)
  ack-term-wins y xs = maximum-universal (ack m (y + maximum xs) ∷ y ∷ xs) (ack m (y + maximum xs)) each-term
   where
    each-term : (i : Fin (suc (suc _))) → lookup (ack m (y + maximum xs) ∷ y ∷ xs) i ≤ ack m (y + maximum xs)
    each-term zero = ≤.refl
    each-term (suc zero) = ≤.trans (ℕProp.m≤m+n y (maximum xs)) (ℕProp.≤⇒pred≤ (ack-superlinear m))
    each-term (suc (suc i)) = begin
      lookup xs i
        ≤⟨ maximum-is xs i ⟩
      maximum xs
        ≤⟨ ℕProp.m≤m+n (maximum xs) y ⟩
      maximum xs + y
        ≡⟨ +-comm (maximum xs) y ⟩
      y + maximum xs
        ≤⟨ ℕProp.≤⇒pred≤ (ack-superlinear m) ⟩
      ack m (y + maximum xs) ∎
  lemma : (y : ℕ) → (xs : Vec ℕ _) → ⟦ prec g h ⟧ (y ∷ xs) < ack m (y + maximum xs)
  lemma zero xs = ≤.trans
    (pg xs)
    (ack-nondecreasing₁ (maximum xs) cg≤m)
  lemma (suc y) xs = begin
    suc (⟦ h ⟧ (⟦ prec g h ⟧ (y ∷ xs) ∷ y ∷ xs))
      ≤⟨ ph _ ⟩
    ack ch (maximum (⟦ prec g h ⟧ (y ∷ xs) ∷ y ∷ xs))
      ≤⟨ ack-nondecreasing₂ ch (ℕProp.≤⇒pred≤ (lemma y xs) ⊔-mono ≤.refl) ⟩
    ack ch (maximum (ack m (y + maximum xs) ∷ y ∷ xs))
      ≤⟨ ack-nondecreasing₂ ch (ack-term-wins y xs) ⟩
    ack ch (ack m (y + maximum xs))
      ≤⟨ ack-nondecreasing₁ _ (m≤n⊔m ch (pred cg)) ⟩
    ack m-1 (ack m (y + maximum xs))
      ≡⟨ ≡.refl ⟩
    ack m (suc y + maximum xs) ∎
  +-bound : (m n : ℕ) → m + n ≤ 2 * (m ⊔ n)
  +-bound m n = ℕProp.+-mono-≤ (m≤m⊔n m n) (≤.trans (m≤m⊔n n m) (≤.reflexive (≡.trans (⊔.comm n m) (+-comm 0 (m ⊔ n)))))
  crec : (args : Vec ℕ _) → ⟦ prec g h ⟧ args < ack cf (maximum args)
  crec (y ∷ xs) = begin
    suc (⟦ prec g h ⟧ (y ∷ xs))
      ≤⟨ lemma y xs ⟩
    ack m (y + maximum xs)
      ≤⟨ ack-nondecreasing₂ m (+-bound y (maximum xs)) ⟩
    ack m (2 * maximum (y ∷ xs))
      ≤⟨ ℕProp.≤⇒pred≤ (ack-fastgrowing m (y ⊔ maximum xs)) ⟩
    ack (2 + m) (maximum (y ∷ xs)) ∎

{- this is kind of a trivial and less useful corollary of previous work,
   but if I say, I'm going to write a proof that the ackermann function
   is not primrec, I had better produce a term of this type at the end -}
ack-not-primrec : (p : PrimRec 2) → (λ m n → ⟦ p ⟧ (m ∷ n ∷ [])) ≢ ack
ack-not-primrec p eq with ack-dominates-primrec p
... | cp , pp = <⇒≢ lt eq′
 where
  open ℕProp.≤-Reasoning
  eq′ : ⟦ p ⟧ (cp ∷ cp ∷ []) ≡ ack cp cp
  eq′ = cong (λ f → f cp cp) eq
  lt : ⟦ p ⟧ (cp ∷ cp ∷ []) < ack cp cp
  lt = begin
    suc (⟦ p ⟧ (cp ∷ cp ∷ []))
      ≤⟨ pp (cp ∷ cp ∷ []) ⟩
    ack cp (cp ⊔ (cp ⊔ 0))
      ≡⟨ cong (λ n → ack cp (cp ⊔ n)) (proj₂ ⊔.identity cp) ⟩
    ack cp (cp ⊔ cp)
      ≡⟨ cong (ack cp) (x⊔x≡x cp) ⟩
    ack cp cp ∎
