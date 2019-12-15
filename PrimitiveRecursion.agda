module PrimitiveRecursion where

open import Data.Nat using (ℕ; zero; suc; pred; _+_; _∸_; _*_)
open import Data.Fin using (Fin; zero; suc; #_)
open import Data.Vec using (Vec; []; _∷_; [_]; lookup; map)
open import Function using (_$_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; cong; trans; sym; module ≡-Reasoning)

import Data.Nat.Properties as ℕProp

open import Lemmae

-- Primitive recursive functions of arity n
data PrimRec : ℕ → Set where
  pzero : PrimRec 0
  psuc  : PrimRec 1
  pproj : {n : ℕ} → Fin n → PrimRec n
  pcomp : {i o : ℕ} → PrimRec o → Vec (PrimRec i) o → PrimRec i
  prec  : {n : ℕ} → PrimRec n → PrimRec (suc (suc n)) → PrimRec (suc n)

-- Interpretation of primitive recursive functions
mutual
  infixl 4 ⟦_⟧
  ⟦_⟧ : {k : ℕ} → PrimRec k → Vec ℕ k → ℕ
  ⟦ pzero      ⟧ xs       = zero
  ⟦ psuc       ⟧ (n ∷ []) = suc n
  ⟦ pproj i    ⟧ inp      = lookup inp i
  ⟦ pcomp g hs ⟧ inp      = ⟦ g ⟧ (⟦ hs ⟧* inp)
  ⟦ prec g h   ⟧ (zero ∷ inp)  = ⟦ g ⟧ inp
  ⟦ prec g h   ⟧ (suc n ∷ inp) = ⟦ h ⟧ ((⟦ prec g h ⟧ (n ∷ inp)) ∷ n ∷ inp)

  -- This needs to be explicit (rather than a map)
  -- to get the termination checker on side
  ⟦_⟧* : {k i : ℕ} → Vec (PrimRec i) k → Vec ℕ i → Vec ℕ k
  ⟦ [] ⟧*     _   = []
  ⟦ g ∷ gs ⟧* inp = (⟦ g ⟧ inp) ∷ ⟦ gs ⟧* inp

-- Lemmas
⟦-⟧*-map : {k i : ℕ} → (ps : Vec (PrimRec i) k) → (args : Vec ℕ i)
  → ⟦ ps ⟧* args ≡ map (λ p → ⟦ p ⟧ args) ps
⟦-⟧*-map [] args = refl
⟦-⟧*-map (p ∷ ps) args = cong (λ rs → (⟦ p ⟧ args) ∷ rs) (⟦-⟧*-map ps args)

-- Shortcuts
projs : {n m : ℕ} → PrimRec n → Vec (Fin m) n → PrimRec m
projs p ixs = pcomp p (map pproj ixs)

-- Identity
pid : PrimRec 1
pid = pproj (# 0)

pid-is-id : {n : ℕ} → ⟦ pid ⟧ [ n ] ≡ n
pid-is-id = refl

-- Constant
pconst : ℕ → PrimRec 0
pconst zero = pzero
pconst (suc n) = pcomp psuc [ pconst n ]

pone : PrimRec 0
pone = pconst 1

ignore-args : {n : ℕ} → PrimRec 0 → PrimRec n
ignore-args p = pcomp p []

-- Predecessor
ppred : PrimRec 1
ppred = prec pzero (pproj (# 1))

ppred-is-pred : (n : ℕ) → ⟦ ppred ⟧ [ n ] ≡ pred n
ppred-is-pred zero = refl
ppred-is-pred (suc _) = refl

-- Bounded subtraction
pbounded-sub : PrimRec 2
pbounded-sub = projs
  (prec pid (projs ppred [ # 0 ]))
  -- Flip arguments because recursion is on the second
  (# 1 ∷ # 0 ∷ [])

pbounded-sub-is-sub : (m n : ℕ) → ⟦ pbounded-sub ⟧ (m ∷ n ∷ []) ≡ m ∸ n
pbounded-sub-is-sub _ zero = refl
pbounded-sub-is-sub m (suc n) = begin
    ⟦ pbounded-sub ⟧ (m ∷ suc n ∷ [])
      ≡⟨ refl ⟩
    ⟦ ppred ⟧ [ ⟦ pbounded-sub ⟧ (m ∷ n ∷ []) ]
      ≡⟨ ppred-is-pred (⟦ pbounded-sub ⟧ (m ∷ n ∷ [])) ⟩
    pred (⟦ pbounded-sub ⟧ (m ∷ n ∷ []))
      ≡⟨ cong pred (pbounded-sub-is-sub m n) ⟩
    pred (m ∸ n)
      ≡⟨ pred-∸-suc m n ⟩
    m ∸ suc n ∎
  where
    open ≡-Reasoning

-- Addition
padd : PrimRec 2
padd = prec pid (projs psuc [ # 0 ])

padd-is-add : (n m : ℕ) → ⟦ padd ⟧ (n ∷ m ∷ []) ≡ n + m
padd-is-add zero _ = refl
padd-is-add (suc n) m = cong suc (padd-is-add n m)

-- Multiplication
pmul : PrimRec 2
pmul = prec (ignore-args pzero) (projs padd (# 2 ∷ # 0 ∷ []))

pmul-is-mul : (n m : ℕ) → ⟦ pmul ⟧ (n ∷ m ∷ []) ≡ n * m
pmul-is-mul zero _ = refl
pmul-is-mul (suc n) m = trans
    (padd-is-add m (⟦ pmul ⟧ (n ∷ m ∷ [])))
    (cong (_+_ m) (pmul-is-mul n m))

-- Exercise 7
module Exercise7 where
  f : ℕ → ℕ → ℕ → ℕ
  f zero m k = m + k
  f (suc n) m zero = m
  f (suc n) m (suc k) = f n (f (suc n) m k) m

  pf : ℕ → PrimRec 2
  pf zero = padd
  pf (suc n) = projs (prec pid (projs (pf n) (# 0 ∷ # 2 ∷ [])))
    (# 1 ∷ # 0 ∷ [])

  pf-is-f : (n m k : ℕ) → f n m k ≡ ⟦ pf n ⟧ (m ∷ k ∷ [])
  pf-is-f zero m k = sym (padd-is-add m k)
  pf-is-f (suc _) _ zero = pid-is-id
  pf-is-f (suc n) m (suc k) = complete (pf-is-f (suc n) m k)
    where
      complete : {s t : ℕ} → s ≡ t → f n s m ≡ ⟦ pf n ⟧ (t ∷ m ∷ [])
      complete {s} {.s} refl = pf-is-f n s m

-- Exercise 8
pfold : PrimRec 0 → PrimRec 2 → PrimRec 1 → PrimRec 1
pfold z op f = prec z (pcomp op
  (projs f [ # 1 ]
  ∷ pproj (# 0)
  ∷ []))

fold : ℕ → (ℕ → ℕ → ℕ) → (ℕ → ℕ) → ℕ → ℕ
fold z _ _ zero = z
fold z op f (suc n) = op (f n) (fold z op f n)

-- this is a generalisation of the below two but is completely inscrutable
pfold-is-fold : (pz : PrimRec 0)(pop : PrimRec 2)(z : ℕ)(op : ℕ → ℕ → ℕ)
  → ⟦ pz ⟧ [] ≡ z → ((m n : ℕ) → ⟦ pop ⟧ (m ∷ n ∷ []) ≡ op m n)
  → (n : ℕ)(pf : PrimRec 1) → ⟦ pfold pz pop pf ⟧ [ n ] ≡ fold z op (λ k → ⟦ pf ⟧ [ k ]) n
pfold-is-fold _ _ _ _ zeq _ zero _ = zeq
pfold-is-fold pz pop z op zeq opeq (suc n) pf = trans
  (opeq (⟦ pf ⟧ [ n ]) (⟦ pfold pz pop pf ⟧ [ n ]))
  (cong (op (⟦ pf ⟧ [ n ])) (pfold-is-fold _ _ _ _ zeq opeq n _))

psum : PrimRec 1 → PrimRec 1
psum = pfold pzero padd

sum : (ℕ → ℕ) → ℕ → ℕ
sum = fold zero (_+_)

psum-is-sum : (n : ℕ)(p : PrimRec 1) → ⟦ psum p ⟧ [ n ] ≡ sum (λ k → ⟦ p ⟧ [ k ]) n
psum-is-sum zero _ = refl
psum-is-sum (suc n) p = trans
  (padd-is-add (⟦ p ⟧ [ n ]) (⟦ psum p ⟧ [ n ]))
  (cong (_+_ (⟦ p ⟧ [ n ])) (psum-is-sum n p))

pprod : PrimRec 1 → PrimRec 1
pprod = pfold pone pmul

prod : (ℕ → ℕ) → ℕ → ℕ
prod = fold 1 (_*_)

pprod-is-prod : (n : ℕ)(p : PrimRec 1) → ⟦ pprod p ⟧ [ n ] ≡ prod (λ k → ⟦ p ⟧ [ k ]) n
pprod-is-prod zero _ = refl
pprod-is-prod (suc n) p = trans
  (pmul-is-mul (⟦ p ⟧ [ n ]) (⟦ pprod p ⟧ [ n ]))
  (cong (_*_ (⟦ p ⟧ [ n ])) (pprod-is-prod n p))
