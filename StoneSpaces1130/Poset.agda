module Poset where

open import BasicTypes

-- Poset is a property of a relation: it's true if the given relation _≤_
-- is reflexive, antisymmetric, and transitive
-- Rel A = A → A → Set is defined at the end of BasicTypes

record PO {A : Set} (_≤_ : Rel A) : Set where
  infixr 12 _؛_
  field
    ≤-refl : ∀ {a : A} → a ≤ a
    -- ؛ is \;
    ≤-tran : ∀ {a b c : A} → a ≤ b → b ≤ c → a ≤ c
    ≤-asymm : ∀ {a b : A} → a ≤ b → b ≤ a → a ≡ b

  _؛_ : ∀ {a b c : A} → a ≤ b → b ≤ c → a ≤ c
  _؛_ = ≤-tran

  -- the opposite ordering
  _≥_ : A → A → Set
  x ≥ y = y ≤ x

  -- is also a partial order
  po' : PO _≥_
  po' = record { ≤-refl = ≤-refl
               ; ≤-tran = λ ba cb → cb ؛ ba
               ; ≤-asymm = λ blea aleb → ≤-asymm aleb blea }

  -- The following section proves properties of joins
  --
  UpperBound : (A → Set) →  A → Set
  UpperBound S a = ∀ {s : A} → S s → s ≤ a

  ⋁ : Pred A → Pred A
  ⋁ S a =  (UpperBound S a) × (∀ {b : A} → UpperBound S b → a ≤ b)

  ⋁-unique : ∀ {S : A → Set} → (a b : A) → ⋁ S a → ⋁ S b → a ≡ b
  ⋁-unique  a b joina joinb = ≤-asymm (p2 joina (p1 joinb))
                                      (p2 joinb (p1 joina))

  -- The following section proves properties of meets
  --
  LowerBound : (A → Set) → A → Set
  LowerBound S a = ∀ {s : A} → S s → a ≤ s

  ⋀ : (A → Set) → A → Set
  ⋀ S a = (LowerBound S a) ×
          (∀ {c : A} → LowerBound S c → c ≤ a)

  ⋀-unique : ∀ {S : A → Set} → (a b : A) → ⋀ S a → ⋀ S b → a ≡ b
  ⋀-unique = λ a b meeta meetb → ≤-asymm (p2 meetb (p1 meeta)) (p2 meeta (p1 meetb))

  -- Lemmas
  equle : ∀ {a b c : A} → a ≤ c → b ≡ a → b ≤ c
  equle alessc refl = alessc

  equplug : ∀ {a b c : A} → a ≡ b → b ≡ c → a ≤ c
  equplug refl refl = ≤-refl

  equlep : ∀ {a b c : A} → a ≤ c → b ≡ a → b ≤ c
  equlep alessc refl = alessc

  equle2 : ∀ {a b c : A} → a ≡ b → b ≤ c → a ≤ c
  equle2 refl blec = blec

  equle3 : ∀ {a b c d : A} → a ≡ b → c ≡ d → a ≤ c → b ≤ d
  equle3 refl refl alec = alec
