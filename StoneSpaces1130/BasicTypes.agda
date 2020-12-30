module BasicTypes where

-- Basic types and basic logic

infix  15 _≡_
infixr 11 _×_
infixr 10 _+_
infixr  5 _⇔_
infixr 13 _∶_

-- Equality and basic type constructors
--
data _≡_ {A : Set} (a : A) : A → Set where
  refl : a ≡ a

symm : ∀ {A} {a b : A} → a ≡ b → b ≡ a
symm refl = refl

-- ~ : ∀ {A} {a b : A} → a ≡ b → b ≡ a
-- ~ refl = refl

~ = symm

-- tran : ∀ {A} {a : A} (b) {c} → a ≡ b → b ≡ c → a ≡ c
tran : ∀ {A} {a c : A} b → a ≡ b → b ≡ c → a ≡ c
tran b refl bc = bc

{-- ∶ is \:  --}
_∶_ : ∀ {A} {a b c : A} → a ≡ b → b ≡ c → a ≡ c
_∶_ {A} {a} {b} {c} ab bc = tran b ab bc


data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B

p1 : ∀ {A B : Set} → A × B → A
p1 (a , b) = a

p2 : ∀ {A B : Set} → A × B → B
p2 (a , b) = b



data _+_ (A B : Set) : Set where
  in1 : A → A + B
  in2 : B → A + B

case : ∀ {A B C : Set} → A + B → (A → C) → (B → C) → C
case (in1 a) f g = f a
case (in2 b) f g = g b

pbreak : ∀ {A B C : Set} → A × B → (A → C) + (B → C) → C
pbreak AandB ACorBC = case ACorBC (λ AC → AC (p1 AandB))
                                  λ BC → BC (p2 AandB)

MP : ∀ {A B C : Set} → A → (A → B) → (B → C) → C
MP A1 A2 A3 = A3 (A2 A1)

data ⊥ : Set where

data ⊤ : Set where
  tt : ⊤

exFalso : ∀ {A : Set} → ⊥ → A
exFalso ()

¬ : Set → Set
¬ A = A → ⊥

--  type \<=>   to enter ⇔
_⇔_ : Set → Set → Set
A ⇔ B = (A → B) × (B → A)


-- Subsets of type A are encoded as predicates on A.
-- A predicate on A is a proposition depending on input x : A.
Pred : Set → Set₁
Pred A = A → Set

-- The empty (sub)set is the predicate which is false on every input.
empty : ∀ {A : Set} → Pred A
empty z = ⊥

-- The singleton set {x} is the predicate that is true
-- whenever the input equals x
singleton : ∀ {A : Set} → A → Pred A
singleton x = λ z → z ≡ x

-- The two-element set {x,y} is the predicate that is true
-- whenever the input equals x, or equals y.
pairSet : ∀ {A : Set} → A → A → Pred A
pairSet x y = λ z → (z ≡ x) + (z ≡ y)

Rel : Set → Set₁
Rel A = A → A → Set

-- \simeq
_≃_ : ∀ {A : Set} → Rel A → Rel A → Set
R ≃ Q = (∀ {x} {y} → R x y → Q x y) × (∀ {x} {y} → Q x y → R x y)
