module StoneSpaces where

open import BasicTypes
open import Poset
open import Lattice
open import Boolean
-- open import Heyting

-- Write \_ for subscript, \^ for superscript
PO-Eq : ∀ {A : Set} {_≤₁_ _≤₂_ : A → A → Set}
           → _≤₁_ ≃ _≤₂_ → PO _≤₁_ → PO _≤₂_
PO-Eq {A} {_≤₁_} {_≤₂_} (h12 , h21) po =
  record { ≤-refl = h12 ≤-refl;
           ≤-tran = λ ab bc → h12 (≤-tran (h21 ab) (h21 bc)) ;
           ≤-asymm = λ ab ba → ≤-asymm (h21 ab) (h21 ba) }
      where open PO po

PO-EqIff : ∀ {A : Set} {_≤₁_ _≤₂_ : A → A → Set}
              → _≤₁_ ≃ _≤₂_ → PO _≤₁_ ⇔ PO _≤₂_
PO-EqIff {A} {R} {Q} (RQ , QR) = (λ po → PO-Eq {A} {R} {Q} (RQ , QR) po)
                                  , (λ po → PO-Eq {A} {Q} {R} (QR , RQ) po)
-- \simeq
-- _≃_ : ∀ {A : Set} → Rel A → Rel A → Set
-- R ≃ Q = (∀ {x} {y} → R x y → Q x y) × (∀ {x} {y} → Q x y → R x y)

MSL-Eq : ∀ {A : Set} (_≤_ : A → A → Set) (po1 po2 : PO _≤_)
         → MSL po1 → MSL po2
MSL-Eq {A} _≤_ po1 po2 record { _∧_ = _∧_ ; ∧-meet = ∧-meet ; I = I ; I-meet = I-meet }
                     = record { _∧_ = _∧_ ; ∧-meet = ∧-meet ; I = I ; I-meet = I-meet }

MSL-Eq2 : ∀ {A : Set} (_≤₁_ _≤₂_ : A → A → Set) → (po1 : PO _≤₁_) → (po2 : PO _≤₂_)
          → _≤₁_ ≃ _≤₂_ → MSL po1 → MSL po2
MSL-Eq2 {A} _≤₁_ _≤₂_ po1 po2 (e12 , e21)
        (record { _∧_ = _∧_ ; ∧-meet = ∧-meet ; I = I ; I-meet = I-meet } )
         = record { _∧_ = _∧_ ;
              ∧-meet = λ {x} {y} →
                (λ {s} p → e12 (p1 ∧-meet p ) )
              , λ {c} h → e12 (p2 ∧-meet λ p → e21 (h p) ) ;
                   I = I ;
              I-meet = (exFalso)
                     , (λ {c} h → e12 (p2 I-meet exFalso ) ) }

-- From MSL we can get a JSL in the opposite ordering
msl2jsl : ∀ {A : Set} {_≤_ : A → A → Set} {po : PO _≤_}
            → MSL po → JSL (PO.po' po)
msl2jsl {A} {_≤_} {po} msl =
      record { _∨_ = _∧_ ;
               ∨-join = (λ a → case a
                                 (λ sequx → leftti sequx)
                                 (λ seqy → decry seqy))
                       , λ c → p2 ∧-meet c;
               O = I ;
               O-join = I-meet }
      where open MSL msl

-- Hey! Try to prove JSL to MSL
jsl2msl' : ∀ {A : Set} {_≤_ : A → A → Set} {po : PO _≤_}
            → JSL po → MSL (PO.po' po)
jsl2msl' {A} {_≤_} {po} jsl =
  record { _∧_ = _∨_ ;
        ∧-meet = (λ a → case a (PO.equle po ub1) (PO.equle po ub2)) , p2 ∨-join;
             I = O ;
        I-meet = O-join }
    where open JSL jsl

jsl2msl : ∀ {A : Set} {_≤_ : A → A → Set} {po : PO _≤_} (jsl : JSL po)
            → ∀ (po' : PO (PO._≥_ po)) → MSL po'
jsl2msl {A} {_≤_} {po} jsl po' =
  let msl = jsl2msl' jsl
  in MSL-Eq (PO._≥_ po) (PO.po' po) po' msl

record ICMon (A : Set) : Set where
  infixr 25 _⊙_   -- ⊙ is \o.
  field
    _⊙_ : A → A → A
    e : A
    idem : ∀ {a : A} → a ⊙ a ≡ a
    comm : ∀ {a b : A} → a ⊙ b ≡ b ⊙ a
    assoc : ∀ {a b c : A} → (a ⊙ b) ⊙ c ≡ a ⊙ (b ⊙ c)
    unit : ∀ {a : A} → a ⊙ e ≡ a

  -- Congruence laws: valid in any monoid
  cong : ∀ {a b a' b' : A} → a ≡ a' → b ≡ b' → (a ⊙ b) ≡ (a' ⊙ b')
  cong refl refl = refl
  congL : ∀ {a a' b : A} → a ≡ a' → (a ⊙ b) ≡ (a' ⊙ b)
  congL aeqap = cong aeqap refl
  congR : ∀ {a b b' : A} → b ≡ b' → (a ⊙ b) ≡ (a ⊙ b')
  congR = cong refl

  -- the partial order induced by the monoid
  le : A → A → Set
  le a b = a ⊙ b ≡ b

  lePO : PO le
  PO.≤-refl lePO = idem
  PO.≤-asymm lePO {a} {b} aorbeqb boraeqa =
    tran (a ⊙ b) (tran (b ⊙ a) (symm boraeqa) comm) aorbeqb
  PO.≤-tran lePO {a} {b} {c} aorbeqb borceqc =
    tran (b ⊙ c)
         (tran (a ⊙ (b ⊙ c))
               (congR (symm borceqc))
               (tran ((a ⊙ b) ⊙ c)
                       (symm assoc)
                       (congL aorbeqb)))
         borceqc

  -- with the following line, we let _≤_ be le
  -- and import all definitions from the PO record.
  open PO lePO

  -- all order-related concepts, including ⋁, are now in reference to _≤_ as le
  ⊙-join : ∀ {a b : A} → ⋁ (pairSet a b) (a ⊙ b)
  ⊙-join {a} {b} = (ub , lub) where
    ub : UpperBound (pairSet a b) (a ⊙ b)
    ub (in1 refl) = tran ((a ⊙ a) ⊙ b) (symm assoc) (congL idem)
    ub (in2 refl) = tran ((a ⊙ b) ⊙ b) comm (tran (a ⊙ (b ⊙ b)) assoc (congR idem))
    lub : ∀ {c : A} → UpperBound (pairSet a b) c → le (a ⊙ b) c
    lub {c} h = tran (a ⊙ (b ⊙ c)) assoc
                     (tran ((a ⊙ c)) (congR (h (in2 refl))) (h (in1 refl)))

  e-join : ⋁ empty e
  e-join = (λ x → exFalso x) ,
           (λ x → tran _ comm unit)

  -- From monoid to JSL
  jsl : JSL lePO
  jsl  = record { _∨_ = _⊙_ ;
               ∨-join = ⊙-join;
                    O = e ;
               O-join = e-join}

  -- HEY! Also Try to get MSL from monoid!
  -- msl : MSL
  -- msl = {!   !}

record ALAT (A : Set) : Set where
  field
    join : ICMon A
    meet : ICMon A

  open ICMon join renaming (_⊙_ to _∨_; e to O;
    idem to ∨-idem; comm to ∨-comm; assoc to ∨-assoc; unit to ∨-unit;
    le to _≤_; lePO to po≤; congR to ∨-congR; jsl to jsl1 )
  open ICMon meet renaming (_⊙_ to _∧_; e to I;
    idem to ∧-idem; comm to ∧-comm; assoc to ∧-assoc; unit to ∧-unit;
    le to _≼_; lePO to po≼; congL to ∧-congL; jsl to jsl2 )

  field
    absorp1 : ∀ {a b : A} → a ∧ (a ∨ b) ≡ a
    absorp2 : ∀ {a b : A} → a ∨ (a ∧ b) ≡ a

  order-opposites : ∀ {x y : A} → y ≼ x ⇔ x ≤ y
  order-opposites {x} {y} =
    (λ ygex → tran (y ∨ x) ∨-comm (tran (y ∨ y ∧ x) ((∨-congR (symm ygex))) absorp2)) ,
    (λ xley → tran ((x ∨ y) ∧ x) (∧-congL (symm xley) )
            (tran (x ∧ x ∨ y) ∧-comm absorp1) )

  open PO po≤

  _≽_ : A → A → Set
  _≽_ x y = y ≼ x

  po≽ : PO _≽_
  po≽ = PO.po' po≼

  oopp : _≽_ ≃ _≤_
  oopp = ((λ {x} {y} → p1 order-opposites ) , λ {x} {y} → p2 order-opposites)

  msl≽ : MSL po≽
  msl≽ = jsl2msl' {A} {_≼_} {po≼} jsl2

  lat : LAT po≤
  LAT.jsl lat = jsl1
  LAT.msl lat = MSL-Eq2 _≽_ _≤_ po≽ po≤ oopp msl≽

module LATtoALAT {A : Set} {_≤_ : A → A → Set} {po : PO _≤_} (lat : LAT po) where

  open PO po
  open JSL (LAT.jsl lat)
  open MSL (LAT.msl lat)

  open LAT lat using (ab1; ab2)

  cong : ∀ {a b a' b' : A} → a ≡ a' → b ≡ b' → (a ∨ b) ≡ (a' ∨ b')
  cong refl refl = refl

  pseu : ∀ {a b : A} → a ∧ (a ∨ b) ≡ (a ∧ a) ∨ (a ∧ b)
  pseu {a} {b} =
    tran a ab1 (tran (a ∨ (a ∧ b))
                     (symm ab2)
                     (cong (symm (≤-asymm lb1 (glb ≤-refl ≤-refl))) refl))

  alat : ALAT A
  ALAT.join alat = record
    { _⊙_ = _∨_ ;
        e = O ;
     idem = ∨-idem ;
     comm = ∨-comm ;
    assoc = ∨-assoc ;
     unit = ∨-unit }
  ALAT.meet alat = record
    { _⊙_ = _∧_ ;
        e = I ;
     idem = ∧-idem ;
     comm = ∧-comm ;
    assoc = ∧-assoc ;
     unit = ∧-unit }
  ALAT.absorp1 alat = ab1
  ALAT.absorp2 alat = ab2
  --
  -- record HA : Set where
  --   infix 16 _∪_
  --   infix 16 _∩_
  --   field
  --     _∪_ : A → A → A
  --     _∩_ : A → A → A
  --     𝕚_ : A → A
  --     O : A
  --     I : A
  --
  --     disa : ∀ {a b c : A} → ((a ∪ b) ∩ c) ≡ (a ∩ c) ∪ (b ∩ c)
  --     disb : ∀ {a b c : A} → ((a ∩ b) ∪ c) ≡ (a ∪ c) ∩ (b ∪ c)
  --     O-min : ∀ {a : A} → a ∪ O ≡ a
  --     I-max : ∀ {a : A} → a ∩ I ≡ a
  --     ∪-idem : ∀ {a : A} → a ∪ a ≡ a
