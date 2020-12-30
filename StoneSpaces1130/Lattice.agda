module Lattice where

open import BasicTypes
open import Poset

record JSL {A : Set} {_≤_ : Rel A} (po : PO _≤_) : Set where
  open PO po
  infix 25 _∨_
  field
    _∨_ : A → A → A
    ∨-join : ∀ {x y : A} → ⋁ (pairSet x y) (x ∨ y)
    O : A
    O-join : ⋁ empty O

  Omin : ∀ {x : A} → O ≤ x
  Omin {x} = p2 O-join λ {s} bot → exFalso bot

  Ounique : ∀ {x : A} → x ≤ O → x ≡ O
  Ounique {x}  xlessO = ≤-asymm xlessO Omin

  ub1 : ∀ {x y : A} → x ≤ (x ∨ y)
  ub1  = p1 ∨-join (in1 refl)

  ub2 : ∀ {x y : A} → y ≤ (x ∨ y)
  ub2 = p1 ∨-join (in2 refl)

  lub : ∀ {x y z : A} → x ≤ z → y ≤ z → (x ∨ y) ≤ z
  lub {x} {y} {z} = λ xlessz → λ ylessz → p2 ∨-join
          λ {s} → λ seqxorseqy → case seqxorseqy (λ seqx → equle xlessz seqx)
          λ seqy → equle ylessz seqy

  ∨-idem  : ∀ {a : A} → a ∨ a ≡ a
  ∨-idem {a} = ≤-asymm (lub ≤-refl ≤-refl)
                       ub1

  ∨-comm  : ∀ {a b : A} → a ∨ b ≡ b ∨ a
  ∨-comm = ≤-asymm (lub ub2 ub1)
                   (lub ub2 ub1)

  ∨-assoc : ∀ {a b c : A} → (a ∨ b) ∨ c ≡ a ∨ (b ∨ c)
  ∨-assoc = ≤-asymm (lub (lub ub1 (ub1 ؛ ub2)) (ub2 ؛ ub2))
                    (lub (ub1 ؛ ub1) (lub (ub2 ؛ ub1) ub2))

  ∨-unit : ∀ {a : A} → a ∨ O ≡ a
  ∨-unit = ≤-asymm (lub ≤-refl Omin)
                     ub1


  ∨-cong : ∀ {a b a' b' : A} → a ≡ a' → b ≡ b' → (a ∨ b) ≡ (a' ∨ b')
  ∨-cong refl refl = refl

  ∨-congL : ∀ {a a' b : A} → a ≡ a' → (a ∨ b) ≡ (a' ∨ b)
  ∨-congL aeqap = ∨-cong aeqap refl

  ∨-congR : ∀ {a b b' : A} → b ≡ b' → (a ∨ b) ≡ (a ∨ b')
  ∨-congR = ∨-cong refl

  _≡∨≡_ : ∀ {a b a' b' : A} → a ≡ a' → b ≡ b' → (a ∨ b) ≡ (a' ∨ b')
  _≡∨≡_ = ∨-cong
  ≡∨_ : ∀ {a a' b : A} → a ≡ a' → (a ∨ b) ≡ (a' ∨ b)
  ≡∨_ = ∨-congL
  ∨≡_ : ∀ {a b b' : A} → b ≡ b' → (a ∨ b) ≡ (a ∨ b')
  ∨≡_ = ∨-congR

  pluginequal : ∀ {a b : A} → (a ∨ b) ≡ b → a ≤ b
  pluginequal aorbeqb = ub1 ؛ (equplug refl aorbeqb)

  ∨to≤    : ∀ {a b : A} → a ∨ b ≡ b ⇔ a ≤ b
  ∨to≤   =  (λ aorbeqb → pluginequal aorbeqb) ,
            (λ aleb → ≤-asymm (lub aleb ≤-refl) ub2)

record MSL {A : Set} {_≤_ : Rel A} (po : PO _≤_) : Set where
  open PO po
  infix 25 _∧_
  field
    _∧_ : A → A → A
    ∧-meet : ∀ {x y : A} → ⋀ (pairSet x y) (x ∧ y)
    I : A
    I-meet : ⋀ empty I

  Imax : ∀ {x : A} → x ≤ I
  Imax = p2 I-meet exFalso

  lb1 : ∀ {x y : A} → x ≥ (x ∧ y)
  lb1 = p1 ∧-meet (in1 refl)

  lb2 : ∀ {x y : A} → y ≥ (x ∧ y)
  lb2 = p1 ∧-meet (in2 refl)

  -- equplug : ∀ {a b c : A} → a ≡ b → b ≡ c → c ≥ a
  -- equplug refl refl = ≤-refl

  glb : ∀ {a b c : A} → a ≥ c → b ≥ c → (a ∧ b) ≥ c
  glb {a} {b} {c} clea cleb = p2 ∧-meet λ bub → case bub
    (λ seqa → clea ؛ (equplug refl (symm seqa)))
    (λ seqb → cleb ؛ (equplug refl (symm seqb)))

  decry : ∀ {a b c : A} → c ≡ b → (a ∧ b) ≤ c
  decry {a} {b} {c} = λ cequb → p1 ∧-meet (in2 cequb)

  leftti : ∀ {a b c : A} → c ≡ a → (a ∧ b) ≤ c
  leftti {a} {b} {c} = λ cequb → p1 ∧-meet (in1 cequb)

  ∧to≤ : ∀ {a b : A} → a ∧ b ≡ a ⇔ b ≥ a

  ∧to≤ = (λ abeqa → equlep lb2 (symm abeqa)) ,
         (λ aleb → ≤-asymm lb1 (glb ≤-refl aleb))

  ∧-unit : ∀ {a : A} → (a ∧ I) ≡ a
  ∧-unit {a} = ≤-asymm lb1 (glb ≤-refl Imax)

  ∧-cong : ∀ {a b a' b' : A} → a ≡ a' → b ≡ b' → (a ∧ b) ≡ (a' ∧ b')
  ∧-cong refl refl = refl
  ∧-congL : ∀ {a a' b : A} → a ≡ a' → (a ∧ b) ≡ (a' ∧ b)
  ∧-congL aeqap = ∧-cong aeqap refl
  ∧-congR : ∀ {a b b' : A} → b ≡ b' → (a ∧ b) ≡ (a ∧ b')
  ∧-congR = ∧-cong refl

  _≡∧≡_ : ∀ {a b a' b' : A} → a ≡ a' → b ≡ b' → (a ∧ b) ≡ (a' ∧ b')
  refl ≡∧≡ refl = refl

  ≡∧_ : ∀ {a a' b : A} → a ≡ a' → (a ∧ b) ≡ (a' ∧ b)
  ≡∧ p = p ≡∧≡ refl

  ∧≡_ : ∀ {a b b' : A} → b ≡ b' → (a ∧ b) ≡ (a ∧ b')
  ∧≡ p = refl ≡∧≡ p

  ∧-idem : ∀ {a : A} → a ∧ a ≡ a
  ∧-idem {a} = ≤-asymm lb1 (glb ≤-refl ≤-refl)

  ∧-comm : ∀ {a b : A} → (a ∧ b) ≡ (b ∧ a)
  ∧-comm {a} {b} = ≤-asymm (glb lb2 lb1) (glb lb2 lb1)

  ∧-assoc : ∀ {a b c : A} → ((a ∧ b) ∧ c) ≡ (a ∧ (b ∧ c))
  ∧-assoc {a} {b} {c} = ≤-asymm (glb (lb1 ؛ lb1) (glb (lb1 ؛ lb2) lb2))
                                (glb (glb lb1 (lb2 ؛ lb1)) (lb2 ؛ lb2))


--  intra : ∀ { a : A} → a ∪ a ≡ a

record LAT {A : Set} {_≤_ : Rel A} (po : PO _≤_) : Set where
  open PO po
  field
    jsl : JSL po
    msl : MSL po

  open JSL jsl public
  open MSL msl public

  dis1 : ∀ {a b c : A} → (a ∧ c) ∨ (b ∧ c) ≤ (a ∨ b) ∧ c
  dis1 = (glb (lub ((lb1) ؛ (ub1)) ((lb1 ) ؛ (ub2 ))) (lub (lb2) (lb2 )))
  dis2 : ∀ {a b c : A} → (a ∧ b) ∨ c ≤ (a ∨ c) ∧ (b ∨ c)
  dis2 = (glb (lub ((lb1) ؛ (ub1)) (ub2)) (lub ((lb2) ؛ (ub1 )) (ub2 )))

  ab1 : ∀ {a b : A} → a ∧ (a ∨ b) ≡ a
  ab1 {a} {b} = ≤-asymm (leftti refl) (glb ≤-refl ub1)
  ab2 : ∀ {a b : A} → a ∨ (a ∧ b) ≡ a
  ab2 {a} {b} = ≤-asymm (lub ≤-refl lb1) ub1

  dualdist : (∀ {a b c : A} → ( a ∧ (b ∨ c) ≡ (a ∧ b) ∨ (a ∧ c) ) ) →
             (∀ {a b c : A} → ( a ∨ (b ∧ c) ≡ (a ∨ b) ∧ (a ∨ c)))
  dualdist h1 {a} {b} {c} =
    ~ (tran (( (a ∨ b) ∧ a) ∨ ((a ∨ b) ∧ c))
                            (
                              (
                              h1 ∶
                              ≡∨ (∧-comm ∶ ab1) ∶
                              ∨≡ ∧-comm ∶
                              ∨≡ h1 ∶
                              ∨≡ (∧-comm ≡∨≡ ∧-comm) ∶ (~ ∨-assoc) ∶ ∨-assoc) ∶
                            (
                            ~ ((∧-comm ∶ ab1) ≡∨≡
                            (∧-comm ∶
                            (h1 ∶ (∧-comm ≡∨≡ ∧-comm))))))
                            ((≡∨ (∧-comm ∶  ab1)) ∶
                             (∨≡ ∧-comm ∶
                             (∨≡ h1 ∶
                             (~ ∨-assoc ∶
                             (≡∨ (∨≡ ∧-comm ∶ ab2) ∶ ∨≡ ∧-comm))))))
                            -- (∨-cong (tran (a ∧ (a ∨ b)) ∧-comm ab1) {!   !}))
  ∧-mono : ∀ {a1 a2 b1 b2 : A} → a1 ≤ a2 → b1 ≤ b2 → a1 ∧ b1 ≤ a2 ∧ b2
  ∧-mono a* b* = glb (lb1 ؛ a*) (lb2 ؛ b*)

-- Distributive Lattices
record DLAT {A : Set} {_≤_ : Rel A} (po : PO _≤_) : Set where
  open PO po
  field
    lat : LAT po
  open LAT lat public

  -- Agda allows different fields of the record to be listed non-consecutively
  -- This is useful when you need to intersperse definitions or open modules
  field
    dist1 : ∀ {a b c : A} → (a ∨ b) ∧ c ≤ (a ∧ c) ∨ (b ∧ c)
    dist2 : ∀ {a b c : A} → (a ∧ b) ∨ c ≥ (a ∨ c) ∧ (b ∨ c)

  ∨-mono : ∀ {a1 a2 b1 b2 : A} → a1 ≤ a2 → b1 ≤ b2 → a1 ∨ b1 ≤ a2 ∨ b2
  ∨-mono a* b* = lub (a* ؛ ub1) (b* ؛ ub2)

  ∧-bot : ∀ {a : A} → (a ∧ O) ≡ O
  ∧-bot = ≤-asymm lb2 Omin

  ∨-top : ∀ {a : A} → (a ∨ I) ≡ I
  ∨-top = ≤-asymm Imax ub2



  supereq : ∀ {a b c d : A} → a ≤ c → c ≡ d → d ≤ b → a ≤ b
  supereq alec cequd dleb = alec ؛ (equplug cequd refl) ؛ dleb


  -- ∧eq∨-reflecto : ∀ {a b : A} → a ∧ b ≡ a ∨ b → a ≡ b
  -- ∧eq∨-reflecto aandbequaorb = ≤-asymm (equle2 (≤-asymm {!   !} {!   !}) lb2) (equle2 {!   !} lb1)

  ∧eq∨-reflect : ∀ {a b : A} → a ∧ b ≡ a ∨ b → a ≡ b
  ∧eq∨-reflect aandbequaorb = ≤-asymm (supereq ub1 (symm aandbequaorb) lb2)
                                      (supereq ub2 (symm aandbequaorb) lb1)

  truefight : ∀ {a x y : A} → a ∧ x ≤ a ∧ y → a ∨ x ≤ a ∨ y → (a ∨ x) ∧ (a ∧ x) ≤ (a ∨ y) ∧ (a ∧ y)
  truefight {a} {x} {y} aandxleaandy aorxleaory = glb (lb1 ؛ aorxleaory) (lb2 ؛ aandxleaandy)

  ∧-squish : ∀ {x a : A} → x ∧ (a ∧ x) ≡ a ∧ x
  ∧-squish {x} {a} = tran ((a ∧ x) ∧ x) ∧-comm
                    (tran (a ∧ (x ∧ x)) ∧-assoc (∧-congR ∧-idem))

  superdist1 : ∀ {a b c : A} → (a ∨ b) ∧ c ≡ (a ∧ c) ∨ (b ∧ c)
  superdist1 = ≤-asymm dist1 dis1

  superdist2 : ∀ {a b c : A} → (a ∧ b) ∨ c ≡ (a ∨ c) ∧ (b ∨ c)
  superdist2 = ≤-asymm dis2 dist2

  ∨-alg-comp : ∀ {a b c : A} → a ≡ b → a ∨ c ≡ b ∨ c
  ∨-alg-comp {a} {.a} {c} refl = refl



  ∧-alg-comp : ∀ {a b c : A} → a ≡ b → a ∧ c ≡ b ∧ c
  ∧-alg-comp {a} {.a} {c} refl = refl



--  modLemma : ∀ {a x y : A} → a ∧ x ≤ a ∧ y → a ∨ x ≤ a ∨ y → x ≤ y
--  modLemma aandxleaandy aorxleaory = ≤-tran {!   !} (≤-tran aandxleaandy lb2)
  modLemma : ∀ {a x y : A} → a ∧ x ≤ a ∧ y → a ∨ x ≤ a ∨ y → x ≤ y
  modLemma {a} {x} {y} aandxleaandy aorxleaory = equle3 ab1 refl
                                                 (≤-tran (∧-mono ≤-refl (≤-tran (equle3 ∨-comm refl ≤-refl) aorxleaory))
                                                 (equle3 ∧-comm refl
                                                (equle3 (≤-asymm dis1 dist1) refl (lub
                                                  (equle3 (tran ((a ∧ x) ∨ (a ∧ x)) refl ∨-idem) ab2
                                                  (≤-tran (equle3 (tran ((a ∧ (a ∧ x)) ∨ (x ∧ (a ∧ x))) refl (∨-cong
                                                  (tran ((a ∧ a) ∧ x) (symm ∧-assoc) (∧-congL ∧-idem)) ∧-squish)) (tran ((y ∧ a) ∨ (y ∧ a)) (symm refl) ∨-idem)
                                                  (equle3 (symm (≤-asymm dis1 dist1)) (tran ((a ∧ (a ∧ y)) ∨ (y ∧ (a ∧ y))) refl (∨-cong
                                                    (tran ((a ∧ a) ∧ y) (symm ∧-assoc) (tran (a ∧ y) (∧-congL ∧-idem) ∧-comm))
                                                    (tran ((a ∧ y) ∧ y) ∧-comm (tran (a ∧ y) (tran (a ∧ (y ∧ y)) ∧-assoc (∧-congR ∧-idem)) ∧-comm))))
                                                  (equle3 refl (≤-asymm dist1 dis1) (glb (≤-tran lb1 aorxleaory) (≤-tran (≤-tran lb2 ≤-refl) aandxleaandy))))) ub2)) lb1))))
--  modLemma aandxleaandy aorxleaory = ≤-tran ub2 (≤-tran (≤-tran aorxleaory (≤-tran (glb {!   !} {!   !}) aandxleaandy)) lb2)
--  modLemma aandxleaandy aorxleaory = equle2 (symm ab1) (≤-tran lb2 (≤-tran (equle2 ∨-comm aorxleaory) (equle
--                                   (≤-tran {!   !} {!   !}) ∨-comm)))

  modLemma2 : ∀ {a x y : A} → a ∧ x ≡ a ∧ y → a ∨ x ≡ a ∨ y → x ≡ y
  modLemma2 {a} {x} {y} aandxequaandy aorxequaory = tran (x ∧ (x ∨ a)) (symm ab1) (tran (x ∧ (a ∨ x)) (∧-congR ∨-comm)
                                                   (tran (x ∧ (a ∨ y)) (∧-congR aorxequaory)
                                                   (tran ((x ∨ (x ∧ a)) ∧ (a ∨ y)) (∧-congL (symm ab2))
                                                   (tran ((x ∨ (a ∧ x)) ∧ (a ∨ y)) (∧-congL (∨-congR ∧-comm))
                                                   (tran ((x ∨ (a ∧ y)) ∧ (a ∨ y)) (∧-congL (∨-congR aandxequaandy))
                                                   (tran (((a ∧ y) ∨ x) ∧ (a ∨ y)) (∧-congL ∨-comm)
                                                   (tran (((a ∨ x) ∧ (y ∨ x)) ∧ (a ∨ y))
                                                   (∧-congL (≤-asymm dis2 dist2))
                                                   (tran (((a ∨ x) ∧ (x ∨ y)) ∧ (a ∨ y)) (∧-congL (∧-congR ∨-comm))
                                                   (tran ((a ∨ x) ∧ ((x ∨ y) ∧ (a ∨ y))) ∧-assoc
                                                   (tran ((a ∨ x) ∧ ((x ∧ a) ∨ y)) (∧-congR (symm (≤-asymm dis2 dist2)))
                                                   (tran (y ∧ (y ∨ a))
                                                   (tran ((y ∨ (y ∧ a)) ∧ (x ∨ a))
                                                   (tran ((x ∨ a) ∧ ((x ∧ a) ∨ y)) (∧-congL ∨-comm)
                                                   (tran (((x ∧ a) ∨ y) ∧ (x ∨ a)) ∧-comm
                                                   (∧-congL (tran (y ∨ (x ∧ a)) ∨-comm (∨-congR
                                                   (tran (a ∧ y)
                                                   (tran (a ∧ x) ∧-comm aandxequaandy) ∧-comm))))))
                                                  (∧-cong ab2 (tran (a ∨ x) ∨-comm
                                                   (tran (a ∨ y) aorxequaory ∨-comm)))) ab1)))))))))))
  modLemma3 : ∀ {a b c x y : A} → x ∧ a ≡ b → x ∨ a ≡ c → y ∧ a ≡ b → y ∨ a ≡ c → x ≡ y
  modLemma3 {a} {b} {c} {x} {y} xandaequb xoraequc yandaequb yoraequc = tran (x ∧ (x ∨ a)) (symm ab1)
                                                                       (tran ((x ∨ (x ∧ a)) ∧ (x ∨ a)) (∧-congL (symm ab2))
                                                                       (tran (((x ∧ a) ∨ x) ∧ (x ∨ a)) (∧-congL ∨-comm)
                                                                       (tran (((y ∧ a) ∨ x) ∧ (x ∨ a)) (∧-congL (∨-congL (tran b xandaequb (symm yandaequb))))
                                                                       (tran (((y ∨ x) ∧ (a ∨ x)) ∧ (x ∨ a)) (∧-congL (≤-asymm dis2 dist2))
                                                                       (tran (y ∧ (y ∨ a))
                                                                       (tran ((y ∨ (y ∧ a)) ∧ (y ∨ a))
                                                                       (tran ((y ∨ (x ∧ a)) ∧ (y ∨ a))
                                                                       (tran (((x ∧ a) ∨ y) ∧ (y ∨ a))
                                                                       (tran (((x ∨ y) ∧ (a ∨ y)) ∧ (y ∨ a))
                                                                       (tran (((y ∨ x) ∧ c) ∧ c) (∧-cong (∧-congR (tran (x ∨ a) ∨-comm xoraequc)) xoraequc)
                                                                       (∧-cong (∧-cong ∨-comm (symm (tran (y ∨ a) ∨-comm yoraequc))) (symm yoraequc)))
                                                                       (∧-congL (≤-asymm dist2 dis2))) (∧-congL ∨-comm)) (∧-congL (∨-congR
                                                                       (tran b xandaequb (symm yandaequb))))) (∧-congL ab2)) ab1)))))

  xequxmeety : ∀ {a b c : A} → ∀ {x y : A} → (x ∧ a ≡ b) → (x ∨ a ≡ c) → (y ∧ a ≡ b) → (y ∨ a ≡ c) → x ≤ x ∧ y
  xequxmeety {a} {b} {c} {x} {y} xandaequb xoraequc yandaequb yoraequc =
    equle2 {b = ((y ∨ a) ∧ x)}
      (
      tran (x ∧ (x ∨ a)) (symm ab1)
      (tran (x ∧ c) (∧-congR xoraequc)
      (tran (x ∧ (y ∨ a)) (∧-congR (symm yoraequc))
      ∧-comm
      ))) (≤-tran
        dist1 (glb (lub lb2 lb2) (lub lb1 (equle2
          (tran (x ∧ a) ∧-comm (tran b xandaequb (symm yandaequb)))
          lb1))))

  uniquecomp : ∀ {a b c : A} → ∀ {x y : A} → (x ∧ a ≡ b) → (x ∨ a ≡ c) → (y ∧ a ≡ b) → (y ∨ a ≡ c) → x ≡ y
  uniquecomp {a} {b} {c} {x} {y} xandaequb xoraequc yandaequb yoraequc =
    ≤-asymm (≤-tran (xequxmeety xandaequb xoraequc yandaequb yoraequc) lb2) (≤-tran (xequxmeety yandaequb yoraequc xandaequb xoraequc) lb2)
  ∁ : A → Pred A
  ∁ a = λ x → (x ∧ a ≡ O) × (x ∨ a) ≡ I

  ∁-unique : ∀ {a : A} → ∀ (x y : A) → ∁ a x → ∁ a y → x ≡ y
  ∁-unique x y (cx1 , cx2) (cy1 , cy2) = uniquecomp cx1 cx2 cy1 cy2

  ∁-unique2 : ∀ {a : A} → ∀ (x y : A) → ∁ a x → ∁ a y → x ≡ y
  ∁-unique2 x y cax cay = modLemma3 (p1 cax) (p2 cax) (p1 cay) (p2 cay)
