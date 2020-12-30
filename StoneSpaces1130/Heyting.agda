module Heyting where

open import BasicTypes
open import Poset
open import Lattice public

record HA-Alg {A : Set} {_≤_ : Rel A} (po : PO _≤_) : Set where
  field
    lat : LAT po
  open LAT lat
  open Poset.PO po

  field
    _⇒_ : A → A → A
    ⇒-I : ∀ {a : A} → (a ⇒ a) ≡ I
    ⇒-absorp1 : ∀ {a b : A} → (a ∧ (a ⇒ b) ) ≡ a ∧ b
    ⇒-absorp2 : ∀ {a b : A} → ( b ∧ (a ⇒ b) ) ≡ b
    ⇒-dist : ∀ {a b c : A} → (a ⇒ (b ∧ c)) ≡ (a ⇒ b) ∧ (a ⇒ c)

  addition : ∀ {a b c : A} →  a ≤ b → c ∧ a ≤ c ∧ b
  addition = λ pipo → glb lb1 (≤-tran lb2 pipo)

  add2 : ∀ {a b c : A} → (a ∧ b ≤ a ∧ c) → (b ≤ a) → b ≤ c
  add2 = λ lep bep → ≤-tran (≤-tran (glb bep ≤-refl) lep) lb2

--  equadd less equ = ≤-asymm (≤-tran {!   !} {!   !}) (≤-tran (glb ≤-refl {!   !}) {!   !})
  --  addition2 : ∀ {a b c : A} → (a ≤ b) →  (c ⇒ a) ≤ (c ⇒ b)
  --  addition2 = λ pipo → {!   !}

  ha-parta : ∀ {a b c : A} → c ≤ (a ⇒ b) → c ∧ a ≤ b
  --  ha-parta = λ cleaimpb → equle3 refl {! !} (glb lb2 (≤-tran lb1 cleaimpb))
  ha-parta = (λ cleaimpb →  (equle3 refl ⇒-absorp1 (glb lb2 (≤-tran lb1 cleaimpb))) ؛ lb2)

  --  ⇒rightswitch : ∀ {a b c : A} → ( ( a ∧ c ) ≤ b ) ⇔ ( a ≤ ( c ⇒ b ) )
  --  ⇒rightswitch = (λ at -> add2 {!   !} {!   !}) , ha-parta

  ⇒-cong : ∀ {a b c d : A} → (a ≡ b) → (c ≡ d) → (a ⇒ c) ≡ (b ⇒ d)
  ⇒-cong refl refl = refl
  --  ⇒premono : ∀ {a b b' : A} → (b ≤ b') → ((a ⇒ b) ≤ (a ⇒ b'))
  --  ⇒premono = λ blebp → {!   !}
--  ⇒-lowergreater aleap = p1 ∧to≤ (≤-asymm lb1 (glb ≤-refl (equle3 refl (⇒-cong (p2 ∧to≤ aleap) refl) {!   !})))
--p1 ∧to≤ (≤-asymm lb1 (≤-tran ≤-refl {!   !}))



  ⇒-higherheyting : ∀ {a b b' : A} → (b ≤ b') → (a ⇒ b) ≤ (a ⇒ b')
  ⇒-higherheyting blebp = ≤-tran (glb (p1 ∧to≤ ((symm ⇒-dist) ∶ ⇒-cong refl (p2 ∧to≤ blebp))) ≤-refl) lb1

-- {!   !} ؛ ≤-tran ≤-refl (⇒-higherheyting blepb)
          --≤-tran (equle3 refl ⇒-absorp1 {!   !}) lb1

          --≤-tran (equle3 refl (symm ⇒-absorp1)
          --(equle3 {!   !} refl {!   !} )) lb2
  --  ⇒mono = λ palea blepb → ≤-tran (equle3 refl (symm ⇒-absorp1) (≤-tran {!   !} lb2)) lb2

  --    pawn : ∀ {a b c : A} → (a ≤ b) → (c ⇒ a) ≤ (c ⇒ b)
  --    pawn = λ aleb → {!   !} ؛ {!   !}

  hapartb : ∀ {a b c : A} → c ∧ a ≤ b → c ≤ (a ⇒ b)
  hapartb {a} {b} {c} canda = equle3 ⇒-absorp2 refl (≤-tran lb2 (equle3 ∧-unit refl (equle (equle3 (symm (symm ⇒-dist)) refl (⇒-higherheyting canda)) (∧-congR (symm ⇒-I)))))
  ha : ∀ {a b c : A} → c ≤ (a ⇒ b) ⇔ c ∧ a ≤ b
  ha = (λ cleaimpb → (equle3 refl (⇒-absorp1 ∶ ∧-comm) (≤-tran ≤-refl (equle3 ∧-comm refl (glb lb1 (≤-tran lb2 cleaimpb))))) ؛ lb1) ,
         hapartb
  --  ha-partb : ∀ {a b c : A} → ( (c ∧ a) ≤ b) → ( c ≤ (a ⇒ b) )
  --  ha-partb = λ candaleb → {!   !}

  ⇒-lowergreater : ∀ {a a' b : A} → (a ≤ a') → (a' ⇒ b) ≤ (a ⇒ b)
  ⇒-lowergreater din = p2 ha ((glb lb1 (≤-tran lb2 din)) ؛ (equle lb2 (∧-comm ∶ ⇒-absorp1)))

  ⇒-lessthan : ∀ {a a' b : A} → (a ≤ a') → (((a ∧ a') ∨ a') ⇒ b) ≤ ((a ∧ a') ⇒ b)
  ⇒-lessthan devo = ⇒-lowergreater (≤-refl ؛ ub1)

  ⇒mono : ∀ {a a' b b' : A} → (a ≤ a') → (b ≤ b') → ((a' ⇒ b) ≤ (a ⇒ b') )
  ⇒mono {a} {a'} {b} {b'} alepa blepb = p2 ha (≤-tran (glb lb1 (lb2 ؛ alepa)) (equle3 ∧-comm refl (equle3 (symm ⇒-absorp1) refl (≤-tran lb2 blepb))))
--equle3 ⇒-absorp2 refl (lb2 ؛ (equle3 (symm ((symm ∧-unit) ∶
  --      (∧≡ (symm ⇒-I)) ∶ (symm (⇒-dist)))) refl (⇒mono ≤-refl candaleb) ))
  --  ha = (λ zlexipy → equle3 (≡∧ ⇒-absorp2) refl (equle3 (symm ((≡∧ ∧-comm) ∶ ∧-assoc)) refl lb1 ؛ equle3 (symm ((symm ∧-unit) ∶ (∧≡ (symm ⇒-I)))) refl (equle3 ⇒-dist refl {!   !})))
  --        , λ zandxlexipy → {!   !}

record DHA {A : Set} {_≤_ : Rel A} (po : PO _≤_) : Set where
  field
    lat : LAT po
  open LAT lat
  open Poset.PO po

  field
    _⇒_ : A → A → A
    ⇒-I : ∀ {a : A} → (a ⇒ a) ≡ I
    ⇒-absorp1 : ∀ {a b : A} → (a ∧ (a ⇒ b) ) ≡ a ∧ b
    ⇒-absorp2 : ∀ {a b : A} → ( b ∧ (a ⇒ b) ) ≡ b
    ⇒-dist : ∀ {a b c : A} → (a ⇒ (b ∧ c)) ≡ (a ⇒ b) ∧ (a ⇒ c)
    ha+ : ∀ {x y z : A} → z ≤ (x ⇒ y) → ( z ∧ x ) ≤ y
    ha- : ∀ {x y z : A} → ( z ∧ x ) ≤ y → z ≤ (x ⇒ y)

-- BOOLEAN ALGEBRAS WERE HERE

record HA {A : Set} {_≤_ : Rel A} (po : PO _≤_) : Set where
  field
    lat : LAT po
  open LAT lat
  open Poset.PO po

  field
    _⇒_ : A → A → A
  --  _⊹_ : A → A → A
    ha : ∀ {x y z : A} → z ≤ (x ⇒ y) ⇔ z ∧ x ≤ y

  -_ : A → A
  - a = a ⇒ O

  P₁ : A → A → A → A
  P₁ a b c = ((a ⇒ b) ⇒ c) ∧ ((c ⇒ b) ⇒ a)

  P₂ : A → A → A → A

  P₂ a b c = (b ⇒ (a ∧ c)) ∧ (a ∨ c)

  ha+ : ∀ {x y z : A} → z ≤ (x ⇒ y) → ( z ∧ x ) ≤ y
  ha+  = p1 ha

  ha- : ∀ {x y z : A} → ( z ∧ x ) ≤ y → z ≤ (x ⇒ y)
  ha-  = p2 ha

  --  ⇒-assoc : ∀ {a b : A} → ((a ⇒ b) ⇒ b) ≡ (a ⇒ (b ⇒ b))
  --  ⇒-assoc = ≤-asymm (ha- (ha- (equle3 (symm (∧-assoc ∶ (∧-comm ∶ (∧-assoc ∶ (∧-congR (≤-asymm lb1 (glb ≤-refl (ha- lb1)))))))) refl lb2)))
  --            (ha- (ha+ (ha- {!   !})))

  attempt : ∀ {a b : A} → b ≤ (a ⇒ b)
  attempt = ha- lb1
  --  ⇒-∧-cong : ∀ {a b : A} → (a ∧ (a ⇒ b)) ≡ ((a ∧ a) ⇒ (b ∧ a))
  --  ⇒-∧-cong = ≤-asymm (ha- {!   !}) {!   !}
  ⇒-I : ∀ {a : A} → (a ⇒ a) ≡ I
  ⇒-I = ≤-asymm Imax (ha- lb2)



  ⇒-absorp2 : ∀ {a b : A} → ( b ∧ (a ⇒ b) ) ≡ b
  ⇒-absorp2 = ≤-asymm lb1 (glb ≤-refl (ha- lb1))


  ⇒-absorp1 : ∀ {a b : A} → (a ∧ (a ⇒ b) ) ≡ a ∧ b
  ⇒-absorp1 {a} {b} = ≤-asymm (glb lb1 (equle3 ∧-comm refl (ha+ ≤-refl))) (glb lb1 (lb2 ؛ attempt))
      --                ≤-asymm (equle3 ∧-comm refl (ha+ {!   !} )) (≤-tran (≤-tran (equle3 (symm ((symm ab2) ∶ (refl ∶ refl))) refl (equle3 ∨-comm refl dis2 ؛
      --                equle3 (symm (∧-comm ∶ (∧≡ ∨-idem))) refl ( {!   !} ؛ lb2)))
      --                (equle3 refl (tran ((b ∧ (a ⇒ b)) ∧ a) refl (∧-assoc ∶ (∧-comm ∶ (≡∧ ∧-comm)))) (equle3 refl (≡∧ (symm ⇒-absorp2)) ≤-refl))) lb1)


  ⇒-dist : ∀ {a b c : A} → (a ⇒ (b ∧ c)) ≡ (a ⇒ b) ∧ (a ⇒ c)
  ⇒-dist = ≤-asymm (glb (ha- (equle3 (symm ∧-comm) refl (equle3 (symm (⇒-absorp1 ∶ (∧-comm ∶ ∧-assoc)) ) refl lb1)))
                   (ha- (equle3 (symm ∧-comm) refl (equle3 (symm (⇒-absorp1 ∶ ((symm ∧-assoc) ∶ refl)) ) refl lb2)))) (ha+ (ha- (ha- (glb (equle3 (symm ((∧-congL ∧-comm ∶ ∧-assoc) ∶ refl)) refl
                  (lb2 ؛ (equle3 (symm (∧-comm ∶ ⇒-absorp1)) refl lb2)) )
                                          (equle3 (symm ∧-assoc) refl (lb2 ؛ (equle3 ∧-comm refl (equle3 (symm ⇒-absorp1) refl lb2))) )))))


  --Try these after you finish the ones up above.

--  bottom : ∀ {a : A} → (a ⇒ O) ≡ O
--  bottom = ≤-asymm {!   !} Omin




  dist1 : ∀ {a b c : A} → (a ∨ b) ∧ c ≤ (a ∧ c) ∨ (b ∧ c)
  dist1 = ha+ (lub (ha- ub1) (ha- ub2))
  dist2 : ∀ {a b c : A} → (a ∧ b) ∨ c ≥ (a ∨ c) ∧ (b ∨ c)
  dist2 = equle3 ∧-comm refl (ha+ (lub (ha- (equle3 ∧-comm refl (ha+ (lub (ha- ub1)
          (ha- (≤-tran lb1 ub2))))))
          (ha- (equle3 ((symm ab1) ∶ (symm (∧≡ ∨-comm))) (symm refl) ub2))))
  -- ha+ (lub ( {!   !} ) (ha- (equle3 (symm ((∧≡ ∨-comm) ∶ ab1)) refl ub2)))
  distribute1 : ∀ {a b c : A} → (a ∨ b) ∧ c ≡ (a ∧ c) ∨ (b ∧ c)
  distribute1 = ≤-asymm dist1 dis1

  distribute2 : ∀ {a b c : A} → (a ∧ b) ∨ c ≡ (a ∨ c) ∧ (b ∨ c)
  distribute2 = ≤-asymm dis2 dist2

  ⇒-flip : ∀ {a b : A} → a ≡  b → - a ≡ - b
  ⇒-flip refl = refl
--  ⇒-flop : ∀ {a b : A} → - a ≡ - b → a ≡ b
--  ⇒-flop {a} {b} flap = {!   !}

  ⇒mono : ∀ {a a' b b' : A} → (a ≤ a') → (b ≤ b') → ((a' ⇒ b) ≤ (a ⇒ b') )
  ⇒mono {a} {a'} {b} {b'} alepa blepb = ha- (≤-tran (≤-tran (glb lb1 (lb2 ؛ alepa)) (equle3 ∧-comm refl (equle lb2 ⇒-absorp1))) blepb)

  --  bomp : ∀ {a : A} → I ∧ a ≡ ( (a ∨ (- a)) ∧ a)  → a ∨ (- a) ≡ I
  --bomp out = {!   !}

  ⇒-lowergreater : ∀ {a a' b : A} → (a ≤ a') → (a' ⇒ b) ≤ (a ⇒ b)
  ⇒-lowergreater aleap = ha- (≤-tran ((equle (glb (≤-tran lb1 aleap) lb2) ∧-comm) ؛ (equle ≤-refl ⇒-absorp1)) lb2)

  ⇒-higherheyting : ∀ {a b b' : A} → (b ≤ b') → (a ⇒ b) ≤ (a ⇒ b')
  ⇒-higherheyting blebp = ≤-tran (glb (ha- (equle (≤-tran lb2 blebp) ( ∧-comm ∶ ⇒-absorp1))) ≤-refl) lb1

  ⇒-cong : ∀ {a b c d : A} → (a ≡ b) → (c ≡ d) → (a ⇒ c) ≡ (b ⇒ d)
  ⇒-cong refl refl = refl

--  ⇒-ItoO : I ⇒ O ≡ O
--  ⇒-ItoO = ⇒-flop (≤-asymm (ha- (equle3 ∧-comm refl (equle ≤-refl ⇒-absorp2))) (equle3 (symm ⇒-I) refl (ha- (equle ≤-refl (⇒-absorp1 ∶ (≤-asymm lb2 Omin))))))

  boink : ∀ {a b c : A} → a ≡ b → (a ∧ c) ≡ b ∧ c
  boink = λ aeqb → ≤-asymm (glb (≤-tran lb1 (equle ≤-refl aeqb)) lb2) (glb (≤-tran lb1 (equle ≤-refl (symm aeqb))) (≤-tran lb2 ≤-refl))

  -- double-comp : ∀ {a : A} → - (- a) ≡ a
  --double-comp = ⇒-flop (≤-asymm (ha- (equle ≤-refl (⇒-flop (≤-asymm (equle3 refl (symm ⇒-I) Imax) (ha- {!   !}))))) (((ha- (equle3 (symm ⇒-absorp1) refl lb2)))))
      --≤-asymm ( {!   !} ) ((ha- (equle3 (symm ⇒-absorp1) refl lb2)))
      --≤-asymm (equle3 ∧-idem refl (ha+ {!   !})) (ha- (equle3 (symm ⇒-absorp1) refl lb2))

  lemma1 : ∀ {a : A} → ( a  ∧ (- a) ) ≡ O
  lemma1 = ≤-asymm (equle3 (symm ⇒-absorp1) refl lb2) Omin

--  lemma2 : ∀ {a : A} → ( a  ∨ (- a) ) ≡ I
--  lemma2 = ⇒-flop ({!   !} ∶ symm ⇒-ItoO)
  --⇒-flop (({!   !} ∶ lemma1) ∶ symm (tran O (⇒-flop (≤-asymm (ha- lb2) (ha- (equle3 ∧-comm refl (ha+ (ha- (equle (equle3 ∧-comm refl (equle ≤-refl (tran (I ∧ O) ⇒-absorp1 (≤-asymm lb2 Omin)))) (∧-congR ⇒-I)))))))) refl))

  -- lemma2 = (∨-congL (symm ab1)) ∶ (∨-congL (∧-comm ∶ distribute1)) ∶ {!  !}
  --  lemma1 = ≤-asymm Imax (equle3 ⇒-I refl (≤-tran {!   !} ≤-refl))

-- equleI : ∀ {a c : A} → (a ⇒ ((a ⇒ c) ∧ a)) ≡ I
--  equleI {a} {c} = ≤-asymm Imax (equle3 ⇒-I refl ( ⇒-lowergreater {!   !} ))
                    -- ≤-asymm Imax (equle3 ⇒-I refl (equle3 refl (symm (tran ((a ⇒ (a ∧ c))) (≤-asymm (ha- (equle3 ∧-comm refl (equle3 (symm (⇒-absorp1 ∶ ((∧-congR (∧-comm ∶ ⇒-absorp1)) ∶ ((symm ∧-assoc) ∶ (∧-congL ∧-idem))))) refl ≤-refl)))
--                                                                                    (ha- (equle3 (symm (∧-comm ∶ ⇒-absorp1)) (symm (∧-comm ∶ ⇒-absorp1)) (glb lb1 (≤-tran lb2 lb2)))))
--                                                                                   refl)) (equle3 refl (symm ⇒-dist) {!   !})))


  ⇒-lessthan : ∀ {a a' b : A} → (a ≤ a') → (((a ∧ a') ∨ a') ⇒ b) ≤ ((a ∧ a') ⇒ b)
  ⇒-lessthan devo = ⇒-lowergreater (≤-refl ؛ ub1)

  orless : ∀ {a b c : A} → (((a ∨ b) ⇒ c)) ≤ ((a) ⇒ c)
  orless = ⇒-lowergreater ub1

  excercise1 : ∀ {a b : A} → - ( a ∨ b ) ≡ ((- a) ∧ (- b) )
  excercise1 = ≤-asymm (glb (ha- (≤-tran (glb lb1 (≤-tran lb2 ub1)) (equle3 (symm ∧-comm) refl (equle3 (symm ⇒-absorp1) refl lb2)))) (ha- (≤-tran (glb lb1 (≤-tran lb2 ub2)) (equle3 (symm (∧-comm ∶ ⇒-absorp1)) refl lb2))))
                                (ha- (equle3 ∧-comm refl (equle3 (symm distribute1) refl
                                (lub (equle3 ∧-assoc refl (≤-tran lb1 (equle3 (symm lemma1) refl ≤-refl)))
                                (≤-tran (equle3 (symm (∧≡ ∧-comm)) refl (equle3 (symm (symm ∧-assoc)) refl lb1))
                                (equle3 (symm ⇒-absorp1) refl lb2))))))

  abovezero : ∀ {a b : A} → (a ⇒ O) ≤ (a ⇒ b)
  abovezero = ha- (equle Omin (∧-comm ∶ ⇒-absorp1 ∶ ≤-asymm lb2 Omin))

  -- bottom : ∀ {a : A} → (- a) ≡ O
  --bottom = ≤-asymm {!   !} Omin



-- Concudes Boolean Stuff
  ⇒-backbigger : ∀ {a b : A} → b ≤ (a ⇒ b)
  ⇒-backbigger = ha- lb1

  ⇒-Itop : ∀ {a : A} → I ⇒ a ≡ a
  ⇒-Itop = (≤-asymm (glb Imax ≤-refl) lb2) ∶ ⇒-absorp1 ∶ (∧-comm ∶ ∧-unit)

--  ⇒-Obot : ∀ {a : A} → O ⇒ a ≡ O
--  ⇒-Obot = ≤-asymm (p1 ∧to≤ {!   !}) {!   !}

-- LOGIC LEMMAS
  ⇒-apply : ∀ {a b c : A} → b ∧ (a ⇒ c) ≤ a → b ∧ (a ⇒ c) ≤ c
  ⇒-apply living = equle3 (p2 ∧to≤ living) refl (equle3 (symm (∧-assoc ∶ ((∧-congR ∧-comm) ∶ (∧-congR ⇒-absorp1)))) refl (equle3 ∧-assoc refl lb2))

  ⇒-cases : ∀ {a b c d : A} →  ( a ∧ c ≤ d ) → (a ∧ b ≤ d) → a ∧ (b ∨ c) ≤ d
  ⇒-cases first sec  = equle3 (symm distribute1 ∶ ∧-comm) refl (equle3 (∨-cong ∧-comm ∧-comm) refl (≤-tran (lub (≤-tran sec (≤-tran ≤-refl ub1)) (≤-tran first ub1)) (equle ≤-refl ∨-idem)))

  ⇒-easyapply : ∀ {a b c d : A} → d ≤ a → d ≤ (a ⇒ c) → d ≤ c
  ⇒-easyapply one two = equle3 (p2 ∧to≤ two) refl (equle (equle3 (symm ∧-assoc) refl (equle (lb2 ؛ lb2) (∧-congR ⇒-absorp1)))
                        (∧-congL (symm (p2 ∧to≤ one))))
---

  -- ⇒-∧breaker : ∀ {a b : A} → ((a ∧ b) ⇒ O) ≤ (a ⇒ O) ∧ (b ⇒ O)
  -- ⇒-∧breaker = equle3 ∧-unit refl (ha+ {! ⇒-higherheyting  !})

  oddDemorgan : ∀ {a b : A} → (- - (a ∧ b) ) ≡ (- - a) ∧ (- - b)
  oddDemorgan = ≤-asymm (glb (⇒-lowergreater (⇒-lowergreater lb1)) (⇒-lowergreater (⇒-lowergreater lb2)))
              --  ( ha+ (equle3 refl {! ⇒-cong  !} {!   !}) )
              --  (ha- (≤-tran (glb lb1 (lb2 ؛ (⇒-lowergreater {!   !}))) {!   !}))

              (≤-tran (ha- (equle3 (symm ∧-assoc) refl (equle3 ∧-comm refl
              (⇒-apply
              (ha- (equle3 ((symm ((∧-congR (∧-comm ∶ (∧-congR ∧-comm))) ∶ (symm ∧-assoc))) ∶ ∧-comm) refl (equle3 ((∧-congR refl) ∶ ∧-assoc) refl
              (⇒-apply
              (ha- (equle3 (symm (∧-comm ∶ ( symm ∧-assoc ∶ (∧-congL ((symm ∧-assoc) ∶ ((∧-congL (symm ∧-assoc)) ∶ ((∧-congL (∧-congL ∧-comm)) ∶ (∧-congL ∧-comm ∶ ∧-assoc))))) ∶ ∧-congL (∧-congR
              ⇒-absorp1)))) refl (≤-tran lb1 (lb2 ؛ lb2))))))))))))
              (⇒-lowergreater (⇒-lowergreater ≤-refl)))
              --  (≤-tran (ha- (≤-tran (glb lb2 (≤-tran lb1 (glb lb2 (lb1 ؛ (⇒-lowergreater (⇒-lowergreater ub1)))))) (equle3 (∧-congR (∧-congR (⇒-cong (symm excercise1) refl))) refl {!   !}))) (⇒-lowergreater abovezero))
  ⇒-sandwich : ∀ {a : A} → ((O ⇒ I) ⇒ O) ≡ O
  ⇒-sandwich = ≤-asymm (p1 ∧to≤ ((≤-asymm lb2 Omin) ∶ (≤-asymm Omin (equle3 refl ⇒-Itop (⇒-lowergreater (ha- lb1)))))) Omin

  ⇒-supersandwich : ∀ {a : A} → ((O ⇒ a) ⇒ O) ≡ O
  ⇒-supersandwich = ≤-asymm (p1 ∧to≤ ((≤-asymm lb2 Omin) ∶ (≤-asymm Omin (equle3 refl ⇒-Itop (⇒-lowergreater (ha- (equle Omin (≤-asymm lb2 Omin)))))))) Omin

  -- ⇒-pseudosandwich : ∀ {a : A} → ((a ⇒ O) ⇒ O) ≡ O
  -- ⇒-pseudosandwich = ≤-asymm (p1 ∧to≤ (≤-asymm (equle3 (≤-asymm Omin lb2) refl Omin) (equle3 refl (≤-asymm Omin lb2) (equle3 refl ⇒-Itop (⇒-lowergreater {!   !}))))) Omin

  MalcevP1ex1 : ∀ {a b : A} → P₁ a a b ≡ b
  MalcevP1ex1 = ≤-asymm (equle3 ∧-comm refl (ha+ (≤-tran Imax (equle3 ⇒-I refl (equle ≤-refl (⇒-cong (symm ⇒-Itop ∶ ⇒-cong (symm ⇒-I) refl) refl))))))
                (glb (equle3 refl (⇒-cong (symm ⇒-I) refl) (equle3 refl (symm ⇒-Itop) ≤-refl)) (ha- (equle3 (symm ⇒-absorp1) refl lb2)))

  --B and (b->a)->a = b
  P1ex1 : ∀ {a b : A} → ((a ⇒ a) ⇒ b) ∧ ((b ⇒ a) ⇒ a) ≡ b
  P1ex1 = MalcevP1ex1

  MalcevP1ex2 : ∀ {a b : A} → P₁ a b b ≡ a
  MalcevP1ex2 = ≤-asymm (equle3 (∧-congR (⇒-cong (symm refl ∶ symm ⇒-I ) refl)) refl (equle3 (∧-congR (symm ⇒-Itop)) refl (ha+ (≤-tran Imax (equle ≤-refl (symm ⇒-I))))))
                (glb (ha- (equle3 (symm ⇒-absorp1) refl lb2)) (equle3 refl (refl ∶ (⇒-cong (symm ⇒-I) refl)) (equle3 refl (symm ⇒-Itop) ≤-refl)))

  P1ex2 : ∀ {a b : A} → ((a ⇒ b) ⇒ b) ∧ ((b ⇒ b) ⇒ a) ≡ a
  P1ex2 = MalcevP1ex2

  MalcevP2ex1 : ∀ {a b : A} → P₂ a a b ≡ b
  MalcevP2ex1 = (∧-congL ⇒-dist) ∶ ((∧-congL (∧-congL ⇒-I)) ∶ ((∧-congL (∧-comm ∶ ∧-unit)) ∶ (∧-comm ∶ (distribute1 ∶ ((∨-cong ⇒-absorp1 ⇒-absorp2) ∶ ((∨-cong ∧-comm refl) ∶ (∨-comm ∶ ab2)))))))

  --(a ⇒ (a ∧ b)) ∧ (a ∨ b) ≡ b
  P2ex1 : ∀ {a b : A} → (a ⇒ (a ∧ b)) ∧ (a ∨ b) ≡ b
  P2ex1 = MalcevP2ex1

  MalcevP2ex2 : ∀ {a b : A} → P₂ a b b ≡ a
  MalcevP2ex2 = (∧-congL ⇒-dist) ∶ ((∧-congL (∧-comm ∶ (∧-congL ⇒-I))) ∶ ((∧-congL (∧-comm ∶ ∧-unit) ∶ ∧-comm) ∶ distribute1 ∶ ((∨-cong ⇒-absorp2 ⇒-absorp1) ∶ ((∨-congR ∧-comm) ∶ ab2))))

  P2ex2 : ∀ {a b : A} → (b ⇒ (a ∧ b)) ∧ (a ∨ b) ≡ a
  P2ex2 = MalcevP2ex2

  -- ⇒-∨absorp1 : ∀ {a b c : A} → (a ∨ b) ∧ (a ⇒ c) ≡ (a) ∧ (a ⇒ c)
  --⇒-∨absorp1 = ≤-asymm (equle3 (symm distribute1) refl {!   !}) (glb (≤-tran lb1 ub1) lb2)

--  ingeneral : ∀ {a b c : A} → P₁ a b c ≡ P₂ a b c
--  ingeneral = ≤-asymm

--              (glb (ha- ((glb lb1 (glb (≤-tran lb2 ≤-refl ) Imax)) ؛ equle3 (symm (∧-comm ∶ ((∧-congL ∧-comm) ∶ ∧-assoc ∶ ((∧-congR refl) ∶ refl) ))) refl (glb (equle3 (symm (symm ∧-assoc ∶ ∧-comm ∶ ∧-assoc )) refl (equle3 ((symm
--              (∧-assoc ∶ ∧-comm)) ∶ ∧-comm) refl (⇒-apply (ha- (lb1 ؛ (≤-tran lb1 (≤-tran lb1 lb2))))))) (equle3 ((symm (∧-comm ∶ (∧-assoc ∶ (∧-comm ∶ refl)))) ∶ ∧-assoc) refl (⇒-apply (ha- (lb1 ؛ (≤-tran lb1 (≤-tran lb2 lb2)))))))))
--              {!   !})

--              (equle3 (∧-congL (symm ⇒-dist)) refl (⇒-cases (glb (ha- (lb1 ؛ ≤-tran lb2 ≤-refl)) (ha- (equle3 (symm ∧-comm) refl (equle3 (∧-congR ((∧-congR ∧-comm) ∶ ∧-comm)) refl (equle3 ( (refl ∶ ∧-assoc) ∶ ∧-assoc) refl (⇒-apply
--              (⇒-easyapply (≤-tran lb1 (≤-tran lb1 lb2)) (lb1 ؛ (≤-tran lb1 lb1)))))))))
--              (glb (ha- (⇒-easyapply (⇒-easyapply (≤-tran lb1 lb2) lb2) (lb1 ؛ (≤-tran lb1 lb2))))
--              (ha- (≤-tran lb1 lb2)))))

--General Proof it could be done.

              --(glb (ha- (equle3 (symm (∧-congL (∧-congL (symm ∧-idem)))) refl (≤-tran (glb (≤-tran lb1 (glb (≤-tran lb1 (glb (≤-tran lb1 (⇒-higherheyting lb2)) lb2)) lb2)) lb2)
              --(equle3 (symm (∧-assoc ∶ (∧-comm ∶ ((∧-congR ∧-comm) ∶ ( ∧-comm ∶ (∧-congL ∧-comm) ∶ ∧-assoc))))) refl (equle3 ∧-comm refl (⇒-apply {!   !})))))) {!   !})
          --    ≤-asymm (equle3 refl (∧-congL (symm ⇒-dist)) (glb (glb (ha- (≤-tran (glb lb1 (≤-tran lb2 ⇒-backbigger)) (equle (≤-tran lb2 lb2) (∧-assoc ∶ ((∧-congR (∧-comm ∶ ⇒-absorp1)) ∶ refl)))))
          --    (ha- (≤-tran (glb lb1 (lb2 ؛ ⇒-backbigger)) (equle3 ((symm ((symm ∧-assoc) ∶ (∧-congL ⇒-absorp1))) ∶ ∧-comm) refl (equle3 ((symm ∧-assoc) ∶ (∧-congL ∧-comm)) refl lb1)))))


-- All boolean stuf
record HABool {A : Set} {_≤_ : Rel A} (po : PO _≤_) : Set where
  field
    lat : LAT po
  open LAT lat
  open Poset.PO po


  field
    _⇒_ : A → A → A
  --  _⊹_ : A → A → A
    ha : ∀ {x y z : A} → z ≤ (x ⇒ y) ⇔ z ∧ x ≤ y

    BooleanCondition : ∀ {a : A} → (a ≡ ((a ⇒ O) ⇒ O))

  -_ : A → A
  - a = a ⇒ O


  ha+ : ∀ {x y z : A} → z ≤ (x ⇒ y) → ( z ∧ x ) ≤ y
  ha+  = p1 ha

  ha- : ∀ {x y z : A} → ( z ∧ x ) ≤ y → z ≤ (x ⇒ y)
  ha-  = p2 ha


  attempt : ∀ {a b : A} → b ≤ (a ⇒ b)
  attempt = ha- lb1

  ⇒-flip : ∀ {a b : A} → a ≡  b → - a ≡ - b
  ⇒-flip refl = refl


  ⇒-absorp2 : ∀ {a b : A} → ( b ∧ (a ⇒ b) ) ≡ b
  ⇒-absorp2 = ≤-asymm lb1 (glb ≤-refl (ha- lb1))


  ⇒-absorp1 : ∀ {a b : A} → (a ∧ (a ⇒ b) ) ≡ a ∧ b
  ⇒-absorp1 {a} {b} = ≤-asymm (glb lb1 (equle3 ∧-comm refl (ha+ ≤-refl))) (glb lb1 (lb2 ؛ attempt))
      --                ≤-asymm (equle3 ∧-comm refl (ha+ {!   !} )) (≤-tran (≤-tran (equle3 (symm ((symm ab2) ∶ (refl ∶ refl))) refl (equle3 ∨-comm refl dis2 ؛
      --                equle3 (symm (∧-comm ∶ (∧≡ ∨-idem))) refl ( {!   !} ؛ lb2)))
      --                (equle3 refl (tran ((b ∧ (a ⇒ b)) ∧ a) refl (∧-assoc ∶ (∧-comm ∶ (≡∧ ∧-comm)))) (equle3 refl (≡∧ (symm ⇒-absorp2)) ≤-refl))) lb1)

  lemma1 : ∀ {a : A} → ( a  ∧ (- a) ) ≡ O
  lemma1 = ≤-asymm (equle3 (symm ⇒-absorp1) refl lb2) Omin

  ⇒-dist : ∀ {a b c : A} → (a ⇒ (b ∧ c)) ≡ (a ⇒ b) ∧ (a ⇒ c)
  ⇒-dist = ≤-asymm (glb (ha- (equle3 (symm ∧-comm) refl (equle3 (symm (⇒-absorp1 ∶ (∧-comm ∶ ∧-assoc)) ) refl lb1)))
                   (ha- (equle3 (symm ∧-comm) refl (equle3 (symm (⇒-absorp1 ∶ ((symm ∧-assoc) ∶ refl)) ) refl lb2)))) (ha+ (ha- (ha- (glb (equle3 (symm ((∧-congL ∧-comm ∶ ∧-assoc) ∶ refl)) refl
                  (lb2 ؛ (equle3 (symm (∧-comm ∶ ⇒-absorp1)) refl lb2)) )
                                          (equle3 (symm ∧-assoc) refl (lb2 ؛ (equle3 ∧-comm refl (equle3 (symm ⇒-absorp1) refl lb2))) )))))
  --  ⇒-∧-cong : ∀ {a b : A} → (a ∧ (a ⇒ b)) ≡ ((a ∧ a) ⇒ (b ∧ a))
  --  ⇒-∧-cong = ≤-asymm (ha- {!   !}) {!   !}
  ⇒-I : ∀ {a : A} → (a ⇒ a) ≡ I
  ⇒-I = ≤-asymm Imax (ha- lb2)

  dist1 : ∀ {a b c : A} → (a ∨ b) ∧ c ≤ (a ∧ c) ∨ (b ∧ c)
  dist1 = ha+ (lub (ha- ub1) (ha- ub2))

  dist2 : ∀ {a b c : A} → (a ∧ b) ∨ c ≥ (a ∨ c) ∧ (b ∨ c)
  dist2 = equle3 ∧-comm refl (ha+ (lub (ha- (equle3 ∧-comm refl (ha+ (lub (ha- ub1)
          (ha- (≤-tran lb1 ub2))))))
          (ha- (equle3 ((symm ab1) ∶ (symm (∧≡ ∨-comm))) (symm refl) ub2))))
  -- ha+ (lub ( {!   !} ) (ha- (equle3 (symm ((∧≡ ∨-comm) ∶ ab1)) refl ub2)))
  distribute1 : ∀ {a b c : A} → (a ∨ b) ∧ c ≡ (a ∧ c) ∨ (b ∧ c)
  distribute1 = ≤-asymm dist1 dis1

  distribute2 : ∀ {a b c : A} → (a ∧ b) ∨ c ≡ (a ∨ c) ∧ (b ∨ c)
  distribute2 = ≤-asymm dis2 dist2



  ⇒-cong : ∀ {a b c d : A} → (a ≡ b) → (c ≡ d) → (a ⇒ c) ≡ (b ⇒ d)
  ⇒-cong refl refl = refl

  excercise1 : ∀ {a b : A} → - ( a ∨ b ) ≡ ((- a) ∧ (- b) )
  excercise1 = ≤-asymm (glb (ha- (≤-tran (glb lb1 (≤-tran lb2 ub1)) (equle3 (symm ∧-comm) refl (equle3 (symm ⇒-absorp1) refl lb2)))) (ha- (≤-tran (glb lb1 (≤-tran lb2 ub2)) (equle3 (symm (∧-comm ∶ ⇒-absorp1)) refl lb2))))
                                (ha- (equle3 ∧-comm refl (equle3 (symm distribute1) refl
                                (lub (equle3 ∧-assoc refl (≤-tran lb1 (equle3 (symm lemma1) refl ≤-refl)))
                                (≤-tran (equle3 (symm (∧≡ ∧-comm)) refl (equle3 (symm (symm ∧-assoc)) refl lb1))
                                (equle3 (symm ⇒-absorp1) refl lb2))))))



  BooleanFlop : ∀ {a b : A} → (- a ≡ - b) → (a ≡ b)
  BooleanFlop kick = BooleanCondition ∶ ((⇒-cong kick refl) ∶ (symm BooleanCondition))

  BooleanProof : ∀ {a : A} → (a ∨ (- a)) ≡ I
  BooleanProof {a} = BooleanFlop (excercise1 ∶ ((∧-congR (symm BooleanCondition)) ∶ (∧-comm ∶ (lemma1 ∶ (refl ∶ ≤-asymm Omin (equle3 (≤-asymm lb1 (glb ≤-refl Imax)) refl (ha+ ≤-refl)))))))
--  BooleanProof : ∀ {a : A} → (a ≡ - - a) → (a ∨ (- a)) ≡ I
--  BooleanProof {a} base = BooleanFlop {!   !} {!   !} (excercise1 ∶ (∧-congR (symm base) ∶ (∧-comm ∶ lemma1) ∶ ({! base  !} ∶ (⇒-cong ⇒-I refl))))
-- ≤-asymm Imax (equle3 ⇒-I refl {!   !})

-- 1.13 Proofs

  -O=I : - O ≡ I
  -O=I = ⇒-I

  -I=O : - I ≡ O
  -I=O = ≤-asymm (equle (equle lb2 (∧-comm ∶ ⇒-absorp1)) (symm ∧-unit)) Omin

  firstimp : ∀ {a : A} → ((a ∧ (- a)) ≡ O) → a ≤ (- - a)
  firstimp first = ha- (equle lb2 ⇒-absorp1)

  secondpart : ∀ {a : A} → (- a) ≡ (- (- (- a)))
  secondpart = ⇒-flip BooleanCondition

  -- LOGIC LEMMAS
  ⇒-apply : ∀ {a b c : A} → b ∧ (a ⇒ c) ≤ a → b ∧ (a ⇒ c) ≤ c
  ⇒-apply living = equle3 (p2 ∧to≤ living) refl (equle3 (symm (∧-assoc ∶ ((∧-congR ∧-comm) ∶ (∧-congR ⇒-absorp1)))) refl (equle3 ∧-assoc refl lb2))

  ⇒-cases : ∀ {a b c d : A} →  ( a ∧ c ≤ d ) → (a ∧ b ≤ d) → a ∧ (b ∨ c) ≤ d
  ⇒-cases first sec  = equle3 (symm distribute1 ∶ ∧-comm) refl (equle3 (∨-cong ∧-comm ∧-comm) refl (≤-tran (lub (≤-tran sec (≤-tran ≤-refl ub1)) (≤-tran first ub1)) (equle ≤-refl ∨-idem)))

  ⇒-easyapply : ∀ {a b c d : A} → d ≤ a → d ≤ (a ⇒ c) → d ≤ c
  ⇒-easyapply one two = equle3 (p2 ∧to≤ two) refl (equle (equle3 (symm ∧-assoc) refl (equle (lb2 ؛ lb2) (∧-congR ⇒-absorp1)))
                        (∧-congL (symm (p2 ∧to≤ one))))
  ---
  ⇒-lowergreater : ∀ {a a' b : A} → (a ≤ a') → (a' ⇒ b) ≤ (a ⇒ b)
  ⇒-lowergreater aleap = ha- (≤-tran ((equle (glb (≤-tran lb1 aleap) lb2) ∧-comm) ؛ (equle ≤-refl ⇒-absorp1)) lb2)

  ⇒-higherheyting : ∀ {a b b' : A} → (b ≤ b') → (a ⇒ b) ≤ (a ⇒ b')
  ⇒-higherheyting blebp = ≤-tran (glb (ha- (equle (≤-tran lb2 blebp) ( ∧-comm ∶ ⇒-absorp1))) ≤-refl) lb1

  BooleanProof2 : ∀ {a : A} → (- (- (a ∨ (- a)))) ≡ I
  BooleanProof2 {a} = ≤-asymm Imax (ha- (equle3 (∧-congL BooleanProof) refl (equle lb2 ⇒-absorp1)))

  DeMorgan : ∀ {a b : A} → - (a ∧ b) ≡ (- a) ∨ (- b)
  DeMorgan = ≤-asymm ( equle ≤-refl (BooleanFlop (≤-asymm (ha- (⇒-cases (≤-tran (glb lb1 (≤-tran lb2 (⇒-lowergreater lb2))) (equle3 ∧-comm refl (equle3 (symm ⇒-absorp1) refl lb2)))
                    (≤-tran (glb (lb2 ؛ (⇒-lowergreater lb1)) lb1) (equle3 (symm ⇒-absorp1) refl lb2))))
                    (ha- (equle3 (symm (∧-congL excercise1)) refl (equle3 (∧-congL (∧-cong BooleanCondition BooleanCondition)) refl (equle3 (symm ⇒-absorp1) refl lb2)))))) )
                    (equle (⇒-cases (≤-tran lb2 (⇒-lowergreater lb2)) (≤-tran lb2 (⇒-lowergreater lb1))) (symm (symm ((symm ∧-unit) ∶ ∧-comm))))

  Theident : ∀ {a b : A} → (- a) ∨ (- (- a)) ≡ I
  Theident = (∨-congR (symm BooleanCondition)) ∶ (∨-comm ∶ (BooleanFlop (BooleanFlop ((BooleanProof2 ∶ (symm ⇒-I)) ∶ (⇒-cong (symm -I=O) refl)))))
