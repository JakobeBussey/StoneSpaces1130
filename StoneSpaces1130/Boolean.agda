module Boolean where

open import BasicTypes
open import Poset
open import Lattice

record BA {A : Set} {_≤_ : Rel A} (po : PO _≤_) : Set where
  field
    dlat : DLAT po
  open DLAT dlat
  open PO po

  field
    - : A → A
    -comp : ∀ {a : A} → ∁ a (- a)

  --  _plus_ : A → A → A
  _⊹_ : A → A → A
  a ⊹ b = (a ∧ (- b)) ∨ (b ∧ (- a))

  gogo : ∀ {x : A} → ∁ x (- x)
  gogo {x} = -comp

  O-comp-swap : ( ∀ {a : A} → ∁ a (- a) ) → - O ≡ I
  O-comp-swap pk = ≤-asymm Imax (equle3 (p2 pk) refl (lub ≤-refl Omin))

  I-comp-swap : ( ∀ {a : A} → ∁ a (- a) ) → O ≡ (- I)
  I-comp-swap pk = ≤-asymm Omin (equle3 refl (p1 pk) (glb ≤-refl Imax))

  ∨-comp : ∀ {x : A} → ( ∀ {a : A} → ∁ a (- a) ) → (x ∨ (- x) ) ≡ I
  ∨-comp {x} pre = tran ((- x) ∨ x) ∨-comm (p2 pre)

  ∧-comp : ∀ {x : A} → ( ∀ {a : A} → ∁ a (- a) ) → (x ∧ (- x) ) ≡ O
  ∧-comp {x} pre = tran ((- x) ∧ x) ∧-comm (p1 pre)

  example2 : (∀ {x y : A} → x ≤ y + y ≤ x ) → ∀ (x : A) → x ≡ O + x ≡ I
  example2 xleyorylex = λ x → case xleyorylex (λ bonx → in1 (≤-asymm (equle3 refl ( ∧-comp -comp ) (glb ≤-refl bonx)) Omin))
                                  (λ blox → in2 (≤-asymm Imax (equle3 ( ∨-comp -comp ) refl (lub ≤-refl blox) )) )


--Section 1.8

  compequ : ∀ {a b : A} → a ≡ b → - a ≡ - b
  compequ {a} {.a} refl = refl



  comp-colapse : ∀ {a : A} → - (- a) ≡ a
  comp-colapse {a} = ∁-unique (-(- a)) a -comp ((∧-comp -comp) , (∨-comp -comp))

  ∨-break : ∀ {a b : A} → - a ∨ (a ∨ b) ≡ I
  ∨-break {a} {b} = (symm ∨-assoc) ∶ ((∨-congL ∨-comm) ∶ ((∨-comm ∶ (∨-congR (∨-comp -comp))) ∶ ∨-top))

  ∧-break : ∀ {a b : A} → a ∧ (- a ∧ - b) ≡ O
  ∧-break {a} {b} = ((symm ∧-assoc) ∶ ((∧-congL (∧-comp -comp)) ∶ ∧-comm)) ∶ ∧-bot

  Demorgan1 : ∀ {a b : A} → (- (a ∧ b)) ≡ (- a) ∨ (- b)
  Demorgan1 {a} {b} = modLemma3 ((∧-congL (modLemma3 (∧-comp -comp) (∨-comp -comp) ( ( ∧-congL
                       (modLemma3 (superdist1 ∶ (∨-cong ((symm ∧-assoc) ∶ ((∧-congL (∧-comm ∶ (∧-comp -comp))) ∶ (∧-comm ∶ ∧-bot))) (∧-comm ∶ (∧-assoc ∶ ((∧-congR (∧-comp -comp)) ∶ ∧-bot)))
                       ∶ ∨-idem)) ((∨-comm ∶ superdist2) ∶ ((∧-cong (symm ∨-assoc ∶ (∨-congL (∨-comp -comp)) ∶ (∨-comm ∶ ∨-top)) (∨-comm ∶ (∨-assoc ∶ ((∨-congR (∨-comm ∶ (∨-comp -comp))) ∶ ∨-top)))) ∶ ∧-idem))
                       (∧-comm ∶ (∧-comp -comp)) (∨-comm ∶ (∨-comp -comp))) ) ∶ (∧-comp -comp) ) (∨-congL (modLemma3 (superdist1 ∶ ((∨-cong ((symm ∧-assoc) ∶ ((∧-congL (∧-comm ∶ (∧-comp -comp))) ∶ (∧-comm ∶ ∧-bot))) (∧-comm ∶ (∧-assoc ∶ (∧-congR (∧-comp -comp) ∶ ∧-bot)))) ∶ ∨-idem))
                     (∨-comm ∶ (superdist2 ∶ (∧-cong ((symm ∨-assoc) ∶ ((∨-congL (∨-comp -comp)) ∶ (∨-comm ∶ ∨-top))) (∨-comm ∶ (∨-assoc ∶ ((∨-congR (∨-comm ∶ (∨-comp -comp))) ∶ ∨-top))) ∶ ∧-idem)))
                     (∧-comm ∶ (∧-comp -comp)) (∨-comm ∶ (∨-comp -comp))) ∶ (∨-comp -comp)))) ∶ (∧-comp -comp))
                                                 (((∨-congR (modLemma3 (∧-comp -comp) (∨-comp -comp) ((∧-congR comp-colapse) ∶ (∧-comm ∶ superdist1) ∶ (∨-cong ((symm ∧-assoc) ∶ ((∧-congL (∧-comm ∶ (∧-comp -comp))) ∶
                                                 ∧-comm ∶ ∧-bot)) (∧-comm ∶ (∧-assoc ∶ ((∧-congR (∧-comp -comp)) ∶ ∧-bot)))) ∶ ∨-idem)
                                                  ((∨-congR comp-colapse) ∶ superdist2 ∶ (∧-cong ((symm ∨-assoc) ∶ ((∨-congL (∨-comp -comp)) ∶ (∨-comm ∶ ∨-top))) (∨-comm ∶ (∨-assoc ∶ ((∨-congR (∨-comm ∶ (∨-comp -comp))) ∶ ∨-top)))) ∶ ∧-idem))) ∶ ∨-comm) ∶ (∨-comp -comp)) (∧-comp -comp) (∨-comp -comp)
  --tran ((- (a ∧ b)) ∧ I) (symm ∧-unit)
    --                  (tran ((- (a ∧ b)) ∧ (- (a ∧ b) ∨ (a ∧ b))) (∧-congR (symm (∨-comm ∶ (∨-comp -comp))))
      --                (∧-comm ∶ (superdist1 ∶ {!   !})))


  Demorgan2 : ∀ {a b : A} → (- (a ∨ b)) ≡ (- a) ∧ (- b)
  Demorgan2 = modLemma3 ((∧-comm ∶ (∧-congL (modLemma3 (∧-comm ∶ (∧-comp -comp)) (∨-comm ∶ (∨-comp -comp)) (superdist1 ∶ ((∨-cong ∧-break (∧-congR ∧-comm ∶ ∧-break)) ∶ ∨-idem)) (∨-comm ∶ (superdist2 ∶ ((∧-cong ((symm ∨-assoc) ∶ ∨-assoc ∶ ∨-break) ((∨-congR ∨-comm) ∶ ∨-break)) ∶ ∧-idem)))))) ∶ ∧-comp -comp)
                       ((∨-comm ∶ ∨-comm ∶ (∨-congL (modLemma3 (∧-comm ∶ (∧-comp -comp)) (∨-comm ∶ (∨-comp -comp)) ((∧-comm ∶ superdist1) ∶ ((refl ∶ (∨-cong ∧-break ((∧-congR ∧-comm) ∶ ∧-break))) ∶ ∨-idem)) (superdist2 ∶ ((∧-cong ∨-break ((∨-congR ∨-comm) ∶ ∨-break)) ∶ ∧-idem))))) ∶ ∨-comp -comp) (∧-comp -comp) (∨-comp -comp)

  dist⊹ : ∀ {a b c : A} → a ∧ (b ⊹ c) ≡ (a ∧ b) ⊹ (a ∧ c)
  dist⊹ {a} {b} {c}  = symm ((∨-cong (∧-congR Demorgan1) (∧-congR Demorgan1)) ∶
         ∨-cong ( ∧-comm ∶ superdist1 ) (∧-comm ∶ superdist1) ∶
         (∨-cong (∨-congL ( symm ∧-assoc ∶ ∧-congL (∧-comm ∶ (∧-comp -comp)) )) (∨-congL (symm ∧-assoc ∶ ∧-congL (∧-comm ∶ (∧-comp -comp))))) ∶
         ∨-cong ((∨-comm ∶ (∨-congR (∧-comm ∶ ∧-bot))) ∶ ∨-unit) (∨-congL (∧-comm ∶ ∧-bot)) ∶ ∨-congR (∨-comm ∶ ∨-unit) ∶
         (∨-cong (∧-comm ∶ ∧-assoc) (∧-comm ∶ ∧-assoc)) ∶
         symm (tran (a ∧ ((b ∧ (- c)) ∨ (c ∧ (- b)))) refl (∧-comm ∶ superdist1 ∶ (∨-cong ∧-comm ∧-comm))) ∶ ∧-congR (∨-cong refl refl))

  idem⊹ : ∀ {a : A} → a ⊹ a ≡ O
  idem⊹ = tran (O ∨ O) (∨-cong (∧-comp -comp) (∧-comp -comp)) ∨-idem

  boxa⊹ : ∀ {a : A} → a ⊹ O ≡ a
  boxa⊹ {a} = tran (a ∨ O) (∨-cong (tran (a ∧ I) (∧-congR (O-comp-swap -comp)) (≤-asymm lb1 (glb ≤-refl Imax))) (∧-comm ∶ ∧-bot)) (≤-asymm (lub ≤-refl Omin) ub1)

  assoc⊹ : ∀ {a b c : A} → a ⊹ (b ⊹ c) ≡ (a ⊹ b) ⊹ c

  assoc⊹ {a} {b} {c} = (∨-congL (∧-congR Demorgan2)) ∶ ((∨-congL (∧-congR (∧-cong Demorgan1 Demorgan1))) ∶
                        (((∨-congL (∧-congR (∧-cong (∨-congR comp-colapse) (∨-congR comp-colapse)))) ∶
                        (((∨-congR (∧-comm ∶ dist⊹)) ∶ (((refl ∶ ∨-comm ∶ (∨-assoc ∶ (((∨-cong (∧-comm ∶ (≤-asymm (glb (glb (equle3 (∧-congL (symm Demorgan1))
                        refl ( equle3 (∧-congL Demorgan1) refl (equle3 (∧-congL (symm Demorgan1)) refl
                        (equle3 (∧-congL (∨-congL (symm comp-colapse))) refl
                        (equle3 (symm ( superdist1 )) refl (lub (equle3 ∧-assoc refl (equle3 (symm (∧-comm ∶ ∧-bot) ∶ (∧-congL (symm (∧-comp -comp))))  refl Omin))  lb1)))))) (lb2 ؛ lb2))
                          (lb2 ؛ (equle3 refl (symm Demorgan1) (lb1 ؛ ub2))))
                        (glb (equle3 (∧-congR (symm (∨-congL comp-colapse) ∶ symm Demorgan1)) (symm (∨-congL comp-colapse ∶ ∨-comm) ∶ symm Demorgan1) (≤-tran (≤-tran lb1 lb1) ub1))
                        (equle3 (symm (∧-congR Demorgan1)) refl (equle3 (symm (∧-congR (∨-congL comp-colapse))) refl (equle3 (symm (∧-comm ∶ superdist1)) refl (equle3 (∨-congL (((symm (∧-comm ∶ ∧-bot))
                        ∶ (∧-congL (symm (∧-comp -comp)))) ∶ ∧-assoc)) refl (equle3 (symm (∨-comm ∶ ∨-unit)) refl (equle3 (∧-congR ∧-comm) refl (equle3 ∧-assoc refl lb1))))))))))
                            (≤-asymm (equle3 (∨-congL (∧-congR (symm Demorgan1))) (∨-congL (∧-congR (symm Demorgan1)))
                          (equle3 (∨-congL (((symm superdist1) ∶ ∧-comm) ∶ (∧-congR (∨-congL (symm comp-colapse))))) (∨-congL (((symm superdist1) ∶ ∧-comm) ∶ (∧-congR (∨-congL (symm comp-colapse)))))
                          (equle3 (∨-congR (∧-congR (symm superdist1))) (∨-congR (∧-congR (symm superdist1))) ( equle3 (∨-congR (∧-congR (∨-cong (symm (∧-comm ∶ superdist1)) ((symm superdist1) ∶ ∧-comm)))) (∨-congR (∧-congR (∨-cong ((symm superdist1) ∶ ∧-comm) ((symm superdist1) ∶ ∧-comm))))
                          (lub (lub (equle3 (symm ((symm ∧-assoc) ∶ ((∧-congL (∧-comp -comp)) ∶ (∧-comm ∶ ∧-bot)))) refl Omin) (≤-tran ( equle3 refl (symm (∧-comm ∶ superdist1)) (≤-tran (equle3 refl (∧-congL (symm ∨-unit ∶ (∨-congR (symm (∧-comp -comp))))) (equle3 ∧-assoc refl ≤-refl)) ub1) ) ub2))
                          (equle3 (symm (∧-comm ∶ superdist1)) (∨-cong (∨-congL ((((symm ∧-bot) ∶ ∧-comm) ∶ (∧-congL (symm (∧-comp -comp)))) ∶ ∧-assoc)) (symm (∧-comm ∶ superdist1))) (equle3 (∨-cong (∧-congL ((symm ∨-unit) ∶ (∨-congR (symm (∧-comp -comp))))) ((∧-congL (symm (∨-comm ∶ ∨-unit))) ∶
                          (∧-congL (∨-congL (symm (∧-comm ∶ (∧-comp -comp))))))) (∨-cong (symm (∨-comm ∶ ∨-unit)) (∨-cong (symm (∧-congL ((∨-congR (∧-comp -comp)) ∶ ∨-unit))) (∧-congL (((symm (∨-unit ∶ ∨-unit)) ∶ (∨-unit ∶ ∨-comm)) ∶ (∨-congL (symm (∧-comm ∶ ∧-comp -comp)))))))
                          (equle3 refl ( (∨-assoc ∶ ∨-comm) ∶ ∨-assoc) (≤-tran (equle3 ∨-comm refl (equplug refl (∨-cong (∧-comm ∶ (symm ∧-assoc)) ((∧-congL ∧-comm) ∶ ∧-assoc)))) ub1))))) ))))
                          (equle3 (∨-cong (((refl ∶ ((symm superdist1) ∶ ∧-comm)) ∶ (∧-congR (∨-congL (symm comp-colapse)))) ∶ (∧-congR (symm Demorgan1))) (symm refl)) (∨-cong (∧-congR (symm Demorgan1)) refl)
                          (equle3 refl (∨-congL (∧-congR (∨-congL (symm comp-colapse)))) (equle3 (∨-cong (symm (∨-comm ∶ ∨-unit) ∶ (∨-congL ((symm (∧-comm ∶ ∧-bot) ∶ (∧-congL (symm (∧-comp -comp)))) ∶ ∧-assoc))) refl) refl (equle3 refl (∨-congL ((symm superdist1) ∶ ∧-comm))
                          (equle3 refl (∨-congL (∨-congL (((symm (∧-comm ∶ ∧-bot)) ∶ (∧-congL (symm (∧-comp -comp)))) ∶ ∧-assoc)))
                          (equle3 (∨-congR (∧-congR (symm superdist1))) (∨-cong (symm (∨-comm ∶ ∨-unit)) (∧-congR (symm superdist1))) (equle3 (∨-cong refl (∧-congR (∨-cong (symm (∧-comm ∶ superdist1)) (symm (∧-comm ∶ superdist1))))) (∨-congR (∧-congR (∨-cong (symm (∧-comm ∶ superdist1)) (symm (∧-comm ∶ superdist1)))))
                          (equplug refl (((∨-congR (∧-congR (∨-cong (∨-congR (∧-comp -comp)) (∨-congL (∧-comm ∶ (∧-comp -comp)))))) ∶ (∨-congR (∧-congR (∨-cong ∨-unit (∨-comm ∶ ∨-unit)))) ∶ (∨-congR (∧-comm ∶ superdist1)) ∶ (((symm ∨-assoc) ∶ (
                          ((∨-comm ∶ (∨-cong (∧-assoc ∶ ∧-comm) (∨-comm ∶ (∨-cong ∧-assoc ((symm ∧-assoc) ∶ (∧-congL ∧-comm)))))) ∶ ∨-comm) ∶ ∨-assoc)) ∶ (∨-congR (symm (∧-comm ∶ superdist1)))))
                          ∶ ∨-congR (∧-congR (∨-cong ((symm ∨-unit) ∶ (∨-congR (symm (∧-comp -comp)))) (((symm ∨-unit) ∶ (symm (∨-congR (∧-comm ∶ (∧-comp -comp))))) ∶ ∨-comm))))))))))))))
                        ∶ (symm ∨-assoc)) ∶ (∨-congL ∨-comm)))) ∶ (∨-congL (symm dist⊹))) ∶ (∨-congL (symm ∧-comm))))
                           ∶ (symm (∨-congR (∧-congR (∧-cong (∨-congR comp-colapse) (∨-congR comp-colapse)))))))
                          ∶ (∨-congR (∧-congR (∧-cong (symm Demorgan1) (symm Demorgan1))))) ∶ (∨-congR (∧-congR (symm Demorgan2))))
  -- --≤-asymm (lub (≤-tran lb2 {!   !}) {!   !}) ( lub {! glb  !} {! glb  !} )
  -- --(∨-cong (∧-congR Demorgan2) refl) ∶ (∨-cong (∧-congR (∧-cong Demorgan1 Demorgan1)) refl) ∶ {!   !}  record BA : Set where
