{-# OPTIONS --cubical --allow-unsolved-metas #-}

open import Cubical.Foundations.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Univalence
open import Cubical.Core.Everything
open import Cubical.Algebra.Monoid
open import Cubical.Algebra.Semigroup
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Reflection.RecordEquiv
open import Cubical.Data.Sigma
open import Cubical.HITs.FreeGroup
open import Cubical.Data.Fin
open import Cubical.Data.Nat
open import Cubical.HITs.PropositionalTruncation

open import GSet


private
  variable
    ℓ : Level

-- (X ≃ X) has a group structure. Note that f·g is f∘g and not g∘f !
AutGroup : (X : hSet ℓ) → Group ℓ
AutGroup (X , trc) = (X ≃ X) ,
  groupstr (idEquiv X) (λ f g → compEquiv g f) invEquiv (
    isgroup (
      ismonoid (
        issemigroup (isOfHLevel≃ 2 trc trc) {!!})
        compEquivIdEquiv compEquivEquivId)
      invEquiv-is-linv
      invEquiv-is-rinv)


-- TODO: An Action G ↷ X is a group morphism from G to (X ≃ X)
-- TODO: Rewrite by renaming
leftMul : {G : Group ℓ} {X : hSet ℓ} → Action G ⟨ X ⟩ → ⟨ G ⟩ → ⟨ X ⟩ ≃ ⟨ X ⟩
leftMul {G = G} {X = X} ϕ g = isoToEquiv e
  where
    e : Iso ⟨ X ⟩ ⟨ X ⟩
    Iso.fun e = Action._*_ ϕ g
    Iso.inv e = Action._*_ ϕ (str G .GroupStr.inv g)
    Iso.rightInv e x = (Action.·Composition ϕ _ _ _) ∙ cong (λ y → Action._*_ ϕ y x) (str G .GroupStr.·InvR g) ∙ Action.·Unit ϕ _
    Iso.leftInv e x = (Action.·Composition ϕ _ _ _) ∙ cong (λ y → Action._*_ ϕ y x) (str G .GroupStr.·InvL g) ∙ Action.·Unit ϕ _


actionToMorphism : {G : Group ℓ} {X : hSet ℓ} → Action G ⟨ X ⟩ → GroupHom G (AutGroup X)
actionToMorphism {G = G} {X = (X , trc)} ϕ = (λ g → leftMul {X = (X , trc)} ϕ g ) ,
  record {
    pres· = λ x y → ΣPathP ((funExt (λ z → sym (Action.·Composition ϕ _ _ _))) , toPathP (isPropIsEquiv _ _ _)) ;
    pres1 = ΣPathP ((funExt (Action.·Unit ϕ)) , toPathP (isPropIsEquiv _ _ _)) ;
    presinv = λ x → ΣPathP ({!!} , {!!})
    }


module _ (G : Group ℓ) (n : ℕ) (g : Fin n → ⟨ G ⟩) where
  import Generators
  import torsor-construction
  open Generators.Generation G n g
  open torsor-construction.delooping G
  open GroupStr (str G) renaming (_·_ to _·₁_ ; inv to inv₁ ; 1g to 1g₁)

  EquivLeftMul : (g : ⟨ G ⟩) → (⟨ G ⟩ ≃ ⟨ G ⟩)
  EquivLeftMul g = isoToEquiv e
    where
      e : Iso ⟨ G ⟩ ⟨ G ⟩
      Iso.fun e x = g ·₁ x
      Iso.inv e x = inv₁ g ·₁ x
      Iso.rightInv e y =
        g ·₁ (inv₁ g ·₁ y) ≡⟨ ·Assoc _ _ _ ⟩
        (g ·₁ inv₁ g) ·₁ y ≡⟨ cong (λ x → x ·₁ y) (·InvR g) ⟩
        1g₁ ·₁ y ≡⟨ ·IdL y ⟩
        y ∎
      Iso.leftInv e y =
        inv₁ g ·₁ (g ·₁ y) ≡⟨ ·Assoc _ _ _ ⟩
        (inv₁ g ·₁ g) ·₁ y ≡⟨ cong (λ x → x ·₁ y) (·InvL g) ⟩
        1g₁ ·₁ y ≡⟨ ·IdL y ⟩
        y ∎

  fg : Fin n → ⟨ G ⟩ → ⟨ G ⟩
  fg i x = (g i) ·₁ x

  commutingSquares : (X : hSet ℓ) (f : Fin n → (⟨ X ⟩ ≃ ⟨ X ⟩)) → Type ℓ
  commutingSquares X f = Σ (⟨ X ⟩ ≃ ⟨ G ⟩) (λ h → (i : Fin n) → (fst h) ∘ (fst (f i)) ≡ (fg i) ∘ (fst h) )

  commutingSquaresAction : (X : hSet ℓ) (f : Fin n → (⟨ X ⟩ ≃ ⟨ X ⟩)) → Type ℓ
  commutingSquaresAction X f = Σ (Action G ⟨ X ⟩) (λ ϕ → (i : Fin n) (x : ⟨ X ⟩) → (Action._*_ ϕ) (g i) x ≡ (fst (f i)) x)


  module decomposition-tools ((X , trc) : hSet ℓ) (f : Fin n → X ≃ X) (comSq : commutingSquares (X , trc) f) where
    hEq = fst comSq
    h = fst hEq
    h⁻¹ = invEq hEq


    -- We have a group morphism  i₁⋯i ↦ f₁⋯fₙ
    compfHom : GroupHom Free_n (AutGroup (X , trc))
    compfHom = Cubical.HITs.FreeGroup.rec f
    compf = fst compfHom

    -- We know that fᵢ = h⁻¹ ∘ (gᵢ · _) ∘ h
    hDecomp : (i : Fin n) → fst (f i) ≡ h⁻¹ ∘ (fg i) ∘ h
    hDecomp i =
      fst (f i) ≡⟨ cong (λ x → x ∘ fst (f i)) (sym (funExt (retEq hEq))) ⟩
      h⁻¹ ∘ h ∘ fst (f i) ≡⟨ cong (λ x → h⁻¹ ∘ x) ((snd comSq) i) ⟩
      h⁻¹ ∘ (fg i) ∘ h ∎

    -- TODO: Factor to show that this is a composition of Group Homomorphisms
    HomHDecomp : GroupHom Free_n (AutGroup (X , trc))
    HomHDecomp = (λ x → compEquiv hEq (compEquiv (EquivLeftMul (prod x)) (invEquiv hEq))) ,
      record {
        pres· = λ x y →
         compEquiv hEq (compEquiv (EquivLeftMul (prod (((str Free_n) .GroupStr._·_ x) y))) (invEquiv hEq)) ≡⟨ cong (λ x → compEquiv hEq (compEquiv (EquivLeftMul x) (invEquiv hEq))) (((snd prodHom) .IsGroupHom.pres·) x y) ⟩
         compEquiv hEq (compEquiv (EquivLeftMul (prod x ·₁ (prod y))) (invEquiv hEq)) ≡⟨ cong ((λ x → compEquiv hEq (compEquiv x (invEquiv hEq)))) (EquivLeftMulPres· _ _) ⟩
         compEquiv hEq (compEquiv (compEquiv (EquivLeftMul (prod y)) (EquivLeftMul (prod x))) (invEquiv hEq)) ≡⟨ cong {!λ a → compEquiv hEq (compEquiv (compEquiv a (EquivLeftMul (prod x))) (invEquiv hEq))!} (compEquivEquivId (EquivLeftMul (prod y))) ⟩
         compEquiv hEq (compEquiv (compEquiv (compEquiv (EquivLeftMul (prod y)) (idEquiv ⟨ G ⟩)) (EquivLeftMul (prod x))) (invEquiv hEq)) ≡⟨ {!!} ⟩
         compEquiv hEq (compEquiv (compEquiv (compEquiv (EquivLeftMul (prod y)) (compEquiv (invEquiv hEq) hEq)) (EquivLeftMul (prod x))) (invEquiv hEq)) ≡⟨ {!!} ⟩
         compEquiv hEq (compEquiv (compEquiv (EquivLeftMul (prod y)) (EquivLeftMul (prod x))) (invEquiv hEq)) ≡⟨ {!!} ⟩
         compEquiv (compEquiv hEq (compEquiv (EquivLeftMul (prod y)) (invEquiv hEq))) (compEquiv hEq (compEquiv (EquivLeftMul (prod x)) (invEquiv hEq))) ∎
        ;
        pres1 =
          compEquiv hEq (compEquiv (EquivLeftMul (prod ((str Free_n) .GroupStr.1g))) (invEquiv hEq)) ≡⟨ cong (λ x → compEquiv hEq (compEquiv (EquivLeftMul x) (invEquiv hEq))) ((snd prodHom) .IsGroupHom.pres1) ⟩
          compEquiv hEq (compEquiv (EquivLeftMul 1g₁) (invEquiv hEq)) ≡⟨ cong ((λ x → compEquiv hEq (compEquiv x (invEquiv hEq)))) EquivLeftMulPres1 ⟩
          compEquiv hEq (compEquiv (idEquiv ⟨ G ⟩) (invEquiv hEq)) ≡⟨ cong (λ x → compEquiv hEq x) (compEquivIdEquiv (invEquiv hEq)) ⟩
          compEquiv hEq (invEquiv hEq) ≡⟨ invEquiv-is-rinv hEq ⟩
          idEquiv X ∎
        ;
        presinv = {!!}
     }

       where

         EquivLeftMulPres· : (x y : ⟨ G ⟩) → EquivLeftMul (x ·₁ y) ≡ compEquiv (EquivLeftMul y) (EquivLeftMul x)
         EquivLeftMulPres· x y = ΣPathP (funExt (λ a →
             (fst (EquivLeftMul (x ·₁ y)) a ≡⟨ refl ⟩
             (x ·₁ y) ·₁ a ≡⟨ sym (·Assoc _ _ _) ⟩
             x ·₁ (y ·₁ a) ≡⟨ refl ⟩
             fst (EquivLeftMul x) (fst (EquivLeftMul y) a) ∎)
           ), toPathP (isPropIsEquiv (fst (compEquiv (EquivLeftMul y) (EquivLeftMul x))) _ _)) -- TODO: Fonction qui dit qu'il suffit que les fonctions soient égales pr que les Equiv le soient ?

         EquivLeftMulPres1 : EquivLeftMul (1g₁) ≡ idEquiv ⟨ G ⟩
         EquivLeftMulPres1 = ΣPathP ((funExt (λ x → ·IdL x)) , toPathP (isPropIsEquiv (fst (idEquiv ⟨ G ⟩)) _ _))

         EquivLeftMulPresInv : (x : ⟨ G ⟩) → EquivLeftMul (inv₁ x) ≡ invEquiv (EquivLeftMul x)
         EquivLeftMulPresInv = {!!}

         EquivLeftMulHom : GroupHom G (AutGroup (⟨ G ⟩ , (str G) .GroupStr.is-set))
         EquivLeftMulHom = EquivLeftMul , record { pres· = EquivLeftMulPres· ; pres1 = EquivLeftMulPres1 ; presinv = EquivLeftMulPresInv }

         -- EquivLeftMulHom = EquivLeftMul , record { pres· = EquivLeftMulPres· ; pres1 = EquivLeftMulPres1 ; presinv = EquivLeftMulPresInv }

    -- TODO: Renommer
    decomposition : compfHom ≡ HomHDecomp
    decomposition = freeGroupHom≡ λ i →
      fst compfHom (η i) ≡⟨ refl ⟩
      f i ≡⟨ lem ⟩
      fst HomHDecomp (η i) ∎

      where

        lem : {i : Fin n} → f i ≡ fst HomHDecomp (η i)
        lem {i = i} = ΣPathP (hDecomp i , toPathP (isPropIsEquiv (fst (fst HomHDecomp (η i))) _ _))

    -- TODO: Rename
    decompose : {g : ⟨ G ⟩} {x : X} {decomp : generateStrong} → fst (compf (fst (decomp g))) x ≡ h⁻¹ (g ·₁ (h x))
    decompose {g = g'} {x = x} {decomp = decomp} =
      fst (compf (fst (decomp g'))) x ≡⟨ cong (λ y → fst (fst y (fst (decomp g'))) x) decomposition ⟩
      fst (fst HomHDecomp (fst (decomp g'))) x ≡⟨ refl ⟩
       h⁻¹ ((prod (fst (decomp g'))) ·₁ (h x)) ≡⟨ cong (λ y → h⁻¹ (y ·₁ (h x))) (snd (decomp g')) ⟩
      h⁻¹ (g' ·₁ (h x)) ∎

    unique_action : generateStrong → isContr(commutingSquaresAction (X , trc) f)
    unique_action decomp = (generateAction , generatedActionCommutesSquares) , isPropCommutingSquareAction
      where

      generateAction : Action G X
      generateAction = action
        _*_
        trc
        ·unit
        ·assoc

        where

          _*_ : ⟨ G ⟩ → X → X
          _*_ g x = fst (compf (fst (decomp g))) x

          ·unit : (x : X) → 1g₁ * x ≡ x
          ·unit x =
            1g₁ * x ≡⟨ decompose {decomp = decomp} ⟩
            h⁻¹ (1g₁ ·₁ (h x)) ≡⟨ cong h⁻¹ (·IdL (h x)) ⟩
            h⁻¹ (h x) ≡⟨ retEq hEq x ⟩
            x ∎

          ·assoc : (g1 g2 : ⟨ G ⟩) (x : X) → g1 * (g2 * x) ≡ (g1 ·₁ g2) * x
          ·assoc g1 g2 x =
            g1 * (g2 * x) ≡⟨ cong (λ x → g1 * x) (decompose {decomp = decomp}) ⟩
            g1 * (h⁻¹ (g2 ·₁ (h x))) ≡⟨ decompose {decomp = decomp} ⟩
            h⁻¹ (g1 ·₁ (h (h⁻¹ (g2 ·₁ (h x))))) ≡⟨ cong (λ g' → h⁻¹ (g1 ·₁ g')) (secEq hEq _) ⟩
            h⁻¹ (g1 ·₁ (g2 ·₁ (h x))) ≡⟨  cong h⁻¹ (·Assoc _ _ _) ⟩
            h⁻¹ ((g1 ·₁ g2) ·₁ (h x)) ≡⟨ sym (decompose {decomp = decomp}) ⟩
            (g1 ·₁ g2) * x ∎

      generatedActionCommutesSquares : (i : Fin n) (x : X) → (generateAction Action.* g i) x ≡ fst (f i) x
      generatedActionCommutesSquares i x =
        (generateAction Action.* g i) x ≡⟨ decompose {decomp = decomp} ⟩
        h⁻¹ (g i ·₁ (h x)) ≡⟨ sym (funExt⁻ (hDecomp i) x) ⟩
        fst (f i) x ∎


      isPropCommutingSquareAction : (ϕ : commutingSquaresAction (X , trc) f) → (generateAction , generatedActionCommutesSquares) ≡ ϕ
      isPropCommutingSquareAction (ϕ , pϕ) = ΣPathP (equalActions generateAction ϕ (funExt λ g' → (funExt λ x →
                                  fst (compf (fst (decomp g'))) x ≡⟨ cong (λ a → fst (fst a (fst (decomp g'))) x) (sym wordToActionIsCompf) ⟩
                                  fst (fst wordToAction (fst (decomp g'))) x ≡⟨ lem (fst (decomp g')) x ⟩
                                  (prod (fst (decomp g')) *₁ x) ≡⟨ cong (λ a → a *₁ x) (snd (decomp g')) ⟩
                                  (g' *₁ x) ∎
                                  )), toPathP (isPropΠ2 (λ _ _ → trc _ _) _ _))
                                  where
                                    _*₁_ = Action._*_ ϕ

                                    wordToAction : GroupHom Free_n (AutGroup (X , trc))
                                    wordToAction = Cubical.HITs.FreeGroup.rec λ i → fst (actionToMorphism {X = (X , trc)} ϕ) (g i)

                                    wordToActionIsCompf : wordToAction ≡ compfHom
                                    wordToActionIsCompf = freeGroupHom≡ λ i →
                                      fst wordToAction (η i) ≡⟨ refl ⟩
                                      fst (actionToMorphism ϕ) (g i) ≡⟨ refl ⟩
                                      ((_*₁_) (g i) , _) ≡⟨ ΣPathP (funExt (pϕ i) , toPathP (isPropIsEquiv _ _ _)) ⟩
                                      f i ≡⟨ refl ⟩
                                      fst compfHom (η i) ∎

                                    -- TODO: rename
                                    lem : (w : ⟨ Free_n ⟩) (x : X) → fst (fst wordToAction w) x ≡ (prod w) *₁ x
                                    lem = Cubical.HITs.FreeGroup.elimProp {B = λ w' → (x' : X) → fst (fst wordToAction w') x' ≡ (prod w') *₁ x'}
                                      (λ w' → isPropΠ (λ x' → trc _ _))
                                      (λ i → λ x' → refl)
                                      (λ w1 w2 p1 p2 x' →
                                        fst (fst wordToAction (w1 ·₂ w2)) x' ≡⟨ cong (λ x → fst x x') ((snd wordToAction) .IsGroupHom.pres· w1 w2) ⟩
                                        fst (fst wordToAction w1) (fst (fst wordToAction w2) x') ≡⟨ cong (fst (fst wordToAction w1)) (p2 x') ⟩
                                        fst (fst wordToAction w1) ((prod w2) *₁ x') ≡⟨ p1 ((prod w2) *₁ x') ⟩
                                        prod w1 *₁ ((prod w2) *₁ x') ≡⟨ ϕ .Action.·Composition _ _ _ ⟩
                                        (prod w1 ·₁ prod w2) *₁ x' ≡⟨ cong ((λ x → x *₁ x')) ((snd prodHom) .IsGroupHom.pres· w1 w2) ⟩
                                        prod (w1 ·₂ w2) *₁ x' ∎)
                                      (λ x' →
                                        fst (fst wordToAction ε) x' ≡⟨ cong (λ x → fst x x') ((snd wordToAction) .IsGroupHom.pres1) ⟩
                                         x' ≡⟨ sym (ϕ .Action.·Unit x') ⟩
                                         1g₁ *₁ x' ≡⟨ cong (λ x → x *₁ x') (sym ((snd prodHom) .IsGroupHom.pres1)) ⟩
                                         prod ε *₁ x' ∎)
                                      (λ w' p x' →
                                        fst (fst wordToAction (inv₂ w')) x' ≡⟨ cong (λ x → fst x x') ((snd wordToAction) .IsGroupHom.presinv w') ⟩
                                        fst (invEquiv (fst wordToAction w')) x' ≡⟨ {!!} ⟩
                                        fst (invEquiv (fst wordToAction w')) x' ≡⟨ {!!} ⟩
                                        inv₁ (prod w') *₁ x' ≡⟨ cong (λ x → x *₁ x') (sym ((snd prodHom) .IsGroupHom.presinv w')) ⟩
                                        (prod (inv₂ w')) *₁ x' ∎)

                                        where
                                          _·₂_ = GroupStr._·_ (str Free_n)
                                          inv₂ = GroupStr.inv (str Free_n)



  isContrCommutingSquaresAction : (X : hSet ℓ) (f : Fin n → (⟨ X ⟩ ≃ ⟨ X ⟩)) → generateStrong → ∥ commutingSquares X f ∥₁ → isContr(commutingSquaresAction X f)
  isContrCommutingSquaresAction (X , trc) f decomp = Cubical.HITs.PropositionalTruncation.elim (λ _ → isPropIsContr) (λ comSq → (decomposition-tools.unique_action (X , trc) f comSq decomp))

  minimalConstruction : Type (ℓ-suc ℓ)
  minimalConstruction = Σ (hSet ℓ) (λ X → Σ (Fin n → ⟨ X ⟩ ≃ ⟨ X ⟩) (λ f → ∥ commutingSquares X f ∥₁))

  zeBigTheorem : generateStrong → minimalConstruction ≃ ⟨ BG ⟩
  zeBigTheorem decomp = isoToEquiv e

    where

      e : Iso minimalConstruction ⟨ BG ⟩
      Iso.fun e (X , (f , comSq)) = Xgset , equalsPG comSq
        where

          ϕcom = fst (isContrCommutingSquaresAction X f decomp comSq)
          ϕ = fst ϕcom

          _*_ = ϕ .Action._*_

          Xgset : GSet ℓ G
          Xgset = (⟨ X ⟩ , gsetstr ϕ)

          gse : commutingSquares X f → (GSetEquiv PG Xgset)
          gse comSq = invEquiv hEq , isGSetHomInv hEq (record { pres* = λ g' x →
                h (g' * x) ≡⟨ (cong h ((lem ≡$S g') ≡$S x)) ⟩
                h (fst (compf (fst (decomp g'))) x) ≡⟨  cong h (decompose {g = g'} {x = x} {decomp = decomp}) ⟩
                h (h⁻¹ ( g' ·₁ (h x))) ≡⟨ secEq hEq (g' ·₁ (h x)) ⟩
                (str PG .GSetStr._*_ g' (h x)) ∎
              })
              where
                open decomposition-tools X f comSq

                XgsetIsTheRightAction :  ϕ ≡ (fst (fst (unique_action decomp)))
                XgsetIsTheRightAction = sym (cong fst (snd (unique_action decomp) ϕcom))

                lem : _*_ ≡ (λ g x → fst (compf (fst (decomp g))) x)
                lem = cong (λ x → x .Action._*_) XgsetIsTheRightAction

          equalsPG : ∥ commutingSquares X f ∥₁ → ∥ PG ≡ Xgset ∥₁
          equalsPG = Cubical.HITs.PropositionalTruncation.elim (λ _ → isPropPropTrunc) λ comSq → ∣ fst GSetUnivalence (gse comSq) ∣₁

      Iso.inv e (Xgset , equalsPG) = (⟨ Xgset ⟩ ,  trc) , f , squaresDoCommute equalsPG
        where
          X : hSet ℓ
          X = ⟨ Xgset ⟩ , str Xgset .GSetStr.is-set

          _*_ = str Xgset .GSetStr._*_
          trc = str Xgset .GSetStr.is-set
          ϕ = action {G = G} _*_ trc (str Xgset .GSetStr.·Unit) (str Xgset .GSetStr.·Composition)

          f : Fin n → ⟨ X ⟩ ≃ ⟨ X ⟩
          f i = leftMul {X = X} ϕ (g i)

          squaresDoCommute : ∥ PG ≡ Xgset ∥₁ → ∥ commutingSquares X f ∥₁
          squaresDoCommute = Cubical.HITs.PropositionalTruncation.elim (λ _ → isPropPropTrunc)
            λ p → ∣ squaresDoCommute-revealed p ∣₁
            where
              squaresDoCommute-revealed : (PG ≡ Xgset) → commutingSquares X f
              squaresDoCommute-revealed equalsPG = (pathToEquiv p) , (λ i → funExt λ x →
                  subst (λ x → x) p (fst (f i) x) ≡⟨ refl ⟩
                  subst (λ x → x) p ((g i) * x) ≡⟨ {!p'!} ⟩
                  (g i) ·₁ subst (λ x → x) p x ∎
                )
                where
                  p : ⟨ X ⟩ ≡ ⟨ G ⟩
                  p = fst (PathPΣ (sym equalsPG))

                  p' = snd (PathPΣ (sym equalsPG))

      Iso.rightInv e = {!!}
      Iso.leftInv e (X , (f , comSq)) = {!!}
