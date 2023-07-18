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
open import Generators


private
  variable
    ℓ : Level

-- (X ≃ X) has a group structure. Note that f·g is f∘g and not g∘f !
AutGroup : {X : hSet ℓ} → Group ℓ
AutGroup {X = (X , trc)} = (X ≃ X) ,
  groupstr (idEquiv X) (λ f g → compEquiv g f) invEquiv (
    isgroup (
      ismonoid (
        issemigroup (isOfHLevel≃ 2 trc trc) {!!})
        compEquivIdEquiv compEquivEquivId)
      invEquiv-is-linv
      invEquiv-is-rinv)


-- An Action G ↷ X is a group morphism from G to (X ≃ X)
-- ActionMorphismEquiv : Action G X ≃

module _ (G : Group ℓ) (n : ℕ) (g : Fin n → ⟨ G ⟩) where
  open Generators
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

  minBG : Type (ℓ-suc ℓ)
  minBG = Σ (hSet ℓ) (λ X → Σ (Fin n → (⟨ X ⟩ ≃ ⟨ X ⟩)) (λ f → ∥ commutingSquares X f ∥₁))

  commutingSquaresAction : (X : hSet ℓ) (f : Fin n → (⟨ X ⟩ ≃ ⟨ X ⟩)) → Type ℓ
  commutingSquaresAction X f = Σ (Action G ⟨ X ⟩) (λ ϕ → (i : Fin n) (x : ⟨ X ⟩) → (Action._*_ ϕ) (g i) x ≡ (fst (f i)) x)

  isContrCommutingSquaresAction : (X : hSet ℓ) (f : Fin n → (⟨ X ⟩ ≃ ⟨ X ⟩)) → generateStrong G n g → ∥ commutingSquares X f ∥₁ → isContr(commutingSquaresAction X f)
  isContrCommutingSquaresAction (X , trc) f decomp = Cubical.HITs.PropositionalTruncation.elim (λ _ → isPropIsContr) (λ comSq → unique_action comSq)

    where

      unique_action : commutingSquares (X , trc) f → isContr(commutingSquaresAction (X , trc) f)
      unique_action comSq = (generateAction , {!!}) , λ y → isPropCommutingSquareAction _ y
        where

        -- We have a group morphism  i₁⋯i ↦ f₁⋯fₙ
        compfHom : GroupHom (Free_n G n g) (AutGroup {X = (X , trc)})
        compfHom = Cubical.HITs.FreeGroup.rec f
        compf = fst compfHom

        hEq = fst comSq
        h = fst hEq
        h⁻¹ = invEq hEq

        -- We know that fᵢ = h⁻¹ ∘ (gᵢ · _) ∘ h
        hDecomp : (i : Fin n) → fst (f i) ≡ h⁻¹ ∘ (fg i) ∘ h
        hDecomp i =
          fst (f i) ≡⟨ cong (λ x → x ∘ fst (f i)) {!!} ⟩
          h⁻¹ ∘ h ∘ fst (f i) ≡⟨ cong (λ x → h⁻¹ ∘ x) ((snd comSq) i) ⟩
          h⁻¹ ∘ (fg i) ∘ h ∎

        -- TODO: Factor to show that this is a composition of Group Homomorphisms
        HomHDecomp : GroupHom (Free_n G n g) (AutGroup {X = (X , trc)})
        HomHDecomp = (λ x → compEquiv hEq (compEquiv (EquivLeftMul (prod G n g x)) (invEquiv hEq))) ,
          record {
            pres· = λ x y →
             compEquiv hEq (compEquiv (EquivLeftMul (prod G n g (((str (Free_n G n g)) .GroupStr._·_ x) y))) (invEquiv hEq)) ≡⟨ cong (λ x → compEquiv hEq (compEquiv (EquivLeftMul x) (invEquiv hEq))) (((snd (prodHom G n g)) .IsGroupHom.pres·) x y) ⟩
             compEquiv hEq (compEquiv (EquivLeftMul ((prod G n g x) ·₁ (prod G n g y))) (invEquiv hEq)) ≡⟨ cong ((λ x → compEquiv hEq (compEquiv x (invEquiv hEq)))) EquivLeftMulPres· ⟩
             compEquiv hEq (compEquiv (compEquiv (EquivLeftMul (prod G n g y)) (EquivLeftMul (prod G n g x))) (invEquiv hEq)) ≡⟨ cong {!!} {!!} ⟩
             compEquiv (compEquiv hEq (compEquiv (EquivLeftMul (prod G n g y)) (invEquiv hEq))) (compEquiv hEq (compEquiv (EquivLeftMul (prod G n g x)) (invEquiv hEq))) ∎
            ;
            pres1 =
              compEquiv hEq (compEquiv (EquivLeftMul (prod G n g ((str (Free_n G n g)) .GroupStr.1g))) (invEquiv hEq)) ≡⟨ cong (λ x → compEquiv hEq (compEquiv (EquivLeftMul x) (invEquiv hEq))) ((snd (prodHom G n g)) .IsGroupHom.pres1) ⟩
              compEquiv hEq (compEquiv (EquivLeftMul 1g₁) (invEquiv hEq)) ≡⟨ cong ((λ x → compEquiv hEq (compEquiv x (invEquiv hEq)))) EquivLeftMulPres1 ⟩
              compEquiv hEq (compEquiv (idEquiv ⟨ G ⟩) (invEquiv hEq)) ≡⟨ cong (λ x → compEquiv hEq x) (compEquivIdEquiv (invEquiv hEq)) ⟩
              compEquiv hEq (invEquiv hEq) ≡⟨ invEquiv-is-rinv hEq ⟩
              idEquiv X ∎
            ;
            presinv = {!!}
         }

           where

             -- TODO: Factoriser en GroupEquivLeftMul
             EquivLeftMulPres· : {x y : ⟨ G ⟩} → EquivLeftMul (x ·₁ y) ≡ compEquiv (EquivLeftMul y) (EquivLeftMul x)
             EquivLeftMulPres· {x = x} {y = y} = ΣPathP (funExt (λ a →
                 (fst (EquivLeftMul (x ·₁ y)) a ≡⟨ refl ⟩
                 (x ·₁ y) ·₁ a ≡⟨ sym (·Assoc _ _ _) ⟩
                 x ·₁ (y ·₁ a) ≡⟨ refl ⟩
                 fst (EquivLeftMul x) (fst (EquivLeftMul y) a) ∎)
               ), toPathP (isPropIsEquiv (fst (compEquiv (EquivLeftMul y) (EquivLeftMul x))) _ _)) -- TODO: Fonction qui dit qu'il suffit que les fonctions soient égales pr que les Equiv le soient ?

             EquivLeftMulPres1 : EquivLeftMul (1g₁) ≡ idEquiv ⟨ G ⟩
             EquivLeftMulPres1 = ΣPathP ((funExt (λ x → ·IdL x)) , toPathP (isPropIsEquiv (fst (idEquiv ⟨ G ⟩)) _ _))

        -- TODO: Renommer
        decomposition : compfHom ≡ HomHDecomp
        decomposition = freeGroupHom≡ λ i →
          fst compfHom (η i) ≡⟨ refl ⟩
          f i ≡⟨ lem ⟩
          fst HomHDecomp (η i) ∎

          where

            lem : {i : Fin n} → f i ≡ fst HomHDecomp (η i)
            lem {i = i} = ΣPathP (hDecomp i , toPathP (isPropIsEquiv (fst (fst HomHDecomp (η i))) _ _))

        generateAction : Action G X
        generateAction = action
          _*_
          trc
          ∙unit
          ·assoc

          where

            _*_ : ⟨ G ⟩ → X → X
            _*_ g x = fst (compf (fst (decomp g))) x

            -- TODO: Rename
            decompose : {g : ⟨ G ⟩} {x : X} → fst (compf (fst (decomp g))) x ≡ h⁻¹ (g ·₁ (h x))
            decompose {g = g'} {x = x} =
              fst (compf (fst (decomp g'))) x ≡⟨ cong (λ y → fst (fst y (fst (decomp g'))) x) decomposition ⟩
              fst (fst HomHDecomp (fst (decomp g'))) x ≡⟨ refl ⟩
               h⁻¹ ((prod G n g (fst (decomp g'))) ·₁ (h x)) ≡⟨ cong (λ y → h⁻¹ (y ·₁ (h x))) (snd (decomp g')) ⟩
              h⁻¹ (g' ·₁ (h x)) ∎

            ∙unit : (x : X) → 1g₁ * x ≡ x
            ∙unit x =
              1g₁ * x ≡⟨ decompose ⟩
              h⁻¹ (1g₁ ·₁ (h x)) ≡⟨ cong h⁻¹ (·IdL (h x)) ⟩
              h⁻¹ (h x) ≡⟨ retEq hEq x ⟩
              x ∎

            ·assoc : (g1 g2 : ⟨ G ⟩) (x : X) → g1 * (g2 * x) ≡ (g1 ·₁ g2) * x
            ·assoc g1 g2 x =
              g1 * (g2 * x) ≡⟨ cong (λ x → g1 * x) decompose ⟩
              g1 * (h⁻¹ (g2 ·₁ (h x))) ≡⟨ decompose ⟩
              h⁻¹ (g1 ·₁ (h (h⁻¹ (g2 ·₁ (h x))))) ≡⟨ cong (λ g' → h⁻¹ (g1 ·₁ g')) (secEq hEq _) ⟩
              h⁻¹ (g1 ·₁ (g2 ·₁ (h x))) ≡⟨  cong h⁻¹ (·Assoc _ _ _) ⟩
              h⁻¹ ((g1 ·₁ g2) ·₁ (h x)) ≡⟨ sym decompose ⟩
              (g1 ·₁ g2) * x ∎

        isPropCommutingSquareAction : isProp(commutingSquaresAction (X , trc) f)
        isPropCommutingSquareAction (ϕ , pϕ) (ψ , pψ) = ΣPathP (equalActions ϕ ψ (funExt λ g' → funExt λ x →
                                    (g' *₁ x) ≡⟨ {!!} ⟩
                                    (prod G n g (fst (decomp g')) *₁ x) ≡⟨ {!!} ⟩
                                    (prod G n g (fst (decomp g')) *₁ x) ≡⟨ {!!} ⟩
                                    (g' *₂ x) ∎
                                    ), {!!})
                                    where
                                    _*₁_ = Action._*_ ϕ
                                    _*₂_ = Action._*_ ψ
