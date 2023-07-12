{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Everything
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Core.Everything
open import Cubical.Algebra.Group
open import Cubical.HITs.PropositionalTruncation
open import Cubical.Homotopy.Loopspace
open import Cubical.Data.Sigma
open import Cubical.Homotopy.Connected

private
  variable
    ℓ : Level

-- Définition de la composante connexe d'un point
BAut : Pointed ℓ → Pointed ℓ
BAut X = ( Σ ⟨ X ⟩ (λ x  → ∥ (pt X) ≡ x ∥₁), (pt X , ∣ refl ∣₁) )

loop-cc-is-loop : {A : Pointed ℓ} → Ω (BAut A) ≃∙ Ω A
loop-cc-is-loop {ℓ} {A} = isoToEquiv e , refl
  where
  e : Iso (fst (Ω (BAut A))) (fst (Ω A))

  -- On projete ((a0, _) ≡ (a0,_)) sur (a0 ≡ a0)
  Iso.fun e p = cong fst p

  -- Pour retourner en arrière on remarque qu'il n'y a qu'un témoin de (∥ x ≡ y ∥₁)
  Iso.inv e p = ΣPathP (p , toPathP (isPropPropTrunc _ _))

  Iso.rightInv e p = refl
  Iso.leftInv e p = isoFunInjective (equivToIso (invEquiv (Σ≡PropEquiv (λ _ → isPropPropTrunc))))  _ _ refl

postulate
  -- Si X et Y pointés connexes et f induit une equivalence ΩX ≃∙ ΩY alors f est une equivalence
  connected-loop-equivalence : {X Y : Pointed ℓ } {f : X →∙ Y} →
    isConnected 0 ⟨ X ⟩ →
    isConnected 0 ⟨ Y ⟩ →
    isEquiv (fst (Ω→ f)) →
    isEquiv (fst f)
