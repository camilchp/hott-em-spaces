{-# OPTIONS --cubical --allow-unsolved-metas #-}

open import Cubical.Foundations.Everything
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Core.Everything
open import Cubical.Algebra.Group
open import Cubical.HITs.PropositionalTruncation
open import Cubical.Homotopy.Loopspace
open import Cubical.Data.Sigma
open import Cubical.Foundations.Equiv.Fiberwise
open import Cubical.Homotopy.Connected

open import BAut
open import GSet

private
  variable
    ℓ : Level

module delooping (G : Group ℓ) where

  open GroupStr (snd G)

  -- action de G sur lui-même par multiplication à gauche
  left-action : Action {ℓ} G ⟨ G ⟩
  left-action = record {
    _*_ = _·_ ;
    is-set = is-set ;
    ·Unit = ·IdL ;
    ·Composition = ·Assoc
    }

  -- On appelle le GSet correspondant "torseur principal de G"
  PG : GSet ℓ G
  PG = ⟨ G ⟩ , gsetstr left-action

  -- La composante connexe de PG dans les GSets est appelée BG, "espace classifiant de G".
  BG : Pointed _
  BG = BAut (GSet ℓ G , PG)

  lemme : ⟨ G ⟩ ≃ (PG ≡ PG)
  lemme = compEquiv carac GSetUnivalence
    where
      carac : ⟨ G ⟩ ≃ GSetEquiv PG PG
      carac = isoToEquiv e
        where
          open GSetStr (str PG)
          _·₁_ = GroupStr._·_ (str G)
          1g₁ = GroupStr.1g (str G)
          inv₁ = GroupStr.inv (str G)

          f : ⟨ G ⟩ → Iso (⟨ PG ⟩) (⟨ PG ⟩)
          f g = f'
            where
            f' : Iso (⟨ PG ⟩) (⟨ PG ⟩)
            Iso.fun f' = λ x → x ·₁ g
            Iso.inv f' = λ x → x ·₁ (inv₁ g)
            Iso.rightInv f' x =
              (x ·₁ (inv₁ g)) ·₁ g ≡⟨ sym (·Assoc x (inv₁ g) g) ⟩
              x ·₁ ((inv₁ g) ·₁ g) ≡⟨ cong (λ y → x ·₁ y) (·InvL g) ⟩
              x ·₁ 1g₁ ≡⟨ ·IdR x ⟩
              x ∎
            Iso.leftInv f' x =
              (x ·₁ g) ·₁ (inv₁ g) ≡⟨ sym (·Assoc x g (inv₁ g)) ⟩
              x ·₁ (g ·₁ (inv₁ g)) ≡⟨ cong (λ y → x ·₁ y) (·InvR g) ⟩
              x ·₁ 1g₁ ≡⟨ ·IdR x ⟩
              x ∎

          e : Iso (⟨ G ⟩) (GSetEquiv PG PG)
          Iso.fun e g = (isoToEquiv (f g)) , (record { pres* = (λ g' x → sym (·Assoc g' x g))})
          Iso.inv e f = fst (fst f) 1g₁
          Iso.rightInv e f = ΣPathP ((ΣPathP (ext-equal ,
            toPathP (isPropIsEquiv (fst (fst f)) (subst (isEquiv) ext-equal (snd (fst (Iso.fun e (Iso.inv e (f)))))) (snd (fst f))))) , toPathP (isPropIsGSetHom (fst (fst f)) ((subst (λ h → IsGSetHom (str PG) h (str PG)) ext-equal (snd (Iso.fun e (Iso.inv e (f)))))) (snd f)))
            where
              ext-equal = funExt (λ x →
                x ·₁ (fst (fst f) 1g₁) ≡⟨ sym (IsGSetHom.pres* (snd f) x 1g₁) ⟩
                fst (fst f) (x ·₁ 1g₁) ≡⟨ cong (fst (fst f)) (·IdR x) ⟩
                (fst (fst f ) x) ∎
                )
          Iso.leftInv e g = ·IdL g

  -- L'espace classifiant de G est un délooping de G
  torsor-delooping : Ω BG ≃∙ (⟨ G ⟩ , 1g)
  torsor-delooping = compEquiv∙ loop-cc-is-loop ((invEquiv (lemme)) , {!!})
