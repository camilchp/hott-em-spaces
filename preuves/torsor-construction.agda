{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Everything
open import Cubical.Core.Everything
open import Cubical.Algebra.Group
open import Cubical.HITs.PropositionalTruncation
open import Cubical.Homotopy.Loopspace

private
  variable
    ℓ : Level

BAut : Pointed ℓ → Type ℓ
BAut X = Σ ⟨ X ⟩ (λ x  → ∥ (pt X) ≡ x ∥₁)

-- postulate
--  loop-cc-is-cc : (X : Pointed ℓ) → Ω X ≃ Ω (BAut X)

module _ (G : Group ℓ) where

  open GroupStr (snd G)
  -- open IsGroup isGroup

  record GroupAction (X : hSet ℓ) : Type ℓ where
    field
      _*_ : ⟨ G ⟩ → ⟨ X ⟩ → ⟨ X ⟩
      unit : (x : ⟨ X ⟩) → 1g * x ≡ x
      composition : (g1 g2 : ⟨ G ⟩) (x : ⟨ X ⟩) → g1 * (g2 * x) ≡ (g1 · g2) * x

  gset = Σ (hSet ℓ) (λ X → GroupAction X)

  left-product : GroupAction (⟨ G ⟩ , isSetGroup G)
  left-product = record {
    _*_ = _·_;
    unit = ·IdL;
    composition = ·Assoc
    }

  -- postulate
  --   left-product : GroupAction (⟨ G ⟩ , isSetGroup G)

  principal-torsor : gset
  principal-torsor = ((⟨ G ⟩ , isSetGroup G) , left-product)

  classifying-space = BAut((gset , principal-torsor))
