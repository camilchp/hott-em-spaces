{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Everything
open import Cubical.Core.Everything
open import Cubical.Algebra.Group
open import Cubical.Reflection.RecordEquiv

private
  variable
    ℓ ℓ' : Level

record Action {G : Group ℓ} {X : Type ℓ} : Type ℓ where
  constructor
    isaction
  field
    _*_ : ⟨ G ⟩ → X → X
    is-set : isSet X
    ·Unit : (x : X) → (str G).GroupStr.1g * x ≡ x
    ·Composition : (g1 g2 : ⟨ G ⟩) (x : X) → g1 * (g2 * x) ≡ ((str G).GroupStr._·_ g1 g2) * x

record GSetStr (X : Type ℓ) : Type (ℓ-suc ℓ) where
  constructor
    gsetsr
  field
    G : Group ℓ
    ϕ : Action {ℓ} {G} {X}

  open Action ϕ public

GSet : ∀ ℓ → Type (ℓ-suc ℓ)
GSet ℓ = TypeWithStr ℓ GSetStr

-- record isgsethom {x : gset ℓ} {y : gset ℓ} (f : ⟨ x ⟩ → ⟨ y ⟩)
--   : type (ℓ-max ℓ ℓ')
--   where

--   -- shorter qualified names
--   private
--     module m = gsetstr (str x)
--     module n = gsetstr (str y)

--   field
--     pres* : (x y : ⟨ x ⟩) → {!!}

module _ (G : Group ℓ) where

  open GroupStr (snd G)

  left-action : Action {ℓ} {G} {⟨ G ⟩}
  left-action = record {
    _*_ = _·_ ;
    is-set = is-set ;
    ·Unit = ·IdL ;
    ·Composition = ·Assoc
    }
