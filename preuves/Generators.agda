{-# OPTIONS --cubical --allow-unsolved-metas #-}

open import Cubical.Foundations.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Univalence
open import Cubical.Core.Everything
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

module _ (G : Group ℓ) (n : ℕ) (g : Fin n → ⟨ G ⟩) where
  open GroupStr (str G)

  Free_n : Group _
  Free_n = freeGroupGroup (Fin n)

  -- prod is the morphism that sends i to (g i), j · k to (g j) · (g k), etc...
  prodHom : GroupHom Free_n G
  prodHom = Cubical.HITs.FreeGroup.rec g
  prod = (fst prodHom)

  generate-strong : Type ℓ
  generate-strong = (g : ⟨ G ⟩) → Σ ⟨ Free_n ⟩ (λ x → prod x ≡ g)

  generate-weak : Type ℓ
  generate-weak = (g : ⟨ G ⟩) → ∃ ⟨ Free_n ⟩ (λ x → prod x ≡ g)

  postulate
    -- This is a consequence of the axiom of choice
    weak-generation : ∥ generate-strong ∥₁ ≃ generate-weak