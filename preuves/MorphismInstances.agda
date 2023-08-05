{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Everything
-- open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
import Cubical.Algebra.Group.Properties
private
  variable
    ℓ : Level

module _ (G : Group ℓ) where
  open GroupStr (str G)
  open Cubical.Algebra.Group.Properties.GroupTheory G
  conjugateHom : ⟨ G ⟩ → GroupHom G G
  conjugateHom g = (λ x → g · x · (inv g)) , record {
    pres· = λ x y →
      g · (x · y) · inv g ≡⟨ cong (λ a → g · (a · y) · inv g) (sym (·IdR x)) ⟩
      g · ((x · 1g) · y) · inv g ≡⟨ cong (λ a → g · ((x · a) · y) · inv g) (sym (·InvL g)) ⟩
      g · ((x · (inv g · g)) · y) · inv g ≡⟨ cong (λ a → g · (a · y) · inv g) (·Assoc x (inv g) g) ⟩
      g · (((x · inv g) · g) · y) · inv g ≡⟨ cong (λ a → g · a · inv g) (sym (·Assoc (x · inv g) g y)) ⟩
      g · (((x · inv g) · (g · y)) · inv g) ≡⟨ cong (λ a → g · a) (sym (·Assoc (x · inv g) (g · y) (inv g))) ⟩
      g · ((x · inv g) · ((g · y) · inv g)) ≡⟨ cong ((λ a → g · (x · inv g) · a)) (sym (·Assoc g y (inv g))) ⟩
      g · ((x · inv g) · (g · (y · inv g))) ≡⟨ ·Assoc _ _ _ ⟩
      (g · (x · inv g)) · (g · (y · inv g)) ∎
    ;
    pres1 =
      g · 1g · inv g ≡⟨ cong (λ a → g · a) (·IdL (inv g)) ⟩
      g · inv g ≡⟨ ·InvR g ⟩
      1g ∎
    ;
    presinv = λ x →
      g · inv x · inv g ≡⟨ cong (λ a → g · a) (sym (invDistr g x)) ⟩
      g · inv (g · x) ≡⟨ cong (λ a → a · inv (g · x)) (sym (invInv g)) ⟩
      inv (inv g) · inv (g · x) ≡⟨ sym (invDistr _ _) ⟩
      inv ((g · x) · inv g) ≡⟨ cong inv (sym (·Assoc _ _ _)) ⟩
      inv (g · x · inv g) ∎
    }
