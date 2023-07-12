\begin{AgdaAlign}
\AgdaHide{
%<*imports>
\begin{code}
{-# OPTIONS --cubical #-}

open import Cubical.Algebra.Group
open import Cubical.Core.Everything
open import Cubical.Foundations.Everything

private
  variable
    ℓ : Level
\end{code}
%</imports>
}
%<*nat>
\begin{code}
record Action (G : Group ℓ) (X : Type ℓ) : Type ℓ where
  field
    _*_          : ⟨ G ⟩ → X → X
    is-set       : isSet X
    ·Unit        : (x : X) → (str G).GroupStr.1g * x ≡ x
    ·Composition : (g1 g2 : ⟨ G ⟩) (x : X) → g1 * (g2 * x) ≡ ((str G).GroupStr._·_ g1 g2) * x

record GSetStr (G : Group ℓ) (X : Type ℓ) : Type ℓ where
  field
    ϕ : Action {ℓ} G X
\end{code}
%</nat>
\end{AgdaAlign}
