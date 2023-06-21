{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Everything
open import Cubical.Core.Everything
open import Cubical.Algebra.Group
open import Cubical.HITs.PropositionalTruncation
open import Cubical.Homotopy.Loopspace
open import Cubical.Data.Sigma

private
  variable
    ℓ : Level

-- Définition de la composante connexe d'un point
BAut : Pointed ℓ → Pointed ℓ
BAut X = ( Σ ⟨ X ⟩ (λ x  → ∥ (pt X) ≡ x ∥₁), (pt X , ∣ refl ∣₁) )

-- Lemme encode-décode pour les loop-spaces (HoTT Lemme 8.9.1)
postulate
  -- plutôt recognizeId
  encode-decode-loops : {A : Pointed ℓ} (code : ⟨ A ⟩ → Type ℓ)
    → (c0 : code (pt A))
    → (decode : (x : ⟨ A ⟩) → (code x → (pt A ≡ x)))
    → ((c : code (pt A)) → ((subst⁻ code (decode (pt A) c) c0) ≡ c))
    → (decode (pt A) c0 ≡ refl)
    → (pt A ≡ pt A) ≃ code (pt A)

  Σ-≡-intro :
    ∀ {α β}{A : Type α}{B : A → Type β}{a a' : A}{b : B a}{b' : B a'}
    → (Σ (a ≡ a') λ p → subst B p b ≡ b') → (a , b) ≡ (a' , b')

-- Le loop space d'un point dans un espace est son loop-space dans sa composante connexe
loop-cc-is-loop : {A : Pointed ℓ} → Ω (BAut A) ≃∙ Ω A
loop-cc-is-loop {ℓ} {A} = (encode-decode-loops {ℓ} {BAut A}
  (λ (x , _) → pt A ≡ x)  -- code
  refl                     -- c0 ≡ (a0 = a0)
  decode -- (λ (x , t) p → Σ-≡-intro (p , (squash₁ {!!} {!!})))
  {!!}
  {!!}
  ) , {!!}
  where
  decode : (x : ⟨ BAut A ⟩) → pt A ≡ fst x → pt (BAut A) ≡ x
  decode (x , t) p = ΣPathP (p , {!!})


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

  principal-torsor : gset
  principal-torsor = ((⟨ G ⟩ , isSetGroup G) , left-product)

  classifying-space = BAut((gset , principal-torsor))
