{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Everything
open import Cubical.Core.Everything
open import Cubical.Algebra.Group
open import Cubical.HITs.PropositionalTruncation
open import Cubical.Homotopy.Loopspace
open import Cubical.Data.Sigma
open import Cubical.Foundations.Equiv.Fiberwise
open import Cubical.Homotopy.Connected

open import Actions

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

-- Le loop space d'un point dans un espace est son loop-space dans sa composante connexe
loop-cc-is-loop : {A : Pointed ℓ} → Ω (BAut A) ≃∙ Ω A
loop-cc-is-loop {ℓ} {A} = (encode-decode-loops {ℓ} {BAut A}
  code
  c0
  decode
  encode-decode
  {!!}
  ) , {!!}
  where
  a0 : ⟨ A ⟩
  a0 = pt A

  a0' : ⟨ BAut A ⟩
  a0' = (a0 , ∣ refl ∣₁)

  code : (x : ⟨ BAut A ⟩) → Type ℓ
  code = (λ (x , _) → a0 ≡ x)

  c0 : code (a0 , ∣ refl ∣₁)
  c0 = refl

  decode : (x : ⟨ BAut A ⟩) → code x → pt (BAut A) ≡ x
  decode (x , t) p = ΣPathP (p , toPathP (isPropPropTrunc _ t ))

  encode-decode : (c : code a0') → ((subst⁻ code (decode a0' c) c0) ≡ c)
  encode-decode c =  {!!}

loop-cc-is-loop' : {A : Pointed ℓ} → Ω (BAut A) ≃∙ Ω A
loop-cc-is-loop' {ℓ} {A} = recognizeId {ℓ} {ℓ} {⟨ BAut A ⟩} {a0'} (λ (x , _) → a0 ≡ x) refl ((a0' , refl) , contract)  {!!}  , {!!} where

  a0 : ⟨ A ⟩
  a0 = pt A

  a0' : ⟨ BAut A ⟩
  a0' = pt (BAut A)

  contract :  (y : Σ ⟨ BAut A ⟩ (λ x → a0 ≡ fst x)) → ( a0' , refl) ≡ y
  contract ((x , t) , p) = ΣPathP ((ΣPathP (p , toPathP (isPropPropTrunc _ t))) , {!!})


postulate
  -- Si X et Y pointés connexes et f induit une equivalence ΩX ≃∙ ΩY alors f est une equivalence
  connected-loop-equivalence : {X Y : Pointed ℓ } {f : X →∙ Y} →
    isConnected 0 ⟨ X ⟩ →
    isConnected 0 ⟨ Y ⟩ →
    isEquiv (fst (Ω→ f)) →
    isEquiv (fst f)
