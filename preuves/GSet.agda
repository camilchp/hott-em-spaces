{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Everything
open import Cubical.Core.Everything
open import Cubical.Algebra.Group
open import Cubical.Reflection.RecordEquiv
open import Cubical.Data.Sigma

private
  variable
    ℓ : Level

record Action (G : Group ℓ) (X : Type ℓ) : Type ℓ where
  constructor
    action
  field
    _*_ : ⟨ G ⟩ → X → X
    is-set : isSet X
    ·Unit : (x : X) → (str G).GroupStr.1g * x ≡ x
    ·Composition : (g1 g2 : ⟨ G ⟩) (x : X) → g1 * (g2 * x) ≡ ((str G).GroupStr._·_ g1 g2) * x

unquoteDecl ActionIsoΣ = declareRecordIsoΣ ActionIsoΣ (quote Action)

record GSetStr (G : Group ℓ) (X : Type ℓ) : Type ℓ where
  constructor
    gsetsr
  field
    ϕ : Action {ℓ} G X

  open Action ϕ public

unquoteDecl GSetStrIsoΣ = declareRecordIsoΣ GSetStrIsoΣ (quote GSetStr)

GSet : ∀ ℓ →  Group ℓ → Type (ℓ-suc ℓ)
GSet ℓ G = TypeWithStr ℓ (GSetStr G)

-- TODO: can the Levels be different ?
record IsGSetHom {G : Group ℓ} {X Y : Type ℓ} (M : GSetStr G X)  (f : X → Y) (N : GSetStr G Y)
  : Type ℓ
  where

  -- shorter qualified names
  private
    module M = GSetStr M
    module N = GSetStr N

  field
    pres* : (g : ⟨ G ⟩) (x : X ) → f (g M.* x) ≡ g N.* (f x)

unquoteDecl IsGSetHomIsoΣ = declareRecordIsoΣ IsGSetHomIsoΣ (quote IsGSetHom)

GSetHom : {G : Group ℓ} (X Y : GSet ℓ G) → Type ℓ
GSetHom X Y = Σ[ f ∈ (⟨ X ⟩ → ⟨ Y ⟩) ] IsGSetHom (str X) f (str Y)

module _ {G : Group ℓ} {X : Type ℓ} {Y : Type ℓ} {M : GSetStr {ℓ} G X} {f : X → Y} {N : GSetStr {ℓ} G Y}
  (pres : (g : ⟨ G ⟩) (x : X) → f ((GSetStr._*_ M) g x) ≡ (GSetStr._*_ N) g (f x))
  where

  makeIsGSetHom : IsGSetHom M f N
  makeIsGSetHom .IsGSetHom.pres* = pres

GSetIso : {G : Group ℓ} (X Y : GSet ℓ G) → Type ℓ
GSetIso X Y =  Σ[ e ∈ Iso ⟨ X ⟩ ⟨ Y ⟩ ] IsGSetHom (str X) (e .Iso.fun) (str Y)

IsGSetEquiv : {G : Group ℓ} {X Y : Type ℓ}
  (M : GSetStr G X) (e : X ≃ Y) (N : GSetStr G Y) → Type ℓ
IsGSetEquiv M e N = IsGSetHom M (e .fst) N

GSetEquiv : {G : Group ℓ} (X Y : GSet ℓ G) → Type ℓ
GSetEquiv X Y = Σ[ e ∈ (⟨ X ⟩ ≃ ⟨ Y ⟩) ] IsGSetEquiv (str X) e (str Y)

gsetEquivFun : {G : Group ℓ} {X : GSet ℓ G} {Y : GSet ℓ G} → GSetEquiv X Y → ⟨ X ⟩ → ⟨ Y ⟩
gsetEquivFun e = e .fst .fst

GSetEquiv→GSetIso : {G : Group ℓ} {X Y : GSet ℓ G} → GSetEquiv X Y → GSetIso X Y
fst (GSetEquiv→GSetIso e) = equivToIso (fst e)
snd (GSetEquiv→GSetIso e) = snd e

GSetEquivToPath : {G : Group ℓ} {X Y : GSet ℓ G} → GSetEquiv X Y → ⟨ X ⟩ ≡ ⟨ Y ⟩
GSetEquivToPath e = isoToPath (fst (GSetEquiv→GSetIso e))

idGSetIso : {G : Group ℓ} {X : GSet ℓ G} → GSetIso X X
fst idGSetIso = idIso
snd idGSetIso = makeIsGSetHom λ _ _ → refl

idGSetEquiv : {G : Group ℓ} {X : GSet ℓ G} → GSetEquiv X X
fst (idGSetEquiv {X = X}) = idEquiv ⟨ X ⟩
snd idGSetEquiv = makeIsGSetHom λ _ _ → refl

-- The reciprocal of an isomorphism is an isomorphism
isGSetHomInv : {G : Group ℓ} {X : GSet ℓ G} {Y : GSet ℓ G} (f : GSetEquiv X Y) → IsGSetHom (str Y) (invEq (fst f)) (str X)
isGSetHomInv {ℓ} {G} {X} {Y} ((e , eEq) , eHom) = is-hom-h
  where
    h : ⟨ Y ⟩ → ⟨ X ⟩
    h = invEq (e , eEq)

    _⋆₁_ = GSetStr._*_ (str Y)
    _⋆₂_ = GSetStr._*_ (str X)

    sec : (g : ⟨ G ⟩) (y : ⟨ Y ⟩) → y ≡ e (h y)
    sec g y = sym (secEq ((e , eEq)) y)

    hom : (g : ⟨ G ⟩) (y : ⟨ Y ⟩) → g ⋆₁ e (h y) ≡ e (g ⋆₂ h y)
    hom g y = sym (IsGSetHom.pres* eHom g (h y))

    is-hom-h : IsGSetHom (str Y)  h (str X)
    IsGSetHom.pres* is-hom-h g y =
      h (g ⋆₁ y) ≡⟨ cong (λ y' → h (g ⋆₁ y'))  (sec g y) ⟩
      h (g ⋆₁ (e (h y))) ≡⟨ cong h (hom g y) ⟩
      h (e (g ⋆₂ (h y))) ≡⟨ retEq (e , eEq) _ ⟩
      g ⋆₂ (h y) ∎

-- An isomorphism between X and Y induces structure on Y
induce-structure-iso : {G : Group ℓ} {X Y : GSet ℓ G} (f : GSetEquiv X Y) → GSetStr G ⟨ X ⟩ → GSetStr G ⟨ Y ⟩
induce-structure-iso {ℓ} {G} {X} {Y} ((f , fEq) , fHom) (gsetsr (action _*_ is-set ·Unit ·Composition)) = gsetsr (action
  (λ g y →  f (g * (h y)))
  (GSetStr.is-set (str Y))
  ( λ y →
    f ( 1g * (h y)) ≡⟨ cong f (·Unit (h y)) ⟩
    f (h y) ≡⟨ secEq (f , fEq) y ⟩
    y ∎
   )
  ( λ g1 g2 y →
    f (g1 * h (f (g2 * (h y)))) ≡⟨ cong (λ x → f (g1 * x)) (retEq (f , fEq) _) ⟩
    f (g1 * (g2 * (h y))) ≡⟨  cong f (·Composition g1 g2 (h y)) ⟩
    f ((g1 · g2) * (h y)) ∎
  ))
  where

    h : ⟨ Y ⟩ → ⟨ X ⟩
    h = invEq (f , fEq)

    1g : ⟨ G ⟩
    1g = str G .GroupStr.1g

    _·_ : ⟨ G ⟩ → ⟨ G ⟩ → ⟨ G ⟩
    _·_ = str G .GroupStr._·_


GSetEquivIsPath : {G : Group ℓ} {X Y : GSet ℓ G} → GSetEquiv X Y  ≃ (X ≡ Y)
GSetEquivIsPath {ℓ} {G} {X} {Y} = isoToEquiv e
  where
    B : (f : GSetEquiv X Y) → GSetStr G ⟨ X ⟩ ≃ GSetStr G ⟨ Y ⟩
    B ((f , fEq) , fHom) = isoToEquiv e'
      where

        h' :  ⟨ Y ⟩ ≃ ⟨ X ⟩
        h' = invEquiv (f , fEq)

        h = fst h'

        1g : ⟨ G ⟩
        1g = str G .GroupStr.1g

        _·_ : ⟨ G ⟩ → ⟨ G ⟩ → ⟨ G ⟩
        _·_ = str G .GroupStr._·_

        equal-actions : {G : Group ℓ} {X : Type ℓ} (A B : GSetStr G X) → A .GSetStr._*_ ≡ B .GSetStr._*_ → A ≡ B
        equal-actions {G} {X} A B refl =  isoFunInjective (compIso GSetStrIsoΣ ActionIsoΣ) A B
          (ΣPathP (refl ,
            ΣPathP (isPropIsSet _ _ ,
              ΣPathP ( funExt {f = A .GSetStr.·Unit} {g = B .GSetStr.·Unit} (λ _ → toPathP (B .GSetStr.is-set _ _ _ _)) ,
                funExt {f = A .GSetStr.·Composition} {g = B .GSetStr.·Composition} (λ x → toPathP {!!} )))))

        e' : Iso  (GSetStr G ⟨ X ⟩) (GSetStr G ⟨ Y ⟩)
        Iso.fun e' = induce-structure-iso ((f , fEq) , fHom)
        Iso.inv e' = induce-structure-iso (h' , isGSetHomInv (((f , fEq) , fHom)))
        Iso.rightInv e' (gsetsr (action _*_ is-set ·Unit ·Composition)) = (
          (Iso.fun e') ((Iso.inv e') (gsetsr (action _*_ is-set ·Unit ·Composition))) ≡⟨ refl ⟩
          (Iso.fun e') (gsetsr (action
          (λ g x → h (g * (f x)))
          ((GSetStr.is-set (str X)))
          ( λ x →
            h ( 1g * (f x)) ≡⟨ cong h (·Unit (f x)) ⟩
            h (f x) ≡⟨ secEq h' x ⟩
            x ∎
          )
          ( λ g1 g2 x →
              h (g1 * f (h (g2 * (f x)))) ≡⟨ cong (λ y → h (g1 * y)) (retEq h' _) ⟩
              h (g1 * (g2 * (f x))) ≡⟨  cong h (·Composition g1 g2 (f x)) ⟩
              h ((g1 · g2) * (f x)) ∎
              )
          )) ≡⟨ refl ⟩

          (gsetsr (action
            (λ g y → f (h (g * (f (h y)))))
            ((GSetStr.is-set (str Y)))
            ( λ y →
              f (h ( 1g * (f (h y)))) ≡⟨ cong f ((((Iso.inv e') (gsetsr (action _*_ is-set ·Unit ·Composition)) ) .GSetStr.·Unit) (h y)) ⟩
              f (h y) ≡⟨ secEq (f , fEq) y ⟩
              y ∎
            )
            ( λ g1 g2 y →
                f (h (g1 * f (h (f (h (g2 * f (h y))))))) ≡⟨ cong (λ x → f ((((Iso.inv e') (gsetsr (action _*_ is-set ·Unit ·Composition)) ) .GSetStr._*_) g1 x)) (retEq (f , fEq) _) ⟩
                f (h (g1 * (f (h (g2 * f (h y))))))  ≡⟨  cong f ((((Iso.inv e') (gsetsr (action _*_ is-set ·Unit ·Composition))) .GSetStr.·Composition) g1 g2 (h y)) ⟩
                f (h ((g1 · g2) * (f (h y)))) ∎
            )
          )) ≡⟨ {!!} ⟩
          (gsetsr (action _*_ is-set ·Unit ·Composition)) ∎
          )
        Iso.leftInv e' = {!!}

    C : (f : GSetEquiv X Y) → GSetStr G ⟨ X ⟩ ≡ GSetStr G ⟨ Y ⟩
    C f = isoToPath ((equivToIso (B f)))

    e : Iso (GSetEquiv X Y) (X ≡ Y)
    Iso.fun e = λ f → ΣPathP (isoToPath (equivToIso (fst f)) , {!!})
    Iso.inv e = {!!}
    Iso.rightInv e = {!!}
    Iso.leftInv e = {!!}
