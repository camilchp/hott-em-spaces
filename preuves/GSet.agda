{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Everything
open import Cubical.Core.Everything
open import Cubical.Algebra.Group
open import Cubical.Reflection.RecordEquiv

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

GSetEquivIsPath : {G : Group ℓ} {X Y : GSet ℓ G} → GSetEquiv X Y  ≃ (X ≡ Y)
GSetEquivIsPath {ℓ} {G} {X} {Y} = isoToEquiv e
  where
  e : Iso (GSetEquiv X Y) (X ≡ Y)
  Iso.fun e = λ f → {!isoToEquiv ?!}
  Iso.inv e = {!!}
  Iso.rightInv e = {!!}
  Iso.leftInv e = {!!}
