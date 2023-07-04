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

-- Actions that coincide are equal
equalActions : {G : Group ℓ} {X : Type ℓ} (A B : GSetStr G X) → A .GSetStr._*_ ≡ B .GSetStr._*_ → A ≡ B
equalActions {G} {X} A B refl =  isoFunInjective (compIso GSetStrIsoΣ ActionIsoΣ) A B
  (ΣPathP (refl ,
    ΣPathP (isPropIsSet _ _ ,
      ΣPathP ( (funExt (λ _ → toPathP (B .GSetStr.is-set _ _ _ _))) ,
      funExt λ _ →
        funExt λ _ →
          funExt λ _ → toPathP (B .GSetStr.is-set _ _ _ _)))))

-- (GSetStr G X) is a set (the set of actions of G on X)
IsSetGSetStr : {G : Group ℓ} {X : Type ℓ} → isSet(GSetStr G X)
IsSetGSetStr {G = G} {X = X} s1 s2 p1 p2 = cong (λ z → (cong (Iso.inv GSetStrIsoΣ) (cong (Iso.inv ActionIsoΣ) z)))
  (cong ΣPathP
    (ΣPathP ( isSet→ {A' = X → X} {A = ⟨ G ⟩} (isSet→ {A' = X} {A = X} (GSetStr.is-set s1)) (GSetStr._*_ s1) (GSetStr._*_ s2) p1* p2* , {!!})))
  where
    p1' = PathPΣ (cong (Iso.fun ActionIsoΣ) (cong (Iso.fun GSetStrIsoΣ) p1))
    p1* = fst p1'
    p2' = PathPΣ (cong (Iso.fun ActionIsoΣ) (cong (Iso.fun GSetStrIsoΣ) p2))
    p2* = fst p2'

    p1-is-set = fst (PathPΣ (snd p2'))

postulate
  lemme-prop : {G : Group ℓ} {X : Type ℓ} → isSet(GSetStr G X)

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

postulate
  -- We can calculate the induced structure of an equivalence
  transport-* : {G : Group ℓ} {X Y : GSet ℓ G} {fEq : ⟨ X ⟩ ≃ ⟨ Y ⟩} →
    subst (λ A → ⟨ G ⟩ → A → A) (ua fEq) (GSetStr._*_ (str X)) ≡ λ g y → (fst fEq) ((GSetStr._*_ (str X)) g ((invEq fEq) y))
  -- transport-* {ℓ} {G} {X} {Y} {fEq} =
  --   subst (λ A → ⟨ G ⟩ → A → A) (ua fEq) (_*x_) ≡⟨ {!funTypeTransp {A = Type ℓ} (λ A → ⟨ G ⟩) (λ A → A → A) {x = ⟨ X ⟩} {y = ⟨ Y ⟩} (ua fEq) (_*x_)!} ⟩
  --   (λ g → subst (λ A → A → A) (ua fEq) (λ z → (subst (λ A → ⟨ G ⟩) (sym (ua fEq)) g) *x z)) ≡⟨ {!!} ⟩
  --   (λ g → subst (λ A → A → A) (ua fEq) (λ z → g *x z)) ≡⟨ {!!} ⟩
  --   (λ g y → subst (λ A → A) (ua fEq) (g *x (subst (λ A → A ) (sym (ua fEq)) y))) ≡⟨ {!!} ⟩
  --   (λ g y → (fst fEq) (g *x ((invEq fEq) y))) ∎
  --   where
  --     _*x_ = GSetStr._*_ (str X)
  --     f = fst fEq
  --     h = fst (invEquiv fEq)

theorem : {G : Group ℓ} {X Y : GSet ℓ G} → (GSetEquiv X Y) ≃ (X ≡ Y)
theorem {ℓ} {G} {X} {Y} = isoToEquiv e
  where

    _*y_ = GSetStr._*_ (str Y)
    _*x_ = GSetStr._*_ (str X)

    e : Iso (GSetEquiv X Y) (X ≡ Y)
    Iso.fun e f = ΣPathP (ua (fst f) , toPathP (equalActions induced-structure (str Y) induced-action-≡-action))
      where

        h' = invEquiv (fst f)
        h = invEq (fst f)
        fFun = fst (fst f)

        induced-structure : GSetStr G ⟨ Y ⟩
        induced-structure = transport (λ i → GSetStr G (ua (fst f) i)) (str X)

        _*i_ = GSetStr._*_ induced-structure

        -- We want to show that *y ≡ *i.

        -- We have shown that g *i y ≡ f (g *x (h y))
        postulate
          lem1 : (g : ⟨ G ⟩) (y : ⟨ Y ⟩) → g *i y ≡ fFun (g *x (h y))

        -- Since h is a GSetHom,  f (g *x (h y)) ≣ f h(g *y y) ≡ g *y y
        lem2 : (g : ⟨ G ⟩) (y : ⟨ Y ⟩) → (g *i y) ≡ (g *y y)
        lem2 g y =
          g *i y ≡⟨ lem1 g y ⟩
          fFun ( g *x (h y)) ≡⟨ cong fFun (sym ((IsGSetHom.pres* (isGSetHomInv f)) g y)) ⟩
          fFun ( h (g *y y)) ≡⟨ secEq (fst f) (g *y y) ⟩
          g *y y ∎

        -- By function extensionality we have *y ≡ *i
        induced-action-≡-action : _*i_ ≡ _*y_
        induced-action-≡-action = funExt  λ _ → funExt λ _ → (lem2 _ _)

    Iso.inv e p = fEq , record { pres* = fHom }
      where
        -- p is a tuple containing :
        --   · a path between underlying sets
        --   · a path between their structures over the first path.
        p-sig = PathPΣ p

        -- that first path induces an equivalence
        fEq : ⟨ X ⟩ ≃ ⟨ Y ⟩
        fEq = pathToEquiv (fst p-sig)
        f : ⟨ X ⟩ → ⟨ Y ⟩
        f = fst fEq

        hEq : ⟨ Y ⟩ ≃ ⟨ X ⟩
        hEq = invEquiv fEq
        h : ⟨ Y ⟩ → ⟨ X ⟩
        h = fst hEq

        -- the second tells us f respects structure.
        fHom : (g : ⟨ G ⟩) (x : ⟨ X ⟩) → f (g *x x) ≡ g *y (f x)
        fHom g x =
          f (g *x x) ≡⟨ cong (λ z → f (g *x z)) x-y  ⟩
          f (g *x (h y)) ≡⟨ (sym (lem1 g y)) ∙ lem3 g y ⟩
          g *y y ≡⟨ refl ⟩
          g *y (f x) ∎
          where

            y : ⟨ Y ⟩
            y = f x

            x-y : x ≡ h y
            x-y = sym (secEq hEq x)

            _*i_ : ⟨ G ⟩ → ⟨ Y ⟩ → ⟨ Y ⟩
            _*i_ = GSetStr._*_ (transport (λ i → GSetStr G (fst (p-sig) i)) (str X))

            postulate
              lem1 : (g : ⟨ G ⟩) (y : ⟨ Y ⟩) → g *i y ≡ f (g *x (h y))
              lem2 : _*i_ ≡ _*y_
              lem3 : (g : ⟨ G ⟩) (y : ⟨ Y ⟩) → g *i y ≡ g *y y

    Iso.rightInv e p = cong ΣPathP (ΣPathP (ua-pathToEquiv (fst (PathPΣ p)) , {!!}))
    Iso.leftInv e = {!!}
