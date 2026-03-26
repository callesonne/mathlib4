/-
Copyright (c) 2026 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Calle Sönne
-/
module

public import Mathlib.CategoryTheory.Bicategory.FunctorBicategory.Pseudo
public import Mathlib.CategoryTheory.Bicategory.Opposites

/-!
# 2-Yoneda embedding

In this file we define the bicategorical Yoneda embedding.

-/

@[expose] public section

namespace CategoryTheory

open Bicategory Bicategory.Opposite Opposite Pseudofunctor StrongTrans

universe w v u

namespace Bicategory

section

variable {B : Type u} [Bicategory.{w, v} B]

/-- Version of `Bicategory.precomposing` viewed in the bicategory `Cat`. -/
@[simps]
def precomposingCat (a b c : B) :
    (a ⟶ b) ⥤ (Cat.of (b ⟶ c) ⟶ Cat.of (a ⟶ c)) where
  obj f := (precomp c f).toCatHom
  map η := NatTrans.toCatHom₂ ((precomposing a b c).map η)

/-- Version of `Bicategory.postcomposing` viewed in the bicategory `Cat`. -/
@[simps]
def postcomposingCat (a b c : B) : (b ⟶ c) ⥤ (Cat.of (a ⟶ b) ⟶ Cat.of (a ⟶ c)) where
  obj f := (postcomp a f).toCatHom
  map η := NatTrans.toCatHom₂ ((postcomposing a b c).map η)

/-- Left unitor as a 2-isomorphism in `Cat`. -/
@[simps!]
def leftUnitorNatIsoCat (a b : B) : (precomposingCat _ _ b).obj (𝟙 a) ≅ 𝟙 (Cat.of (a ⟶ b)) :=
  Cat.Hom.isoMk <| NatIso.ofComponents (λ_ ·)

/-- Right component of the associator as a 2-isomorphism in `Cat`. -/
@[simps!]
def associatorNatIsoRightCat {a b c : B} (f : a ⟶ b) (g : b ⟶ c) (d : B) :
    (precomposingCat _ _ d).obj (f ≫ g) ≅
      (precomposingCat ..).obj g ≫ (precomposingCat ..).obj f :=
  Cat.Hom.isoMk <| NatIso.ofComponents (α_ f g ·)

set_option backward.isDefEq.respectTransparency false in
/-- Middle component of the associator as a 2-isomorphism in `Cat`. -/
@[simps!]
def associatorNatIsoMiddleCat {a b c d : B} (f : a ⟶ b) (h : c ⟶ d) :
    (precomposingCat ..).obj f ≫ (postcomposingCat ..).obj h ≅
      (postcomposingCat ..).obj h ≫ (precomposingCat ..).obj f :=
  Cat.Hom.isoMk <| NatIso.ofComponents (α_ f · h)

/-- Right unitor as a 2-isomorphism in `Cat`. -/
@[simps!]
def rightUnitorNatIsoCat (a b : B) : (postcomposingCat a _ _).obj (𝟙 b) ≅ 𝟙 (Cat.of (a ⟶ b)) :=
  Cat.Hom.isoMk <| NatIso.ofComponents (ρ_ ·)

set_option backward.isDefEq.respectTransparency false in
/-- Left component of the associator as a 2-isomorphism in `Cat`. -/
@[simps!]
def associatorNatIsoLeftCat (a : B) {b c d : B} (g : b ⟶ c) (h : c ⟶ d) :
    (postcomposingCat a ..).obj g ≫ (postcomposingCat ..).obj h ≅
      (postcomposingCat ..).obj (g ≫ h) :=
  Cat.Hom.isoMk <| NatIso.ofComponents (α_ · g h)

set_option backward.isDefEq.respectTransparency false in
/-- The map on objects underlying the Yoneda embedding. It sends an object `x` to
the pseudofunctor defined by:
* Objects: `a ↦ (a ⟶ x)`
* Higher morphisms get sent to the corresponding "precomposing" operation.

This is only used for defining `yoneda`, after which `Bicategory.yoneda.obj` should be preferred. -/
@[simps!]
def yoneda₀ (x : B) : Pseudofunctor Bᵒᵖ Cat.{w, v} where
  toPrelaxFunctor := PrelaxFunctor.mkOfHomFunctors (fun y => Cat.of (unop y ⟶ x))
    (fun a b => unopFunctor a b ⋙ precomposingCat (unop b) (unop a) x)
  mapId a := leftUnitorNatIsoCat (unop a) x
  mapComp f g := associatorNatIsoRightCat g.unop f.unop x

set_option backward.isDefEq.respectTransparency false in
/-- Postcomposing of a 1-morphism seen as a strong transformation between pseudofunctors. -/
@[simps!]
def postcomp₂ {a b : B} (f : a ⟶ b) : yoneda₀ a ⟶ yoneda₀ b where
  app x := (postcomposingCat (unop x) a b).obj f
  naturality g := associatorNatIsoMiddleCat g.unop f

set_option backward.isDefEq.respectTransparency false in
/-- Postcomposing of `1`-morphisms seen as a functor from `a ⟶ b` to the hom-category of the
corresponding pseudofunctors.

This is an implementation detail, and `Bicategory.yoneda.map` should be preferred. -/
@[simps!]
def postcomposing₂ (a b : B) : (a ⟶ b) ⥤ (yoneda₀ a ⟶ yoneda₀ b) where
  obj := postcomp₂
  map η := { as := { app x := (postcomposingCat (unop x) a b).map η }}

set_option backward.isDefEq.respectTransparency false in
/-- The Yoneda pseudofunctor from `B` to `Bᵒᵖ ⥤ᵖ Cat`.

It consists of the following:
* On objects: sends `x : B` to the pseudofunctor `Bᵒᵖ ⥤ᵖ Cat` given by
  `a ↦ (a ⟶ x)` on objects and on 1- and 2-morphisms given by "precomposing"
* On 1- and 2-morphisms it is given by "postcomposing" -/
@[simps!]
def yoneda : B ⥤ᵖ Bᵒᵖ ⥤ᵖ Cat.{w, v} where
  toPrelaxFunctor := PrelaxFunctor.mkOfHomFunctors (yoneda₀ ·) postcomposing₂
  mapId a := isoMk (fun b => rightUnitorNatIsoCat (unop b) a)
  mapComp f g := (isoMk (fun b ↦ associatorNatIsoLeftCat (unop b) f g)).symm

end

section

-- Locally Small bicategory
variable {B : Type u} [Bicategory.{v, v} B]

attribute [local simp] Cat.associator_hom_app Cat.associator_inv_app
  Cat.leftUnitor_hom_app Cat.rightUnitor_hom_app
  Cat.leftUnitor_inv_app Cat.rightUnitor_inv_app

def yonedaEquivInv (P : Bᵒᵖ ⥤ᵖ Cat) (a : Bᵒᵖ) :
    ↑(P.obj a) ⥤ (yoneda.obj (unop a) ⟶ P) where
  obj d := {
    -- Again this should be a general construction...? P.mapFunctor ⋙ opFunctor?
    app w :=
      { obj h := (P.map h.op).obj d
        map α := (P.map₂ (op2 α)).app d }
    naturality f := NatIso.ofComponents (fun x ↦ ((P.mapComp x.op f).app d))
    naturality_comp := by
      intros
      ext x
      simp [Cat.app]
      rw [← (P.map _).map_comp]
      simp only [Iso.inv_hom_id_app, Cat.comp_obj, Functor.map_id, comp_id] }
  map f := {
    app x := {
      app X := (P.map (Quiver.Hom.op X)).map f
      naturality f' := sorry
    }
    naturality := sorry
  }
  map_id := sorry
  map_comp := sorry

#exit

def yonedaEquiv [LocallySmallBicategory B] (P : Bᵒᵖ ⥤ᵖ Cat.{u₁, u₁}) (a : Bᵒᵖ) :
    (yoneda.obj (unop a) ⟶ P) ≌ P.obj a where
  -- this should already be a functor in another file
  functor := {
    obj θ := (θ.app a).obj (𝟙 (unop a))
    map Γ := (Γ.app a).app (𝟙 (unop a))
  }
  inverse := yonedaEquivInv P a
  unitIso := sorry
  counitIso := sorry
  functor_unitIso_comp := sorry

#exit

@[simps!] -- probably have some bad simp lemmas here?
def yonedaPairing (P : Bᵒᵖ ⥤ᵖ Cat.{w₁, v₁}) : Bᵒᵖ ⥤ᵖ Cat :=
    (yoneda (B := B)).op.comp (yoneda₀ P)

/- def yonedaEvaluation (P ) -/
--attribute [-simp] Iso.app_hom
-- I don't want to deal w/ universe issues for now
def yonedaLemmaHom [SmallBicategory B] (P : Bᵒᵖ ⥤ᵖ Cat.{u₁, u₁}) :
    (yonedaPairing P) ⟶ P where
  app a := {
    obj θ := (θ.app a).obj (𝟙 (unop a))
    map Γ := (Γ.app a).app (𝟙 (unop a))
  }
  naturality {a b} f := NatIso.ofComponents
    (fun θ =>
      ((θ.app b).mapIso (λ_ f.unop ≪≫ (ρ_ f.unop).symm)) ≪≫
        ( (θ.naturality f).app (𝟙 (unop a)))) -- Cat.Iso.app might not be needed
    (fun {θ τ} Γ => by simp [← Γ.naturality_app f (𝟙 (unop a))])
  naturality_naturality {a b θ τ} Γ := by
    ext x
    simp [← naturality_naturality_app x Γ (𝟙 (unop a))]
  naturality_comp := by
    intros a b c f g
    ext x
    -- Really just applying NatTrans.naturality_assoc here...
    simp
    simp_rw [← Cat.comp_map, ← Functor.map_comp_assoc, ← NatTrans.naturality_assoc]
    -- Should be 1 simp from here...
    simp [- NatTrans.naturality_assoc]
    simp_rw [← Functor.map_comp_assoc]
    simp

end Bicategory

end CategoryTheory
