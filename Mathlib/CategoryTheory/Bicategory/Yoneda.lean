/-
Copyright (c) 2025 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Calle Sönne
-/

import Mathlib.CategoryTheory.Bicategory.FunctorBicategory.Pseudo
import Mathlib.CategoryTheory.Bicategory.Adjunction.Basic
import Mathlib.CategoryTheory.Bicategory.Functor.Opposites
import Mathlib.CategoryTheory.Bicategory.Opposites
import Mathlib.CategoryTheory.Products.Basic

/-!
# 2-Yoneda embedding

-/

namespace CategoryTheory

open Category Bicategory Bicategory.Opposite Opposite Bicategory.Equivalence

open Bicategory Pseudofunctor StrongTrans

universe w₁ v₁ u₁ w v u

namespace Bicategory

variable {B : Type u₁} [Bicategory.{w₁, v₁} B]

attribute [local simp] Cat.associator_hom_app Cat.associator_inv_app
  Cat.leftUnitor_hom_app Cat.rightUnitor_hom_app
  Cat.leftUnitor_inv_app Cat.rightUnitor_inv_app
/-- The map on objects underlying the Yoneda embedding. It sends an object `x` to
the pseudofunctor defined by:
* Objects: `a ↦ (a ⟶ x)`
* Higher morphisms get sent to the corresponding "precomposing" operation. -/
@[simps!]
def yoneda₀ (x : B) : Pseudofunctor Bᵒᵖ Cat.{w₁, v₁} where
  toPrelaxFunctor := PrelaxFunctor.mkOfHomFunctors (fun y => Cat.of (unop y ⟶ x))
    (fun a b => unopFunctor a b ⋙ precomposing (unop b) (unop a) x)
  mapId a := leftUnitorNatIso (unop a) x
  mapComp f g := associatorNatIsoRight g.unop f.unop x

/-- Postcomposing of a 1-morhisms seen as a strong transformation between pseudofunctors. -/
@[simps!]
def postcomp₂ {a b : B} (f : a ⟶ b) : yoneda₀ a ⟶ yoneda₀ b where
  app x := (postcomposing (unop x) a b).obj f
  naturality g := (associatorNatIsoMiddle g.unop f)

/-- Postcomposing of `1`-morphisms seen as a functor from `a ⟶ b` to the hom-category of the
corresponding pseudofunctors. -/
@[simps!]
def postcomposing₂ (a b : B) : (a ⟶ b) ⥤ (yoneda₀ a ⟶ yoneda₀ b) where
  obj := postcomp₂
  map η := { app x := (postcomposing (unop x) a b).map η }

/-- The yoneda pseudofunctor from `B` to `Pseudofunctor Bᵒᵖ Cat`.

It consists of the following:
* On objects: sends `x : B` to the pseudofunctor `Bᵒᵖ ⥤ Cat` given by
  `a ↦ (a ⟶ x)` on objects and on 1- and 2-morphisms given by "precomposing"
* On 1- and 2-morphisms it is given by "postcomposing" -/
@[simps!]
def yoneda : Pseudofunctor B (Pseudofunctor Bᵒᵖ Cat.{w₁, v₁}) where
  toPrelaxFunctor := PrelaxFunctor.mkOfHomFunctors (fun x ↦ yoneda₀ x) postcomposing₂
  mapId a := isoMk (fun b => rightUnitorNatIso (unop b) a)
  mapComp f g := (isoMk (fun b ↦ associatorNatIsoLeft (unop b) f g)).symm

/-- The map on objects underlying the Yoneda embedding. It sends an object `x` to
the pseudofunctor defined by:
* Objects: `a ↦ (a ⟶ x)`
* Higher morphisms get sent to the corresponding "precomposing" operation. -/
@[simps!]
def coyoneda₀ (x : B) : Pseudofunctor B Cat.{w₁, v₁} where
  toPrelaxFunctor := PrelaxFunctor.mkOfHomFunctors (fun y => Cat.of (x ⟶ y))
    (fun a b => postcomposing x a b)
  mapId a := rightUnitorNatIso x a
  mapComp f g := (associatorNatIsoLeft x f g).symm

/-- Postcomposing of a 1-morhisms seen as a strong transformation between pseudofunctors. -/
@[simps!]
def precomp₂ {a b : B} (f : a ⟶ b) : coyoneda₀ b ⟶ coyoneda₀ a where
  app x := (precomposing a b x).obj f
  naturality g := (associatorNatIsoMiddle f g).symm

/-- Postcomposing of `1`-morphisms seen as a functor from `a ⟶ b` to the hom-category of the
corresponding pseudofunctors. -/
@[simps!]
def precomposing₂ (a b : B) : (a ⟶ b) ⥤ (coyoneda₀ b ⟶ coyoneda₀ a) where
  obj := precomp₂
  map η := { app x := (precomposing a b x).map η }

/-- The yoneda pseudofunctor from `B` to `Pseudofunctor Bᵒᵖ Cat`.

It consists of the following:
* On objects: sends `x : B` to the pseudofunctor `Bᵒᵖ ⥤ Cat` given by
  `a ↦ (a ⟶ x)` on objects and on 1- and 2-morphisms given by "precomposing"
* On 1- and 2-morphisms it is given by "postcomposing" -/
/- @[simps!] -/
/- def coyoneda : Pseudofunctor B (Pseudofunctor B Cat.{w₁, v₁}) where -/
/-   toPrelaxFunctor := PrelaxFunctor.mkOfHomFunctors (fun x ↦ coyoneda₀ x) precomposing₂ -/
/-   mapId a := isoMk (fun b => leftUnitorNatIso a b) -/
/-   mapComp f g := (isoMk (fun b ↦ associatorNatIsoRight f g b)) -/


-- TODO: state cat-level equivalence without universe assumptions

def yonedaEquivInv [LocallySmallBicategory B] (P : Bᵒᵖ ⥤ᵖ Cat) (a : Bᵒᵖ) :
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


-- attribute [-simp] Cat.associator_hom_app Cat.associator_inv_app
--   Cat.leftUnitor_hom_app Cat.rightUnitor_hom_app
--   Cat.leftUnitor_inv_app Cat.rightUnitor_inv_app
/- def yonedaEvaluation (P ) -/
--attribute [-simp] Iso.app_hom
-- I don't want to deal w/ universe issues for now
def yonedaLemmaHom [SmallBicategory B] (P : Bᵒᵖ ⥤ᵖ Cat.{u₁, u₁}) :
    (yonedaPairing P) ⟶ P where
  app a := {
    obj θ := (θ.app a).obj (𝟙 (unop a))
    map Γ := (Γ.app a).app (𝟙 (unop a))
  }
  -- Possibly need Cat.NatIso.ofComponents here
  naturality {a b} f := NatIso.ofComponents
    -- TODO: can I use bicategorical coherence here to simplify?
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


#check NatTrans.naturality
  /- left_triangle := sorry -/

/-
WANT NOW: for any pseudofunctor P, asssoc pseudofunctor from B to ( - "" -) sending C to
Pseudo(yoneda.obj c, P)

Want "evaluation uncurried ..." in this setting. Don't have products of bicategories, so let's do
"evaluatoin curried": Pseudo()
-/

end Bicategory

end CategoryTheory
