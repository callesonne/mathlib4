/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.CategoryTheory.Bicategory.Strict.Basic
import Mathlib.CategoryTheory.ConcreteCategory.Bundled
import Mathlib.CategoryTheory.Discrete.Basic
import Mathlib.CategoryTheory.Types.Basic

/-!
# Category of categories

This file contains the definition of the category `Cat` of all categories.
In this category objects are categories and
morphisms are functors between these categories.

## Implementation notes

Though `Cat` is not a concrete category, we use `bundled` to define
its carrier type.
-/


universe v u

namespace CategoryTheory

open Bicategory Functor

-- intended to be used with explicit universe parameters
/-- Category of categories. -/
@[nolint checkUnivs]
def Cat :=
  Bundled Category.{v, u}

namespace Cat

instance : Inhabited Cat :=
  ⟨⟨Type u, CategoryTheory.types⟩⟩

-- TODO: maybe this coercion should be defined to be `objects.obj`?
instance : CoeSort Cat (Type u) :=
  ⟨Bundled.α⟩

instance str (C : Cat.{v, u}) : Category.{v, u} C :=
  Bundled.str C

/-- Construct a bundled `Cat` from the underlying type and the typeclass. -/
def of (C : Type u) [Category.{v} C] : Cat.{v, u} :=
  Bundled.of C

/-- Bicategory structure on `Cat` -/
instance bicategory : Bicategory.{max v u, max v u} Cat.{v, u} where
  Hom C D := C ⥤ D
  id C := 𝟭 C
  comp F G := F ⋙ G
  homCategory := fun _ _ => Functor.category
  whiskerLeft {_} {_} {_} F _ _ η := whiskerLeft F η
  whiskerRight {_} {_} {_} _ _ η H := whiskerRight η H
  associator {_} {_} {_} _ := Functor.associator
  leftUnitor {_} _ := Functor.leftUnitor
  rightUnitor {_} _ := Functor.rightUnitor
  pentagon := fun {_} {_} {_} {_} {_}=> Functor.pentagon
  triangle {_} {_} {_} := Functor.triangle

/-- `Cat` is a strict bicategory. -/
instance bicategory.strict : Bicategory.Strict Cat.{v, u} where
  id_comp {C} {D} F := by cases F; rfl
  comp_id {C} {D} F := by cases F; rfl
  assoc := by intros; rfl

/-- Category structure on `Cat` -/
instance category : LargeCategory.{max v u} Cat.{v, u} :=
  StrictBicategory.category Cat.{v, u}

/-- Synonym for `NatTrans.app` to help with automation. -/
abbrev app {C D : Cat} {F G : C ⟶ D} (α : F ⟶ G) (x : C) := α.app x

/-- Synonym for `Iso.app` to help with automation. -/
abbrev Iso.app {C D : Cat} {F G : C ⟶ D} (α : F ≅ G) (x : C) := α.app x

@[simp]
lemma Iso.app_hom {C D : Cat} {F G : C ⟶ D} (α : F ≅ G) (x : C) :
    (Iso.app α x).hom = Cat.app α.hom x :=
  rfl

@[simp]
lemma Iso.app_inv {C D : Cat} {F G : C ⟶ D} (α : F ≅ G) (x : C) :
    (Iso.app α x).inv = Cat.app α.inv x :=
  rfl

@[ext]
theorem ext {C D : Cat} {F G : C ⟶ D} {α β : F ⟶ G} (w : app α = app β) : α = β :=
  NatTrans.ext w

@[simp]
theorem id_obj {C : Cat} (X : C) : (𝟙 C : C ⥤ C).obj X = X :=
  rfl

@[simp]
theorem id_map {C : Cat} {X Y : C} (f : X ⟶ Y) : (𝟙 C : C ⥤ C).map f = f :=
  rfl

@[simp]
theorem comp_obj {C D E : Cat} (F : C ⟶ D) (G : D ⟶ E) (X : C) : (F ≫ G).obj X = G.obj (F.obj X) :=
  rfl

@[simp]
theorem comp_map {C D E : Cat} (F : C ⟶ D) (G : D ⟶ E) {X Y : C} (f : X ⟶ Y) :
    (F ≫ G).map f = G.map (F.map f) :=
  rfl

@[simp]
theorem id_app {C D : Cat} (F : C ⟶ D) (X : C) : app (𝟙 F : F ⟶ F) X = 𝟙 (F.obj X) := rfl

@[simp]
theorem comp_app {C D : Cat} {F G H : C ⟶ D} (α : F ⟶ G) (β : G ⟶ H) (X : C) :
    app (α ≫ β) X = app α X ≫ app β X := rfl

@[simp]
theorem eqToHom_app {C D : Cat} (F G : C ⟶ D) (h : F = G) (X : C) :
    app (eqToHom h) X = eqToHom (Functor.congr_obj h X) :=
  CategoryTheory.eqToHom_app h X

@[simp]
lemma whiskerLeft_app {C D E : Cat} (F : C ⟶ D) {G H : D ⟶ E} (η : G ⟶ H) (X : C) :
    app (F ◁ η) X = app η (F.obj X) :=
  rfl

@[simp]
lemma whiskerRight_app {C D E : Cat} {F G : C ⟶ D} (H : D ⟶ E) (η : F ⟶ G) (X : C) :
    app (η ▷ H) X = H.map (app η X) :=
  rfl

lemma leftUnitor_hom_app {B C : Cat} (F : B ⟶ C) (X : B) : app (λ_ F).hom X = eqToHom (by simp) :=
  rfl

lemma leftUnitor_inv_app {B C : Cat} (F : B ⟶ C) (X : B) : app (λ_ F).inv X = eqToHom (by simp) :=
  rfl

lemma rightUnitor_hom_app {B C : Cat} (F : B ⟶ C) (X : B) : app (ρ_ F).hom X = eqToHom (by simp) :=
  rfl

lemma rightUnitor_inv_app {B C : Cat} (F : B ⟶ C) (X : B) : app (ρ_ F).inv X = eqToHom (by simp) :=
  rfl

lemma associator_hom_app {B C D E : Cat} (F : B ⟶ C) (G : C ⟶ D) (H : D ⟶ E) (X : B) :
    app (α_ F G H).hom X = eqToHom (by simp) :=
  rfl

lemma associator_inv_app {B C D E : Cat} (F : B ⟶ C) (G : C ⟶ D) (H : D ⟶ E) (X : B) :
    app (α_ F G H).inv X = eqToHom (by simp) :=
  rfl

/-- The identity in the category of categories equals the identity functor. -/
theorem id_eq_id (X : Cat) : 𝟙 X = 𝟭 X := rfl

/-- Composition in the category of categories equals functor composition. -/
theorem comp_eq_comp {X Y Z : Cat} (F : X ⟶ Y) (G : Y ⟶ Z) : F ≫ G = F ⋙ G := rfl

@[simp] theorem of_α (C) [Category C] : (of C).α = C := rfl

@[simp] theorem coe_of (C : Cat.{v, u}) : Cat.of C = C := rfl

end Cat

namespace Functor

/-- Functors between categories of the same size define arrows in `Cat`. -/
def toCatHom {C D : Type u} [Category.{v} C] [Category.{v} D] (F : C ⥤ D) :
    Cat.of C ⟶ Cat.of D := F

/-- Arrows in `Cat` define functors. -/
def ofCatHom {C D : Type} [Category C] [Category D] (F : Cat.of C ⟶ Cat.of D) : C ⥤ D := F

@[simp] theorem to_ofCatHom {C D : Type} [Category C] [Category D] (F : Cat.of C ⟶ Cat.of D) :
    (ofCatHom F).toCatHom = F := rfl

@[simp] theorem of_toCatHom {C D : Type} [Category C] [Category D] (F : C ⥤ D) :
    ofCatHom (F.toCatHom) = F := rfl

end Functor
namespace Cat

/-- Functor that gets the set of objects of a category. It is not
called `forget`, because it is not a faithful functor. -/
def objects : Cat.{v, u} ⥤ Type u where
  obj C := C
  map F := F.obj

/-- See through the defeq `objects.obj X = X`. -/
instance (X : Cat.{v, u}) : Category (objects.obj X) := inferInstanceAs <| Category X

section

attribute [local simp] eqToHom_map

/-- Any isomorphism in `Cat` induces an equivalence of the underlying categories. -/
def equivOfIso {C D : Cat} (γ : C ≅ D) : C ≌ D where
  functor := γ.hom
  inverse := γ.inv
  unitIso := eqToIso <| Eq.symm γ.hom_inv_id
  counitIso := eqToIso γ.inv_hom_id

/-- Under certain hypotheses, an equivalence of categories actually
defines an isomorphism in `Cat`. -/
@[simps]
def isoOfEquiv {C D : Cat.{v, u}} (e : C ≌ D)
    (h₁ : ∀ (X : C), e.inverse.obj (e.functor.obj X) = X)
    (h₂ : ∀ (Y : D), e.functor.obj (e.inverse.obj Y) = Y)
    (h₃ : ∀ (X : C), app e.unitIso.hom X = eqToHom (h₁ X).symm := by cat_disch)
    (h₄ : ∀ (Y : D), app e.counitIso.hom Y = eqToHom (h₂ Y) := by cat_disch) :
    C ≅ D where
  hom := e.functor
  inv := e.inverse
  hom_inv_id := (Functor.ext_of_iso e.unitIso (fun X ↦ (h₁ X).symm) h₃).symm
  inv_hom_id := (Functor.ext_of_iso e.counitIso h₂ h₄)

end

end Cat

/-- Embedding `Type` into `Cat` as discrete categories.

This ought to be modelled as a 2-functor!
-/
@[simps]
def typeToCat : Type u ⥤ Cat where
  obj X := Cat.of (Discrete X)
  map := fun f => Discrete.functor (Discrete.mk ∘ f)
  map_id X := by
    apply Functor.ext
    · intro X Y f
      cases f
      simp only [eqToHom_refl, Cat.id_map, Category.comp_id, Category.id_comp]
      apply ULift.ext
      cat_disch
    · simp
  map_comp f g := by apply Functor.ext; cat_disch

instance : Functor.Faithful typeToCat.{u} where
  map_injective {_X} {_Y} _f _g h :=
    funext fun x => congr_arg Discrete.as (Functor.congr_obj h ⟨x⟩)

instance : Functor.Full typeToCat.{u} where
  map_surjective F := ⟨Discrete.as ∘ F.obj ∘ Discrete.mk, by
    apply Functor.ext
    · intro x y f
      dsimp
      apply ULift.ext
      cat_disch
    · rintro ⟨x⟩
      apply Discrete.ext
      rfl⟩

end CategoryTheory
