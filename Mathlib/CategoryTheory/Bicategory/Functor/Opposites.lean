/-
Copyright (c) 2025 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Calle Sönne
-/
import Mathlib.CategoryTheory.Bicategory.Opposites
import Mathlib.CategoryTheory.Bicategory.Functor.Pseudofunctor

namespace CategoryTheory

open Category Bicategory Opposite Bicategory.Opposite

universe w₁ w₂ w₃ v₁ v₂ v₃ u₁ u₂ u₃

variable {B : Type u₁} [Bicategory.{w₁, v₁} B] {C : Type u₂} [Bicategory.{w₂, v₂} C]
variable {D : Type u₃} [Bicategory.{w₃, v₃} D]

namespace Pseudofunctor

/-- TODO -/
@[simps!]
nonrec def op (P : Pseudofunctor B C) : Pseudofunctor Bᵒᵖ Cᵒᵖ where 
  obj a := op (P.obj (unop a))
  map f := (P.map f.unop).op
  map₂ η := op2 (P.map₂ η.unop2)
  mapId a := (P.mapId (unop a)).op2
  mapComp f g := (P.mapComp g.unop f.unop).op2
  map₂_associator f g h := congrArg op2 <| by sorry 

end Pseudofunctor


end CategoryTheory
