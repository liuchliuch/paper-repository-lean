import Paper18.Category.DrinfeldRigid
import Paper18.Category.SemisimpleCoendOpposite
import Mathlib.CategoryTheory.Limits.Shapes.End
import Mathlib.CategoryTheory.Monoidal.Linear
import Mathlib.CategoryTheory.Linear.FunctorCategory
import Mathlib.CategoryTheory.Preadditive.Opposite
import Mathlib.Data.Complex.Basic

/-!
# The actual central-induction coend diagram

The bifunctor is `H_X(U,V) = (V ⊗ X) ⊗ U*`, contravariant in `U` and
covariant in `V`. Its diagonal coend is the induction object. This file
constructs the bifunctor and proves its actual linearity properties.
-/
noncomputable section
universe v u
namespace Paper18.Category.Drinfeld
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits Opposite
attribute [local instance 2000] RightRigidCategory.rightDual

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]

/-- The actual right dual as a contravariant functor. -/
def rightDualFunctor : Cᵒᵖ ⥤ C where
  obj U := U.unopᘁ
  map f := rightAdjointMate f.unop
  map_id U := by simp
  map_comp f g := by simp [comp_rightAdjointMate]

/-- The actual bifunctor defining central induction. -/
def inductionDiagram (X : C) : Cᵒᵖ ⥤ C ⥤ C where
  obj U :=
    { obj := fun V => (V ⊗ X) ⊗ U.unopᘁ
      map := fun f => (f ▷ X) ▷ U.unopᘁ
      map_id V := by simp
      map_comp f g := by simp }
  map {U V} f :=
    { app := fun W => (W ⊗ X) ◁ rightAdjointMate f.unop
      naturality {V W} g := by
        dsimp
        exact (whisker_exchange (g ▷ X) (rightAdjointMate f.unop)).symm }
  map_id U := by ext W; simp
  map_comp f g := by ext W; simp [comp_rightAdjointMate]

@[simp] lemma inductionDiagram_obj_obj (X U V : C) :
    ((inductionDiagram X).obj (op U)).obj V = (V ⊗ X) ⊗ Uᘁ := rfl

@[simp] lemma inductionDiagram_obj_map (X U : C) {V W : C} (f : V ⟶ W) :
    ((inductionDiagram X).obj (op U)).map f = (f ▷ X) ▷ Uᘁ := rfl

@[simp] lemma inductionDiagram_map_app (X W : C) {U V : C} (f : U ⟶ V) :
    ((inductionDiagram X).map f.op).app W = (W ⊗ X) ◁ rightAdjointMate f := rfl

section Linear
variable [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]

omit [Linear ℂ C] [MonoidalLinear ℂ C] in
/-- Additivity of the actual dual map follows directly from its cup-cap formula. -/
lemma rightAdjointMate_add {U V : C} (f g : U ⟶ V) :
    rightAdjointMate (f + g) = rightAdjointMate f + rightAdjointMate g := by
  simp [rightAdjointMate, Preadditive.comp_add, Preadditive.add_comp]

/-- The actual contravariant right dual is complex-linear on morphisms. -/
lemma rightAdjointMate_smul {U V : C} (c : ℂ) (f : U ⟶ V) :
    rightAdjointMate (c • f) = c • rightAdjointMate f := by
  simp [rightAdjointMate]

instance rightDualFunctor_additive : (rightDualFunctor (C := C)).Additive where
  map_add := by intros; simp [rightDualFunctor, rightAdjointMate_add]

instance rightDualFunctor_linear : (rightDualFunctor (C := C)).Linear ℂ where
  map_smul f c := by simp [rightDualFunctor, rightAdjointMate_smul]

instance inductionDiagram_obj_additive (X : C) (U : Cᵒᵖ) :
    ((inductionDiagram X).obj U).Additive where
  map_add := by intros; simp [inductionDiagram]

instance inductionDiagram_obj_linear (X : C) (U : Cᵒᵖ) :
    ((inductionDiagram X).obj U).Linear ℂ where
  map_smul f c := by simp [inductionDiagram]

instance inductionDiagram_additive (X : C) : (inductionDiagram X).Additive where
  map_add := by intros; ext W; simp [inductionDiagram, rightAdjointMate_add]

instance inductionDiagram_linear (X : C) : (inductionDiagram X).Linear ℂ where
  map_smul f c := by ext W; simp [inductionDiagram, rightAdjointMate_smul]

/-- Componentwise linearity in the contravariant variable, stated without
requiring any additional convention for scalars on the opposite category. -/
lemma inductionDiagram_map_smul (X W : C) {U V : C} (c : ℂ) (f : U ⟶ V) :
    ((inductionDiagram X).map (c • f).op).app W =
      c • ((inductionDiagram X).map f.op).app W := by
  simp

end Linear

end Paper18.Category.Drinfeld
