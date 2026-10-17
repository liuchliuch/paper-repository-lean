import Paper18.Category.SeparableModules
import Mathlib.CategoryTheory.Monoidal.Bimod
import Mathlib.CategoryTheory.Monoidal.Rigid.Braided
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Bicategory.End

/-!
# Canonical bimodules over a commutative internal algebra

The braiding turns an actual left module into a bimodule. Commutativity of
the algebra proves the two actions commute. This connects the actual module
category to mathlib's coequalizer tensor product of internal bimodules.
-/
noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open CategoryTheory.BraidedCategory
open scoped MonObj
universe v u
namespace Paper18.Category.RelativeTensor
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  {A : C} [MonObj A]

/-- The actual right action induced by the ambient braiding. -/
def rightAction (M : Mod_ C A) : M.X ⊗ A ⟶ M.X :=
  (β_ M.X A).hom ≫ γ[A,M.X]

@[reassoc]
theorem rightAction_naturality {M N : Mod_ C A} (f : M ⟶ N) :
    rightAction M ≫ f.hom = (f.hom ▷ A) ≫ rightAction N := by
  have hf : γ[A,M.X] ≫ f.hom = (A ◁ f.hom) ≫ γ[A,N.X] :=
    IsMod_Hom.smul_hom (A := A) (f := f.hom)
  unfold rightAction
  rw [Category.assoc, hf, ← braiding_naturality_left_assoc]

@[reassoc (attr := simp)]
theorem rightAction_one (M : Mod_ C A) :
    (M.X ◁ η[A]) ≫ rightAction M = (ρ_ M.X).hom := by
  unfold rightAction
  rw [braiding_naturality_right_assoc, InternalModule.one_smul,
    braiding_tensorUnit_right]
  simp

variable [IsCommMonObj A]

/-- Commutativity of the algebra makes the two actual module actions commute. -/
@[reassoc]
theorem middle_assoc (M : Mod_ C A) :
    γ[A,M.X] ▷ A ≫ rightAction M =
      (α_ A M.X A).hom ≫ (A ◁ rightAction M) ≫ γ[A,M.X] := by
  unfold rightAction
  rw [braiding_naturality_left_assoc]
  change (β_ (A ⊗ M.X) A).hom ≫ (A ◁ γ[A,M.X]) ≫ γ[A,M.X] = _
  rw [braiding_tensor_left_hom]
  simp only [Category.assoc, whiskerLeft_comp]
  rw [← InternalModule.mul_smul, ← comp_whiskerRight_assoc, IsCommMonObj.mul_comm,
    InternalModule.mul_smul]
  simp

/-- The right action is associative, derived from module associativity and
the actual braiding hexagon. -/
@[reassoc]
theorem right_assoc (M : Mod_ C A) :
    (M.X ◁ μ[A]) ≫ rightAction M =
      (α_ M.X A A).inv ≫ rightAction M ▷ A ≫ rightAction M := by
  calc
    _ = (α_ M.X A A).inv ≫ (β_ M.X A).hom ▷ A ≫
        (α_ A M.X A).hom ≫ (A ◁ rightAction M) ≫ γ[A,M.X] := by
      unfold rightAction
      rw [braiding_naturality_right_assoc, InternalModule.mul_smul,
        braiding_tensor_right_hom]
      simp
    _ = _ := by
      rw [← middle_assoc]
      unfold rightAction
      simp only [comp_whiskerRight, Category.assoc]

/-- The actual bimodule associated to an actual left module. -/
def toBimodObj (M : Mod_ C A) : Bimod (Mon.mk A) (Mon.mk A) where
  X := M.X
  actLeft := γ[A,M.X]
  one_actLeft := InternalModule.one_smul M
  left_assoc := InternalModule.mul_smul M
  actRight := rightAction M
  actRight_one := rightAction_one M
  right_assoc := right_assoc M
  middle_assoc := middle_assoc M

/-- Module morphisms become actual bimodule intertwiners. -/
def toBimod : Mod_ C A ⥤ Bimod (Mon.mk A) (Mon.mk A) where
  obj := toBimodObj
  map f :=
    { hom := f.hom
      left_act_hom := IsMod_Hom.smul_hom (A := A) (f := f.hom)
      right_act_hom := rightAction_naturality f }

/-- Every actual bimodule gives an actual left module by retaining its
left action. -/
def fromBimodObj (M : Bimod (Mon.mk A) (Mon.mk A)) : Mod_ C A :=
  letI : ModObj A M.X :=
    { smul := M.actLeft
      one_smul' := M.one_actLeft
      mul_smul' := M.left_assoc }
  ⟨M.X⟩

/-- Forget the right action, retaining actual left-module morphisms. -/
def fromBimod : Bimod (Mon.mk A) (Mon.mk A) ⥤ Mod_ C A where
  obj := fromBimodObj
  map f := Mod_.Hom.mk' f.hom f.left_act_hom

section Rigid
variable [RightRigidCategory C]
attribute [local instance 2000] RightRigidCategory.rightDual LeftRigidCategory.leftDual

/-- Rigid tensor functors preserve all existing colimits by actual tensor
adjunctions. -/
instance tensorLeft_preservesColimits (X : C) :
    PreservesColimitsOfSize.{0,0} (tensorLeft X) :=
  (tensorLeftAdjunction (ᘁX) X).leftAdjoint_preservesColimits

instance tensorRight_preservesColimits (X : C) :
    PreservesColimitsOfSize.{0,0} (tensorRight X) :=
  (tensorRightAdjunction X Xᘁ).leftAdjoint_preservesColimits

variable [HasCoequalizers C]

/-- The actual relative tensor module is obtained from the existing actual
coequalizer tensor of the two canonical bimodules. -/
def tensorObj (M N : Mod_ C A) : Mod_ C A :=
  fromBimodObj ((toBimodObj M).tensorBimod (toBimodObj N))

end Rigid
end Paper18.Category.RelativeTensor
