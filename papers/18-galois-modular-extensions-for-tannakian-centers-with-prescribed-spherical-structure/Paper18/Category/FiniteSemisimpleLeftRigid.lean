import Paper18.Category.DiagonalAlgebraAdjoints
import Mathlib.CategoryTheory.Limits.Opposites
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.CategoryTheory.Preadditive.Opposite

/-! # Left duals derived from finite semisimplicity and right duals -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
universe v u w
namespace Paper18.Category.FiniteSemisimpleLeftRigid
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]

/-- Actual contravariant right duality, as a functor. -/
def rightDualFunctor : Cᵒᵖ ⥤ C where
  obj X := X.unopᘁ
  map f := rightAdjointMate f.unop
  map_id X := by change rightAdjointMate (𝟙 X.unop) = 𝟙 _; simp
  map_comp f g := by
    change rightAdjointMate (g.unop ≫ f.unop) = _
    exact comp_rightAdjointMate

instance rightDualFunctorAdditive : (rightDualFunctor (C := C)).Additive where
  map_add {X Y} f g := by
    change rightAdjointMate (f.unop + g.unop) =
      rightAdjointMate f.unop + rightAdjointMate g.unop
    simpa only [DiagonalAlgebra.rightDualHomLinearEquiv_apply] using
      (rightDualHomLinearEquiv Y.unop X.unop).map_add f.unop g.unop

/-- The actual linear mate bijection gives actual full faithfulness. -/
def rightDualFunctorFullyFaithful : (rightDualFunctor (C := C)).FullyFaithful where
  preimage {X Y} f := ((rightDualHomLinearEquiv Y.unop X.unop).symm f).op
  map_preimage {X Y} f := by
    change rightAdjointMate ((rightDualHomLinearEquiv Y.unop X.unop).symm f) = f
    simpa only [DiagonalAlgebra.rightDualHomLinearEquiv_apply] using
      (rightDualHomLinearEquiv Y.unop X.unop).apply_symm_apply f
  preimage_map {X Y} f := by
    apply Quiver.Hom.unop_inj
    change (rightDualHomLinearEquiv Y.unop X.unop).symm (rightAdjointMate f.unop) = f.unop
    simpa only [DiagonalAlgebra.rightDualHomLinearEquiv_apply] using
      (rightDualHomLinearEquiv Y.unop X.unop).symm_apply_apply f.unop

variable [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ C)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)

local instance oppositeHasFiniteBiproducts : HasFiniteBiproducts Cᵒᵖ :=
  HasFiniteBiproducts.of_hasFiniteCoproducts

/-- Finite actual simple classes and their proved involutive dual labels
give actual preimages of all objects under right duality. -/
def rightDualFunctorEssSurj : (rightDualFunctor (C := C)).EssSurj where
  mem_essImage X := by
    let f : Fin (S.length X) → Cᵒᵖ := fun a =>
      Opposite.op (S.simpleObject (S.dualLabel (S.label X a)))
    refine ⟨⨁ f, ⟨(rightDualFunctor (C := C)).mapBiproduct f ≪≫
      biproduct.mapIso (fun a => ?_) ≪≫ (S.decomposition X).symm⟩⟩
    exact (S.dualIso (S.dualLabel (S.label X a))).symm ≪≫
      eqToIso (congrArg S.simpleObject (S.dualLabel_involutive (S.label X a)))

/-- Every actual object has an actual left dual, chosen as a proved
preimage under right duality and equipped with its transported pairing. -/
def hasLeftDual (X : C) : HasLeftDual X := by
  let Y := Classical.choose ((rightDualFunctorEssSurj S).mem_essImage X)
  let e : (rightDualFunctor (C := C)).obj Y ≅ X :=
    Classical.choice (Classical.choose_spec ((rightDualFunctorEssSurj S).mem_essImage X))
  letI : ExactPairing Y.unop ((rightDualFunctor (C := C)).obj Y) := by
    change ExactPairing Y.unop (Y.unopᘁ)
    infer_instance
  exact { leftDual := Y.unop, exact := exactPairingCongrRight e.symm }

/-- Finite semisimplicity, a simple unit and actual right duals suffice
for actual left rigidity. No braiding or pivotal structure is supplied. -/
def leftRigidCategory : LeftRigidCategory C where
  leftDual X := hasLeftDual S X

end Paper18.Category.FiniteSemisimpleLeftRigid
