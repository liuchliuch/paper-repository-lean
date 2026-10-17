import Paper18.Category.NondegenerateBraidedFunctorUnit
import Mathlib.CategoryTheory.Adjunction.FullyFaithful

/-! # Braided functors out of an actual nondegenerate fusion category

The actual finite semisimple right adjoint exists. Braidedness and the
actual rigid projection formula make its unit object transparent; source
nondegeneracy and actual connectedness make the adjunction unit invertible.
This constructs actual full faithfulness. The target need not be
semisimple or rigid and no pivotal structure is used.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open Functor.LaxMonoidal Functor.OplaxMonoidal
universe v u w v' u'
namespace Paper18.Category.NondegenerateBraidedFunctor
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [MonoidalCategory C] [BraidedCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C] [RightRigidCategory C] [Simple (𝟙_ C)]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  {D : Type u'} [Category.{v'} D] [Preadditive D] [Linear ℂ D]
  [MonoidalCategory D] [BraidedCategory D] [HasFiniteBiproducts D] [HasKernels D]
  [Simple (𝟙_ D)] [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)]
  (F : C ⥤ D) [F.Braided] [F.Additive] [F.Linear ℂ]

/-- The actual projection formula factors every actual adjunction-unit
component through the actual adjoint-unit map. -/
lemma adjunctionUnit_eq (X : C) :
    (DiagonalAlgebra.semisimpleRightAdjunction S F).unit.app X =
      (ρ_ X).inv ≫ (X ◁ adjointUnitMap S F) ≫
        unitProjection F (DiagonalAlgebra.semisimpleRightAdjunction S F) X := by
  let adj := DiagonalAlgebra.semisimpleRightAdjunction S F
  apply (adj.homEquiv X (F.obj X)).symm.injective
  change F.map (adj.unit.app X) ≫ adj.counit.app (F.obj X) =
    F.map ((ρ_ X).inv ≫ (X ◁ adjointUnitMap S F) ≫ unitProjection F adj X) ≫
      adj.counit.app (F.obj X)
  rw [adj.left_triangle_components]
  simp only [F.map_comp, Category.assoc]
  rw [unitProjection_counit, ← Category.assoc (F.map (X ◁ adjointUnitMap S F))]
  erw [← Functor.OplaxMonoidal.δ_natural_right F X (adjointUnitMap S F)]
  simp only [Category.assoc]
  have hu : F.map (adjointUnitMap S F) ≫ adj.counit.app (𝟙_ D) = η F :=
    adjointUnitMap_counit S F
  erw [← MonoidalCategory.whiskerLeft_comp_assoc (F.obj X) (F.map (adjointUnitMap S F))
    (adj.counit.app (𝟙_ D)), hu]
  rw [Functor.OplaxMonoidal.right_unitality_hom]
  rw [← F.map_comp, Iso.inv_hom_id, F.map_id]

/-- Actual source nondegeneracy forces every actual adjunction-unit
component to be an isomorphism. -/
lemma adjunctionUnit_isIso (hC : IsNondegenerate (C := C)) (X : C) :
    IsIso ((DiagonalAlgebra.semisimpleRightAdjunction S F).unit.app X) := by
  letI := adjointUnitMap_isIso S F hC
  rw [adjunctionUnit_eq S F X]
  infer_instance

/-- A genuine braided additive complex-linear strong tensor functor from
an actual nondegenerate fusion category is actually fully faithful.
The target assumptions do not include semisimplicity or rigidity. -/
def fullyFaithful (hC : IsNondegenerate (C := C)) : F.FullyFaithful := by
  let adj := DiagonalAlgebra.semisimpleRightAdjunction S F
  letI (X : C) : IsIso (adj.unit.app X) := adjunctionUnit_isIso S F hC X
  letI : IsIso adj.unit := NatIso.isIso_of_isIso_app adj.unit
  exact adj.fullyFaithfulLOfIsIsoUnit

/-- Actual fullness, derived from the constructed adjunction. -/
def full (hC : IsNondegenerate (C := C)) : F.Full := (fullyFaithful S F hC).full

/-- Actual faithfulness, derived from the constructed adjunction. -/
def faithful (hC : IsNondegenerate (C := C)) : F.Faithful := (fullyFaithful S F hC).faithful

end Paper18.Category.NondegenerateBraidedFunctor
