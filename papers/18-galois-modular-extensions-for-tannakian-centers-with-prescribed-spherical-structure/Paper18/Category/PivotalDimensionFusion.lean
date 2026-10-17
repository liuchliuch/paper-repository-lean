import Paper18.Category.PivotalDimension
import Paper18.Category.FusionCategory
import Paper18.Fusion.Pivotal

/-!
# Pivotal dimension data derived from an actual fusion category

Every field of `Paper18.PivotalData` is proved from the categorical pivotal
structure, Schur scalar extraction, actual biproduct decompositions, and
canonical rigid tensor comparisons. No numerical dimension law is assumed.
-/
noncomputable section
open Classical
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators
universe v u w
namespace Paper18.Category
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [RightRigidCategory C] [Simple (𝟙_ C)]
  {ι : Type w} [Fintype ι]

namespace PivotalStructure
variable (J : PivotalStructure C) (S : FiniteSemisimpleSkeleton C ι)

/-- Additive categorical dimension is the sum over actual simple multiplicities. -/
lemma rightDim_eq_sum_multiplicity (X : C) :
    J.rightDim X = ∑ i, (S.multiplicity X i : ℂ) * J.rightDim (S.simpleObject i) := by
  rw [J.rightDim_iso (S.decomposition X), J.rightDim_biproduct]
  symm
  simp_rw [S.multiplicity_eq_sum, Nat.cast_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  simp

/-- Genuine categorical pivotal structures produce the numerical pivotal
character used by the arithmetic part of the paper. -/
def pivotalData : Paper18.PivotalData S.fusionBasis where
  jdim i := J.rightDim (S.simpleObject i)
  jdim_ne_zero i := J.rightDim_ne_zero S (S.simpleObject i)
  jdim_one := by
    change J.rightDim (S.simpleObject S.unitLabel) = 1
    rw [J.rightDim_iso S.unitIso, J.rightDim_unit S]
  jdim_tensor i j := by
    change J.rightDim (S.simpleObject i) * J.rightDim (S.simpleObject j) =
      ∑ k, (S.fusionCoeff i j k : ℂ) * J.rightDim (S.simpleObject k)
    rw [← J.rightDim_tensor]
    exact J.rightDim_eq_sum_multiplicity S _

@[simp] lemma pivotalData_jdim (i : ι) :
    (J.pivotalData S).jdim i = J.rightDim (S.simpleObject i) := rfl

/-- Actual sphericality implies the dual dimension symmetry used by the
numerical slope formalization. -/
lemma pivotalData_spherical (h : J.Spherical) : (J.pivotalData S).Spherical := by
  apply (J.pivotalData S).spherical_iff_jdim_dual.mpr
  intro i
  change J.rightDim (S.simpleObject i) = J.rightDim (S.simpleObject (S.dualLabel i))
  rw [J.rightDim_iso (S.dualIso i), J.rightDim_dual_of_spherical h]

/-- In a finite semisimple category, equality of left and right simple
 dimensions implies sphericality on every actual endomorphism. -/
lemma spherical_of_simple_dimensions
    (hd : ∀ i, J.leftDim (S.simpleObject i) = J.rightDim (S.simpleObject i)) :
    J.Spherical := by
  intro X f
  let Y := fun a : Fin (S.length X) => S.simpleObject (S.label X a)
  let e := S.decomposition X
  let i := fun a => biproduct.ι Y a ≫ e.inv
  let p := fun a => e.hom ≫ biproduct.π Y a
  have hr : ∑ a, p a ≫ i a = 𝟙 X := by
    dsimp only [i, p]
    simp only [assoc, ← Preadditive.comp_sum]
    simp_rw [← assoc]
    rw [← Preadditive.sum_comp, biproduct.total]
    dsimp only [Y]
    rw [id_comp]
    exact e.hom_inv_id
  apply J.traces_eq_of_resolution Y i p hr
  intro a g
  obtain ⟨c, hc⟩ := CategoryTheory.endomorphism_simple_eq_smul_id ℂ g
  rw [← hc, J.leftTrace_smul, J.rightTrace_smul]
  have hh : J.leftDimension (Y a) = J.rightDimension (Y a) := by
    apply (unitScalarEquiv (C := C)).injective
    exact hd (S.label X a)
  exact congrArg (fun k => c • k) hh

/-- Sphericality of the numerical pivotal character is equivalent to actual
sphericality, because every object has an actual finite simple decomposition. -/
lemma pivotalData_spherical_iff : (J.pivotalData S).Spherical ↔ J.Spherical := by
  constructor
  · intro h
    apply J.spherical_of_simple_dimensions S
    intro i
    have hi := (J.pivotalData S).spherical_iff_jdim_dual.mp h i
    change J.rightDim (S.simpleObject i) =
      J.rightDim (S.simpleObject (S.dualLabel i)) at hi
    rw [J.rightDim_iso (S.dualIso i), J.rightDim_dual] at hi
    exact hi.symm
  · exact J.pivotalData_spherical S

end PivotalStructure
end Paper18.Category
