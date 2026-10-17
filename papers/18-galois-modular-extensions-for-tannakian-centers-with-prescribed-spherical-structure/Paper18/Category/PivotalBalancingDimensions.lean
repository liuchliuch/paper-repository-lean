import Paper18.Category.PivotalBalancing
import Paper18.Category.PivotalBalancingInvertible
import Paper18.Category.PivotalDimensionFusion

/-!
# Dual twist scalars and actual categorical dimensions

The braided cup-cap closure is invariant under rigid duality directly from
the actual Drinfeld cup/cap equations. This derives the scalar dual-twist law
and the implication from an actual ribbon twist to actual sphericality.
-/
noncomputable section
open Classical
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.BraidedCategory CategoryTheory.Limits
universe v u w
namespace Paper18.Category
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [RightRigidCategory C] [BraidedCategory C]

/-- The actual braided closure is unchanged by the chosen rigid dual. -/
lemma braidedDimension_dual (X : C) : braidedDimension (dual C X) = braidedDimension X := by
  unfold braidedDimension
  rw [← drinfeldIso_coevaluation X]
  simp only [assoc]
  have hn := braiding_naturality_right (dual C X) (drinfeldIso X).hom
  dsimp only [doubleDualFunctor] at hn
  rw [reassoc_of% hn, Iso.inv_hom_id_assoc, drinfeldIso_evaluation]

variable [Preadditive C] [Linear ℂ C] [HasKernels C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalPreadditive C] [MonoidalLinear ℂ C] [Simple (𝟙_ C)]

/-- The scalar of the actual braided closure. -/
def braidedDim (X : C) : ℂ := unitScalarEquiv (C := C) (braidedDimension X)

@[simp] lemma braidedDim_dual (X : C) : braidedDim (dual C X) = braidedDim X :=
  congrArg (unitScalarEquiv (C := C)) (braidedDimension_dual X)

namespace PivotalStructure
variable (J : PivotalStructure C)

lemma rightDim_twistScalar (X : C) [Simple X] :
    J.rightDim X = J.twistScalar X * braidedDim X := by
  simp only [rightDim, J.rightDimension_twistScalar, map_smul, smul_eq_mul, braidedDim]

/-- The scalar dual-twist relation before division: it follows from actual
trace closures, with no numerical dual-twist hypothesis. -/
lemma twistScalar_dim_dual (X : C) [Simple X] [Simple (dual C X)] :
    J.twistScalar (dual C X) * J.rightDim X =
      J.twistScalar X * J.rightDim (dual C X) := by
  rw [J.rightDim_twistScalar X, J.rightDim_twistScalar (dual C X), braidedDim_dual]
  ring

lemma twistScalar_unit : J.twistScalar (𝟙_ C) = 1 := by
  apply smul_left_injective ℂ (CategoryTheory.id_nonzero (𝟙_ C))
  change J.twistScalar (𝟙_ C) • 𝟙 (𝟙_ C) = (1 : ℂ) • 𝟙 (𝟙_ C)
  rw [J.twistScalar_spec, J.twist_unit]
  simp

variable [HasFiniteBiproducts C] {ι : Type w} [Fintype ι]
  (S : FiniteSemisimpleSkeleton C ι)

/-- The paper's scalar dual-twist equation is derived from the actual
duality and actual categorical trace. -/
lemma twistScalar_dualLabel (i : ι) :
    J.twistScalar (S.simpleObject (S.dualLabel i)) =
      J.twistScalar (S.simpleObject i) * ((J.pivotalData S).gamma i)⁻¹ := by
  letI := S.simple_rightDual (S.simpleObject i)
  have hc := J.twistScalar_dim_dual (S.simpleObject i)
  rw [← J.twistScalar_iso (S.dualIso i), ← J.rightDim_iso (S.dualIso i)] at hc
  change _ = _ * (J.rightDim (S.simpleObject i) /
    J.rightDim (S.simpleObject (S.dualLabel i)))⁻¹
  rw [inv_div, ← mul_div_assoc]
  exact (eq_div_iff (J.rightDim_ne_zero S (S.simpleObject i))).mpr hc

/-- Actual pivotal braided categories supply all scalar balancing-data
fields from the actual induced twist; no twist law is an input certificate. -/
def balancingData : Paper18.BalancingData (J.pivotalData S) where
  theta i := J.twistScalar (S.simpleObject i)
  theta_ne_zero i := J.twistScalar_ne_zero (S.simpleObject i)
  theta_one := by
    change J.twistScalar (S.simpleObject S.unitLabel) = 1
    rw [J.twistScalar_iso S.unitIso, J.twistScalar_unit]
  theta_dual := J.twistScalar_dualLabel S

/-- An actual ribbon dual-compatibility equation for the induced twist. -/
def TwistSelfDual : Prop := ∀ X : C,
  (J.twistIso (dual C X)).hom = dualMap C (J.twistIso X).hom

include S in
/-- Actual ribbon compatibility implies actual sphericality on every
endomorphism, by trace duality and the actual simple decompositions. -/
lemma spherical_of_twistSelfDual (h : J.TwistSelfDual) : J.Spherical := by
  apply J.spherical_of_simple_dimensions S
  intro i
  let X := S.simpleObject i
  letI := S.simple_rightDual X
  have hs : J.twistScalar (dual C X) = J.twistScalar X := by
    apply smul_left_injective ℂ (CategoryTheory.id_nonzero (dual C X))
    change J.twistScalar (dual C X) • 𝟙 (dual C X) = J.twistScalar X • 𝟙 (dual C X)
    rw [J.twistScalar_spec, h X, ← J.twistScalar_spec X]
    simp [dualMap, rightAdjointMate]
  have hc := J.twistScalar_dim_dual X
  rw [hs] at hc
  have hd := mul_left_cancel₀ (J.twistScalar_ne_zero X) hc
  rw [← J.rightDim_dual]
  exact hd.symm

end PivotalStructure
end Paper18.Category
