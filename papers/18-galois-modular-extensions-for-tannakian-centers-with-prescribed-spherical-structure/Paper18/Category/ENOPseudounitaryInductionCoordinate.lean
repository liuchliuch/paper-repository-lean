import Paper18.Category.DrinfeldLoopTraceBasic
import Paper18.Category.ENOPseudounitaryInductionUnit
import Paper18.Category.ENOPseudounitaryInductionProjector

/-! # The actual unit coordinate of the induction coend

The coordinate is the projection to the actual unit-labelled simple
diagonal summand, followed by its actual augmentation cap. Cup classes of
other simple labels have zero coordinate. The resulting actual rank-one
endomorphisms have the Kronecker-delta pivotal trace.
-/

noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped BigOperators
universe v u w
namespace Paper18.Category.Drinfeld
attribute [local instance 2000] RightRigidCategory.rightDual

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)

@[reassoc (attr := simp)]
lemma inductionι_projection_ne (X : C) (i j : ι) (hij : i ≠ j) :
    inductionι S X (S.simpleObject i) ≫ inductionProjection S X j = 0 := by
  simp only [inductionProjection, inductionι_coendIso_assoc, biproduct.ι_π_ne _ hij]

@[reassoc (attr := simp)]
lemma inductionCup_projection_ne (i j : ι) (hij : i ≠ j) :
    inductionCup S (S.simpleObject i) ≫ inductionProjection S (𝟙_ C) j = 0 := by
  simp only [inductionCup, Category.assoc, inductionι_projection_ne S _ _ _ hij, comp_zero]

@[reassoc (attr := simp)]
lemma inductionCup_projection_self (i : ι) :
    inductionCup S (S.simpleObject i) ≫ inductionProjection S (𝟙_ C) i =
      η_ (S.simpleObject i) (S.simpleObject i)ᘁ ≫
        (ρ_ (S.simpleObject i)).inv ▷ (S.simpleObject i)ᘁ := by
  simp only [inductionCup, Category.assoc, inductionι_projection_self, inductionDiagonal, comp_id]

variable [Simple (𝟙_ C)] (J : PivotalStructure C)

/-- The actual unit coordinate, normalized by the actual pivotal unit cap. -/
def inductionUnitCoordinate : inductionUnderlying S (𝟙_ C) ⟶ 𝟙_ C :=
  inductionProjection S (𝟙_ C) S.unitLabel ≫
    inductionAugmentationComponent J (𝟙_ (Center C)) (𝟙 (𝟙_ C))
      (S.simpleObject S.unitLabel)

@[reassoc (attr := simp)]
lemma inductionCup_unitCoordinate_self :
    inductionCup S (S.simpleObject S.unitLabel) ≫ inductionUnitCoordinate S J = 𝟙 (𝟙_ C) := by
  calc
    _ = inductionCup S (S.simpleObject S.unitLabel) ≫
        inductionAugmentation J S (𝟙_ (Center C)) (𝟙 (𝟙_ C)) := by
      simp only [inductionUnitCoordinate, inductionCup, Category.assoc,
        inductionι_projection_self_assoc, inductionι_augmentation, inductionDiagonal, id_comp]
    _ = inductionAdjunctionUnit J S (𝟙_ C) ≫
        inductionAugmentation J S (𝟙_ (Center C)) (𝟙 (𝟙_ C)) := by
      rw [inductionCup_iso S S.unitIso, inductionCup_unit S J]
    _ = _ := inductionAdjunctionUnit_augmentation J S (𝟙_ (Center C)) (𝟙 (𝟙_ C))

@[reassoc (attr := simp)]
lemma inductionCup_unitCoordinate_ne (i : ι) (hi : i ≠ S.unitLabel) :
    inductionCup S (S.simpleObject i) ≫ inductionUnitCoordinate S J = 0 := by
  simp only [inductionUnitCoordinate, ← Category.assoc,
    inductionCup_projection_ne S _ _ hi, zero_comp]

/-- The actual coordinate functional is dual to the actual unit cup. -/
lemma inductionCup_unitCoordinate (i : ι) :
    inductionCup S (S.simpleObject i) ≫ inductionUnitCoordinate S J =
      if i = S.unitLabel then 𝟙 (𝟙_ C) else 0 := by
  split_ifs with hi
  · subst i
    exact inductionCup_unitCoordinate_self S J
  · exact inductionCup_unitCoordinate_ne S J i hi

/-- The underlying rank-one operator whose central average is used in
the alternative loop-trace computation. -/
def inductionCupRankOne (T : C) :
    inductionUnderlying S (𝟙_ C) ⟶ inductionUnderlying S (𝟙_ C) :=
  inductionUnitCoordinate S J ≫ inductionCup S T

/-- Cyclicity computes the actual pivotal trace of the rank-one
operator directly from cup-coordinate orthogonality. -/
theorem inductionCupRankOne_rightTrace (i : ι) :
    unitScalarEquiv (C := C) (J.rightTrace (inductionCupRankOne S J (S.simpleObject i))) =
      if i = S.unitLabel then 1 else 0 := by
  rw [inductionCupRankOne, J.rightTrace_comp, inductionCup_unitCoordinate]
  split_ifs
  · exact J.rightDim_unit S
  · simp only [J.rightTrace_zero, map_zero]

/-- The constructed FP projection sends the actual adjunction unit to
the FP-weighted sum of the actual cup classes. -/
lemma inductionAdjunctionUnit_fpProjection :
    inductionAdjunctionUnit J S (𝟙_ C) ≫ inductionFPProjection S J =
      (S.fusionBasis.totalFPdim : ℂ)⁻¹ •
        ∑ i, (S.fusionBasis.fpdim i : ℂ) • inductionCup S (S.simpleObject i) := by
  simp only [inductionFPProjection, PivotalStructure.fpProjection,
    Linear.comp_smul, Preadditive.comp_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  exact inductionLoop_under_adjunction S J (S.simpleObject i)

/-- The unit coordinate of this actual FP vector is the inverse total
FP dimension, so the constructed projection cannot vanish. -/
lemma inductionFPProjection_unitCoordinate :
    (inductionAdjunctionUnit J S (𝟙_ C) ≫ inductionFPProjection S J) ≫
        inductionUnitCoordinate S J =
      (S.fusionBasis.totalFPdim : ℂ)⁻¹ • 𝟙 (𝟙_ C) := by
  rw [inductionAdjunctionUnit_fpProjection]
  simp only [Linear.smul_comp, Preadditive.sum_comp, inductionCup_unitCoordinate]
  have hunit : S.fusionBasis.fpdim S.unitLabel = 1 := S.fusionBasis.fpdim_one
  simp [hunit]

/-- This actual idempotent is nonzero, independently of the unresolved
nonunit-loop trace calculation. -/
theorem inductionFPProjection_ne_zero : inductionFPProjection S J ≠ 0 := by
  intro he
  have h := inductionFPProjection_unitCoordinate S J
  rw [he, comp_zero, zero_comp] at h
  have hz : (S.fusionBasis.totalFPdim : ℂ)⁻¹ = 0 := by
    apply smul_left_injective ℂ (CategoryTheory.id_nonzero (𝟙_ C))
    simpa only [zero_smul] using h.symm
  exact inv_ne_zero (Complex.ofReal_ne_zero.mpr
    (ne_of_gt S.fusionBasis.totalFPdim_pos)) hz

end Paper18.Category.Drinfeld
