import Paper18.Category.HopfLinkGauss
import Paper18.Category.DrinfeldSemisimpleCentrality
import Paper18.Category.FactorizationFullyFaithfulCross

/-! # The actual positive-to-negative Hopf averaging projector -/
noncomputable section
open Classical
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped BigOperators
universe v u w
namespace Paper18.Category
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [RightRigidCategory C] [Simple (𝟙_ C)] [BraidedCategory C]
  {ι : Type w} [Fintype ι]

namespace PivotalStructure
open Drinfeld
variable (J : PivotalStructure C) (S : FiniteSemisimpleSkeleton C ι)

/-- Average the underlying identity from the actual positive center image to
the actual negative center image. Its centrality is already proved categorically. -/
def hopfProjector (X : C) : X ⟶ X :=
  (centerAverage S J (Z := (positive C).obj X) (W := (negative C).obj X) (𝟙 X)).f

lemma hopfProjector_eq (X : C) : J.hopfProjector S X =
    inductionNormalizedSection S J ((positive C).obj X) ≫
      (inductionCounit S J ((negative C).obj X)).f := by
  change centerAverageUnderlying S J (Z := (positive C).obj X)
    (W := (negative C).obj X) (𝟙 X) = _
  simp only [centerAverageUnderlying]
  have hc : inductionUnderlyingMap S (𝟙 X) ≫
      (inductionCounit S J ((negative C).obj X)).f =
      (inductionCounit S J ((negative C).obj X)).f := by
    rw [inductionUnderlyingMap_id S X]
    exact id_comp _
  exact congrArg (fun f => inductionNormalizedSection S J ((positive C).obj X) ≫ f) hc

/-- The actual averaged identity is natural in every actual morphism. -/
lemma hopfProjector_naturality {X Y : C} (f : X ⟶ Y) :
    f ≫ J.hopfProjector S Y = J.hopfProjector S X ≫ f := by
  rw [J.hopfProjector_eq, J.hopfProjector_eq]
  have hs := inductionNormalizedSection_naturality S J ((positive C).map f)
  change f ≫ inductionNormalizedSection S J ((positive C).obj Y) =
    inductionNormalizedSection S J ((positive C).obj X) ≫ inductionUnderlyingMap S f at hs
  have hc := congrArg Center.Hom.f
    ((inductionAdjunction S J).counit.naturality ((negative C).map f))
  change inductionUnderlyingMap S f ≫ (inductionCounit S J ((negative C).obj Y)).f =
    (inductionCounit S J ((negative C).obj X)).f ≫ f at hc
  rw [← assoc, hs, assoc, hc, ← assoc]

/-- The natural averaged endomorphism vanishes on every nonunit simple in
an actual Müger nondegenerate category. -/
lemma hopfProjector_simple_eq_zero (hC : IsNondegenerate (C := C)) (i : ι)
    (hi : i ≠ S.unitLabel) : J.hopfProjector S (S.simpleObject i) = 0 := by
  have hz := positive_negative_simple_hom_eq_zero S hC i i (Or.inl hi)
    (centerAverage S J (Z := (positive C).obj (S.simpleObject i))
      (W := (negative C).obj (S.simpleObject i)) (𝟙 (S.simpleObject i)))
  exact congrArg Center.Hom.f hz

/-- Every actual transparent object has identity Hopf projector. -/
lemma hopfProjector_eq_id_of_transparent (X : C) (hX : X ∈ mugerCenter) :
    J.hopfProjector S X = 𝟙 X := by
  obtain ⟨e, he⟩ := (positive_iso_negative_iff (C := C) X).mpr hX
  change (centerAverage S J (Z := (positive C).obj X) (W := (negative C).obj X) (𝟙 X)).f = _
  rw [← he, centerAverage_central_map]

lemma hopfProjector_unit : J.hopfProjector S (𝟙_ C) = 𝟙 (𝟙_ C) := by
  apply J.hopfProjector_eq_id_of_transparent S
  intro X _
  exact centralizes_unit_left X

lemma hopfProjector_unitLabel : J.hopfProjector S (S.simpleObject S.unitLabel) =
    𝟙 (S.simpleObject S.unitLabel) := by
  have hn := J.hopfProjector_naturality S S.unitIso.hom
  rw [J.hopfProjector_unit] at hn
  apply (cancel_mono S.unitIso.hom).1
  simpa only [id_comp, comp_id] using hn.symm

lemma hopfProjector_simple (hC : IsNondegenerate (C := C)) (i : ι) :
    J.hopfProjector S (S.simpleObject i) =
      if i = S.unitLabel then 𝟙 (S.simpleObject i) else 0 := by
  split_ifs with hi
  · subst i; exact J.hopfProjector_unitLabel S
  · exact J.hopfProjector_simple_eq_zero S hC i hi

/-- The actual trace of the averaged identity counts actual unit summands.
The count follows from actual decompositions and categorical naturality. -/
lemma rightTraceScalar_hopfProjector (hC : IsNondegenerate (C := C)) (X : C) :
    unitScalarEquiv (C := C) (J.rightTrace (J.hopfProjector S X)) =
      (S.multiplicity X S.unitLabel : ℂ) := by
  let Y := fun a : Fin (S.length X) => S.simpleObject (S.label X a)
  let e := S.decomposition X
  let ii := fun a => biproduct.ι Y a ≫ e.inv
  let pp := fun a => e.hom ≫ biproduct.π Y a
  have hr : ∑ a, pp a ≫ ii a = 𝟙 X := by
    dsimp only [ii, pp]
    simp only [assoc, ← Preadditive.comp_sum]
    simp_rw [← assoc]
    rw [← Preadditive.sum_comp, biproduct.total, id_comp]
    exact e.hom_inv_id
  have hpi (a : Fin (S.length X)) : ii a ≫ pp a = 𝟙 (Y a) := by simp [ii, pp, assoc]
  rw [J.rightTrace_of_resolution Y ii pp hr, map_sum, S.multiplicity_eq_sum]
  simp only [Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [reassoc_of% (J.hopfProjector_naturality S (ii a)), hpi, comp_id,
    J.hopfProjector_simple S hC]
  by_cases ha : S.label X a = S.unitLabel
  · simp only [if_pos ha, if_pos ha.symm, Nat.cast_one]
    change J.rightDim (S.simpleObject (S.label X a)) = 1
    rw [ha, J.rightDim_iso S.unitIso, J.rightDim_unit S]
  · simp [ha, Ne.symm ha]

end PivotalStructure
end Paper18.Category
