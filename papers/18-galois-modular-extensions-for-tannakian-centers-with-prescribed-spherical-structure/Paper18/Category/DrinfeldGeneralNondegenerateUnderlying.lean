import Paper18.Category.DrinfeldGeneralNondegenerateBasic

/-! # Transparent central objects have only unit constituents underneath -/
noncomputable section
open Classical
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory CategoryTheory.Limits
universe v u w
namespace Paper18.Category.Drinfeld
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C] [Simple (𝟙_ C)]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
include S

lemma inductionUnitTest_simple_eq_zero (J : PivotalStructure C) (i : ι)
    (hi : i ≠ S.unitLabel) :
    (inductionUnitTest S J).app (S.simpleObject i) = 0 := by
  have hdi : S.dualLabel i ≠ S.unitLabel := by
    intro h
    apply hi
    calc
      i = S.dualLabel (S.dualLabel i) := (S.dualLabel_involutive i).symm
      _ = S.dualLabel S.unitLabel := congrArg S.dualLabel h
      _ = S.unitLabel := S.dualLabel_unit
  let e : dual C (S.simpleObject i) ⊗ S.simpleObject S.unitLabel ≅
      S.simpleObject (S.dualLabel i) :=
    (Iso.refl _ ⊗ᵢ S.unitIso) ≪≫ ρ_ _ ≪≫ (S.dualIso i).symm
  have hv (f : 𝟙_ C ⟶ dual C (S.simpleObject i) ⊗ S.simpleObject S.unitLabel) : f = 0 := by
    apply (cancel_mono e.hom).mp
    simpa only [zero_comp] using simple_nonunit_from_unit_eq_zero S _ hdi (f ≫ e.hom)
  have hz : inductionBraidingTail S (𝟙_ C) (S.simpleObject i) (S.simpleObject S.unitLabel) ≫
      inductionProjection S (𝟙_ C) S.unitLabel = 0 := by
    rw [← inductionBraidingComparison_ι, assoc,
      inductionι_projection_unit_zero S (𝟙_ C) _ hv, comp_zero]
  dsimp only [inductionUnitTest, inductionUnderlyingUnitRetract]
  simp only [comp_whiskerRight, whiskerLeft_comp, assoc,
    inductionObj_halfBraiding_hom, inductionHalfBraidingHom_ι_assoc]
  dsimp only [inductionHalfBraidingComponent]
  simp only [assoc]
  rw [← whiskerLeft_comp_assoc, hz]
  simp only [MonoidalPreadditive.whiskerLeft_zero, comp_zero, zero_comp]

/-- The coend test excludes every actual nonunit ambient simple from a
transparent central object's underlying decomposition. -/
lemma transparent_underlying_unitSum (J : PivotalStructure C)
    (Z : Center C) (hZ : Z ∈ mugerCenter) : IsUnitSum Z.1 := by
  have hf (i : ι) (hi : i ≠ S.unitLabel) (f : S.simpleObject i ⟶ Z.1) : f = 0 := by
    have hn := (inductionUnitTest S J).naturality f
    change f ≫ (inductionUnitTest S J).app Z.1 =
      (inductionUnitTest S J).app (S.simpleObject i) ≫ f at hn
    rw [inductionUnitTest_eq_id_of_transparent S J Z hZ,
      inductionUnitTest_simple_eq_zero S J i hi, comp_id, zero_comp] at hn
    exact hn
  have hl (a : Fin (S.length Z.1)) : S.label Z.1 a = S.unitLabel := by
    by_contra ha
    have hz := hf _ ha (S.coendInclusion Z.1 a)
    have hr : S.coendInclusion Z.1 a ≫ S.coendProjection Z.1 a =
        𝟙 (S.simpleObject (S.label Z.1 a)) := by
      simp only [FiniteSemisimpleSkeleton.coendInclusion,
        FiniteSemisimpleSkeleton.coendProjection, assoc,
        Iso.inv_hom_id_assoc, biproduct.ι_π_self]
    rw [hz, zero_comp] at hr
    exact CategoryTheory.id_nonzero _ hr.symm
  refine ⟨S.length Z.1, ⟨S.decomposition Z.1 ≪≫ biproduct.mapIso (fun a => ?_)⟩⟩
  exact eqToIso (congrArg S.simpleObject (hl a)) ≪≫ S.unitIso

end Paper18.Category.Drinfeld
