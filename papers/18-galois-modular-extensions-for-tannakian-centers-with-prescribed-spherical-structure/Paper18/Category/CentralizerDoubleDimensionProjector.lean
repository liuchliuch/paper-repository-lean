import Paper18.Category.CentralizerDoubleDimensionSlide

/-! # Restricted actual Hopf averaging selects the categorical centralizer -/
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
  [RightRigidCategory C] [Simple (𝟙_ C)] [BraidedCategory C]
  {ι : Type w} [Fintype ι]
namespace PivotalStructure
open Drinfeld
variable (J : PivotalStructure C) (S : FiniteSemisimpleSkeleton C ι)

/-- The unnormalized actual averaging operator restricted to a full property. -/
def restrictedHopfProjector (P : ObjectProperty C) (X : C) : X ⟶ X :=
  restrictedInductionSection S J P ((positive C).obj X) ≫
    (inductionCounit S J ((negative C).obj X)).f

lemma restrictedHopfProjector_loops (P : ObjectProperty C) (X : C) :
    J.restrictedHopfProjector S P X = ∑ i, if P (S.simpleObject i) then
      J.rightDim (S.simpleObject (S.dualLabel i)) • J.hopfLoop X (S.simpleObject i) else 0 := by
  have hc (i : ι) : inductionι S X (S.simpleObject i) ≫
      (inductionCounit S J ((negative C).obj X)).f =
        inductionAugmentationCap J ((negative C).obj X) (S.simpleObject i) := by
    rw [inductionCounit, inductionAugmentationHom_f, inductionι_augmentation]
    change ((S.simpleObject i ◁ 𝟙 X) ▷ dual C (S.simpleObject i)) ≫
      inductionAugmentationCap J ((negative C).obj X) (S.simpleObject i) = _
    rw [whiskerLeft_id, id_whiskerRight]
    exact id_comp _
  simp only [restrictedHopfProjector, restrictedInductionSection, supportedInductionSection,
    Preadditive.sum_comp, Linear.smul_comp, assoc]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : P (S.simpleObject i)
  · simp only [if_pos hi, one_smul]
    rw [← J.rightDim_dual, ← J.rightDim_iso (S.dualIso i)]
    congr 1
    change inductionSectionComponent ((positive C).obj X) (S.simpleObject i) ≫
      inductionι S X (S.simpleObject i) ≫ (inductionCounit S J ((negative C).obj X)).f = _
    rw [hc]
    exact J.averagingHopfLoop_eq_rightPartialTrace X (S.simpleObject i)
  · simp only [if_neg hi, zero_smul]

/-- The actual restricted averaging operator intertwines the positive and
negative half-braidings against every object of the chosen fusion subcategory. -/
lemma restrictedHopfProjector_comm (P : ObjectProperty C)
    [IsAdditiveFullProperty P] [P.IsMonoidal] (X U : C) (hU : P U) :
    (J.restrictedHopfProjector S P X ▷ U) ≫ (((negative C).obj X).2.β U).hom =
      (((positive C).obj X).2.β U).hom ≫ U ◁ J.restrictedHopfProjector S P X := by
  have hc := (inductionCounit S J ((negative C).obj X)).comm U
  change ((inductionCounit S J ((negative C).obj X)).f ▷ U) ≫
      (((negative C).obj X).2.β U).hom =
    inductionHalfBraidingHom S J X U ≫ U ◁ (inductionCounit S J ((negative C).obj X)).f at hc
  dsimp only [restrictedHopfProjector]
  have hs := restrictedInductionSection_central S J P ((positive C).obj X) U hU
  change (restrictedInductionSection S J P ((positive C).obj X) ▷ U) ≫
      inductionHalfBraidingHom S J X U =
    (((positive C).obj X).2.β U).hom ≫ U ◁ restrictedInductionSection S J P ((positive C).obj X) at hs
  rw [comp_whiskerRight, assoc, hc, ← assoc, hs, assoc, ← whiskerLeft_comp]

/-- Closing an identity on the right tensor factor is its actual dimension. -/
lemma rightPartialTrace_id_eq_smul (A T : C) :
    J.rightPartialTrace T (𝟙 (A ⊗ T)) = J.rightDim T • 𝟙 A := by
  have h : J.rightPartialTrace T (𝟙 (A ⊗ T)) =
      (ρ_ A).inv ≫ A ◁ J.rightDimension T ≫ (ρ_ A).hom := by
    dsimp only [rightPartialTrace, rightClosure, rightDimension, rightTrace]
    simp only [id_whiskerRight, id_comp]
    monoidal
  rw [h, ← unitScalarEquiv_spec (J.rightDimension T)]
  simp only [MonoidalLinear.whiskerLeft_smul, whiskerLeft_id, Linear.comp_smul,
    Linear.smul_comp, id_comp, Iso.inv_hom_id]
  rfl

lemma hopfLoop_eq_dim_smul_of_centralizes (X T : C) (h : Centralizes X T) :
    J.hopfLoop X T = J.rightDim T • 𝟙 X := by
  unfold hopfLoop
  rw [h, J.rightPartialTrace_id_eq_smul]

lemma restrictedHopfProjector_eq_dim_smul (P : ObjectProperty C) (X : C)
    (hX : X ∈ centralizer (P : Set C)) :
    J.restrictedHopfProjector S P X = S.supportGlobalDimension J P • 𝟙 X := by
  rw [J.restrictedHopfProjector_loops, S.supportGlobalDimension_eq]
  rw [Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : P (S.simpleObject i)
  · rw [if_pos hi, if_pos hi, J.hopfLoop_eq_dim_smul_of_centralizes _ _ (hX _ hi), smul_smul]
  · simp only [if_neg hi, zero_smul]

lemma restrictedHopfProjector_simple_zero (P : ObjectProperty C)
    [IsAdditiveFullProperty P] [P.IsMonoidal] (X : C) [Simple X]
    (hX : X ∉ centralizer (P : Set C)) : J.restrictedHopfProjector S P X = 0 := by
  obtain ⟨c, hc⟩ := CategoryTheory.endomorphism_simple_eq_smul_id ℂ
    (J.restrictedHopfProjector S P X)
  have hz : c = 0 := by
    by_contra hcn
    apply hX
    intro U hU
    have hh := J.restrictedHopfProjector_comm S P X U hU
    rw [← hc] at hh
    simp only [MonoidalLinear.smul_whiskerRight, id_whiskerRight,
      Linear.smul_comp, id_comp, MonoidalLinear.whiskerLeft_smul,
      whiskerLeft_id, Linear.comp_smul, comp_id] at hh
    have he := (smul_right_injective _ hcn) hh
    change (β_ X U).hom ≫ (β_ U X).hom = 𝟙 _
    change (β_ U X).inv = (β_ X U).hom ≫ U ◁ 𝟙 X at he
    rw [whiskerLeft_id, comp_id] at he
    rw [← he, Iso.inv_hom_id]
  rw [← hc, hz, zero_smul]

/-- On actual simples the restricted Hopf average is exactly the centralizer
support projector multiplied by the actual subcategory global dimension. -/
lemma restrictedHopfProjector_simple (P : ObjectProperty C)
    [IsAdditiveFullProperty P] [P.IsMonoidal] (i : ι) :
    J.restrictedHopfProjector S P (S.simpleObject i) =
      S.supportGlobalDimension J P •
        (S.centralizerProjector (P : Set C)).app (S.simpleObject i) := by
  rw [S.supportProjector_simple]
  change J.restrictedHopfProjector S P (S.simpleObject i) = S.supportGlobalDimension J P •
    (if S.simpleObject i ∈ centralizer (P : Set C) then 𝟙 (S.simpleObject i) else 0)
  by_cases hi : S.simpleObject i ∈ centralizer (P : Set C)
  · rw [if_pos hi]
    exact J.restrictedHopfProjector_eq_dim_smul S P _ hi
  · rw [if_neg hi, smul_zero]
    exact J.restrictedHopfProjector_simple_zero S P _ hi

end PivotalStructure
end Paper18.Category
