import Paper18.Category.DrinfeldLoopTraceComponents

/-! # Actual diagonal matrix terms of induction loops -/
noncomputable section
universe v u w
namespace Paper18.Category.Drinfeld
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped BigOperators
open Classical
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)

/-- Dinaturality transports an actual coend inclusion along any isomorphism. -/
lemma inductionι_iso (X : C) {T U : C} (e : T ≅ U) :
    inductionι S X T = ((e.hom ▷ X) ▷ dual C T) ≫
      (U ⊗ X) ◁ dualMap C e.inv ≫ inductionι S X U := by
  symm
  rw [inductionι_dinatural, ← comp_whiskerRight_assoc, ← comp_whiskerRight,
    Iso.hom_inv_id, id_whiskerRight, id_whiskerRight, id_comp]

/-- A matching simple coordinate is the actual isomorphism transport map. -/
lemma inductionι_projection_iso (X : C) {T : C} (i : ι) (e : T ≅ S.simpleObject i) :
    inductionι S X T ≫ inductionProjection S X i =
      ((e.hom ▷ X) ▷ dual C T) ≫ (S.simpleObject i ⊗ X) ◁ dualMap C e.inv := by
  rw [inductionι_iso S X e]
  simp only [assoc, inductionι_projection_self]
  change ((e.hom ▷ X) ▷ dual C T) ≫
    (S.simpleObject i ⊗ X) ◁ dualMap C e.inv ≫ 𝟙 ((S.simpleObject i ⊗ X) ⊗ dual C (S.simpleObject i)) = _
  rw [comp_id]

omit [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)] in
/-- Changing a simple matrix coordinate transports both actual matrix maps. -/
lemma inductionLoopAnnular_matrix_iso (J : PivotalStructure C) (T A B : C)
    (e : B ≅ T) (u : B ⟶ dual C (dual C T) ⊗ A)
    (p : dual C (dual C T) ⊗ A ⟶ B) :
    inductionLoopOpenDiagram J T A ≫
      ((p ▷ (𝟙_ C)) ▷ dual C (dual C (dual C T) ⊗ A)) ≫
      (B ⊗ (𝟙_ C)) ◁ dualMap C u ≫
      ((e.hom ▷ (𝟙_ C)) ▷ dual C B) ≫
      (T ⊗ (𝟙_ C)) ◁ dualMap C e.inv =
        inductionLoopAnnularTerm J T A (e.inv ≫ u) (p ≫ e.hom) := by
  have hd : dualMap C (e.inv ≫ u) = dualMap C u ≫ dualMap C e.inv :=
    comp_rightAdjointMate
  dsimp only [inductionLoopAnnularTerm]
  rw [hd, whiskerLeft_comp]
  rw [whisker_exchange_assoc]
  simp only [comp_whiskerRight, assoc]

/-- An arbitrary actual decomposition expands the diagonal matrix entry. -/
lemma inductionLoop_diagonal_expansion (J : PivotalStructure C) (i : ι) (A : C) :
    inductionι S (𝟙_ C) (S.simpleObject i) ≫ (inductionLoop S J A).f ≫
        inductionProjection S (𝟙_ C) i =
      ∑ a : Fin (S.length (dual C (dual C (S.simpleObject i)) ⊗ A)),
        inductionLoopOpenDiagram J (S.simpleObject i) A ≫
          ((S.coendProjection _ a ▷ (𝟙_ C)) ▷
            dual C (dual C (dual C (S.simpleObject i)) ⊗ A)) ≫
          (S.simpleObject (S.label _ a) ⊗ (𝟙_ C)) ◁ dualMap C (S.coendInclusion _ a) ≫
          inductionι S (𝟙_ C) (S.simpleObject (S.label _ a)) ≫
          inductionProjection S (𝟙_ C) i := by
  rw [← assoc, inductionι_loop_open]
  rw [inductionι_of_resolution S (𝟙_ C) (dual C (dual C (S.simpleObject i)) ⊗ A)
    (fun a => S.simpleObject (S.label _ a))
    (S.coendInclusion _) (S.coendProjection _) (S.coendResolution _)]
  simp only [Preadditive.comp_sum, Preadditive.sum_comp, assoc]

/-- The actual finite coend matrix resolution reduces loop-trace vanishing
to the corresponding pure annular trace calculation. -/
lemma inductionLoop_rightTrace_zero_of_annular (J : PivotalStructure C) (A : C)
    (h : ∀ (i : ι) (u : S.simpleObject i ⟶ dual C (dual C (S.simpleObject i)) ⊗ A)
      (p : dual C (dual C (S.simpleObject i)) ⊗ A ⟶ S.simpleObject i),
      J.rightTrace (inductionLoopAnnularTerm J (S.simpleObject i) A u p) = 0) :
    J.rightTrace (inductionLoop S J A).f = 0 := by
  rw [inductionTrace_diagonal S J (𝟙_ C)]
  apply Finset.sum_eq_zero
  intro i _
  rw [inductionLoop_diagonal_expansion S J i A, J.rightTrace_sum]
  apply Finset.sum_eq_zero
  intro a _
  by_cases ha : S.label (dual C (dual C (S.simpleObject i)) ⊗ A) a = i
  · let e : S.simpleObject (S.label (dual C (dual C (S.simpleObject i)) ⊗ A) a) ≅
        S.simpleObject i := eqToIso (congrArg S.simpleObject ha)
    rw [inductionι_projection_iso S (𝟙_ C) i e]
    rw [inductionLoopAnnular_matrix_iso]
    exact h i _ _
  · have hz : inductionι S (𝟙_ C)
        (S.simpleObject (S.label (dual C (dual C (S.simpleObject i)) ⊗ A) a)) ≫
          inductionProjection S (𝟙_ C) i = 0 := by
      simp only [inductionProjection, inductionι_coendIso_assoc, biproduct.ι_π_ne _ ha]
    simp only [hz, comp_zero, J.rightTrace_zero]

omit [RightRigidCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C] in
/-- The tensor unit has no maps into a distinct simple representative. -/
lemma simple_nonunit_from_unit_eq_zero [Simple (𝟙_ C)] (i : ι)
    (hi : i ≠ S.unitLabel) (f : 𝟙_ C ⟶ S.simpleObject i) : f = 0 := by
  by_contra hf
  letI := CategoryTheory.isIso_of_hom_simple hf
  exact hi (S.iso_injective i S.unitLabel ⟨(asIso f).symm ≪≫ S.unitIso.symm⟩)

omit [RightRigidCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C] in
/-- A distinct simple representative has no maps into the tensor unit. -/
lemma simple_nonunit_to_unit_eq_zero [Simple (𝟙_ C)] (i : ι)
    (hi : i ≠ S.unitLabel) (f : S.simpleObject i ⟶ 𝟙_ C) : f = 0 := by
  by_contra hf
  letI := CategoryTheory.isIso_of_hom_simple hf
  exact hi (S.iso_injective i S.unitLabel ⟨asIso f ≪≫ S.unitIso.symm⟩)

/-- If an actual object has no unit constituent, its universal coend
inclusion has zero component at the actual unit-labelled diagonal. -/
lemma inductionι_projection_unit_zero [Simple (𝟙_ C)] (X V : C)
    (hV : ∀ f : 𝟙_ C ⟶ V, f = 0) :
    inductionι S X V ≫ inductionProjection S X S.unitLabel = 0 := by
  rw [inductionι_of_resolution S X V
    (fun a => S.simpleObject (S.label V a))
    (S.coendInclusion V) (S.coendProjection V) (S.coendResolution V)]
  simp only [Preadditive.sum_comp, assoc]
  apply Finset.sum_eq_zero
  intro a _
  have ha : S.label V a ≠ S.unitLabel := by
    intro he
    let e : 𝟙_ C ≅ S.simpleObject (S.label V a) :=
      S.unitIso.symm ≪≫ (eqToIso (congrArg S.simpleObject he)).symm
    have hu : S.coendInclusion V a = 0 := by
      apply (cancel_epi e.hom).mp
      simpa only [comp_zero] using hV (e.hom ≫ S.coendInclusion V a)
    have hsplit : S.coendInclusion V a ≫ S.coendProjection V a =
        𝟙 (S.simpleObject (S.label V a)) := by
      simp only [FiniteSemisimpleSkeleton.coendInclusion,
        FiniteSemisimpleSkeleton.coendProjection, assoc,
        Iso.inv_hom_id_assoc, biproduct.ι_π_self]
    rw [hu, zero_comp] at hsplit
    exact CategoryTheory.id_nonzero _ hsplit.symm
  have hz : inductionι S X (S.simpleObject (S.label V a)) ≫
      inductionProjection S X S.unitLabel = 0 := by
    simp only [inductionProjection, inductionι_coendIso_assoc, biproduct.ι_π_ne _ ha]
  simp only [hz, comp_zero]

end Paper18.Category.Drinfeld
