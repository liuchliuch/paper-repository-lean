import Paper18.Category.DrinfeldSemisimpleResolution

/-! # Actual resolutions consumed by the central averaging slide -/
noncomputable section
universe v u w w'
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

omit [Linear ℂ C] [MonoidalCategory C] [RightRigidCategory C] [MonoidalPreadditive C]
  [MonoidalLinear ℂ C] [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)] in
/-- The finite biproduct composition formula for an arbitrary index universe. -/
lemma biproduct_lift_desc_universe {κ : Type w'} [Fintype κ] (A : κ → C)
    [HasBiproduct A] {X Y : C} (p : ∀ a, X ⟶ A a) (u : ∀ a, A a ⟶ Y) :
    biproduct.lift p ≫ biproduct.desc u = ∑ a, p a ≫ u a := by
  have hd : biproduct.desc u = ∑ a, biproduct.π A a ≫ u a := by
    apply biproduct.hom_ext'
    intro a
    simp only [biproduct.ι_desc, Preadditive.comp_sum, biproduct.ι_π_assoc,
      dite_comp, zero_comp, Finset.sum_dite_eq, Finset.mem_univ, if_true,
      eqToHom_refl, id_comp]
  rw [hd, Preadditive.comp_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [← assoc, biproduct.lift_π]

/-- Any actual finite resolution of the identity gives the corresponding
actual resolution of the universal dinatural inclusion. -/
lemma inductionι_of_resolution (X Y : C) {κ : Type w'} [Fintype κ]
    (A : κ → C) (u : ∀ a, A a ⟶ Y) (p : ∀ a, Y ⟶ A a)
    (h : ∑ a, p a ≫ u a = 𝟙 Y) :
    inductionι S X Y = ∑ a,
      (((p a ▷ X) ▷ dual C Y) ≫ (A a ⊗ X) ◁ dualMap C (u a) ≫ inductionι S X (A a)) := by
  symm
  calc
    _ = ∑ a, (((p a ≫ u a) ▷ X) ▷ dual C Y) ≫ inductionι S X Y := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [inductionι_dinatural, ← comp_whiskerRight_assoc, ← comp_whiskerRight]
    _ = ((((∑ a, p a ≫ u a) ▷ X) ▷ dual C Y)) ≫ inductionι S X Y := by
      simp only [sum_whiskerRight, Preadditive.sum_comp]
    _ = _ := by rw [h]; simp only [id_whiskerRight, id_comp]

variable [Simple (𝟙_ C)] (J : PivotalStructure C)

lemma averagingReciprocalResolution (U : C) (i : ι) :
    (∑ a : averagingReciprocalIndex S U i,
      (J.leftDim (S.simpleObject a.1) / J.leftDim (S.simpleObject i)) •
        (averagingReciprocalProjection S U i a.1 a.2 ≫
          averagingReciprocalInclusion S J U i a.1 a.2)) =
      𝟙 (dual C U ⊗ S.simpleObject i) := by
  have h := averagingReciprocalFrom_to S J U i
  dsimp only [averagingReciprocalFrom, averagingReciprocalTo] at h
  rw [biproduct_lift_desc_universe] at h
  simpa only [Linear.smul_comp] using h

/-- The weighted reciprocal identity resolves a tensor-dual coend component
using precisely the dual-dimension factors needed by averaging. -/
lemma inductionι_reciprocal_resolution (X U : C) (i : ι) :
    J.leftDim (S.simpleObject i) • inductionι S X (dual C U ⊗ S.simpleObject i) =
      ∑ a : averagingReciprocalIndex S U i, J.leftDim (S.simpleObject a.1) •
        ((((averagingReciprocalProjection S U i a.1 a.2) ▷ X) ▷
          dual C (dual C U ⊗ S.simpleObject i)) ≫
          (S.simpleObject a.1 ⊗ X) ◁ dualMap C
            (averagingReciprocalInclusion S J U i a.1 a.2) ≫
          inductionι S X (S.simpleObject a.1)) := by
  rw [inductionι_of_resolution S X (dual C U ⊗ S.simpleObject i)
    (fun a : averagingReciprocalIndex S U i => S.simpleObject a.1)
    (fun a => averagingReciprocalInclusion S J U i a.1 a.2)
    (fun a => (J.leftDim (S.simpleObject a.1) / J.leftDim (S.simpleObject i)) •
      averagingReciprocalProjection S U i a.1 a.2)]
  · rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    simp only [MonoidalLinear.smul_whiskerRight, Linear.smul_comp, smul_smul]
    congr 1
    field_simp [simple_leftDim_ne_zero S J (S.simpleObject i)]
  · simpa only [Linear.smul_comp] using averagingReciprocalResolution S J U i

omit [Linear ℂ C] [RightRigidCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [Simple (𝟙_ C)] [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)] in
/-- Grouping all actual summands of `U ⊗ Sj` by their simple label does
not change the actual identity resolution. -/
lemma averagingOriginalResolution (U : C) (j : ι) :
    (∑ i : ι, ∑ a : averagingSlots S U i j,
      averagingOriginalProjection S U i j a ≫ averagingOriginalInclusion S U i j a) =
      𝟙 (U ⊗ S.simpleObject j) := by
  calc
    _ = ∑ i : ι, ∑ a : averagingSlots S U i j,
        S.coendProjection (U ⊗ S.simpleObject j) a.1 ≫
          S.coendInclusion (U ⊗ S.simpleObject j) a.1 := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro a ha
      simp only [averagingOriginalProjection, averagingOriginalInclusion, assoc,
        Iso.hom_inv_id_assoc]
    _ = ∑ a : Fin (S.length (U ⊗ S.simpleObject j)),
        S.coendProjection (U ⊗ S.simpleObject j) a ≫
          S.coendInclusion (U ⊗ S.simpleObject j) a := by
      simpa only [Fintype.sum_sigma, Equiv.sigmaFiberEquiv, Equiv.coe_fn_mk] using
        (Equiv.sigmaFiberEquiv (S.label (U ⊗ S.simpleObject j))).sum_comp
          (fun a => S.coendProjection (U ⊗ S.simpleObject j) a ≫
            S.coendInclusion (U ⊗ S.simpleObject j) a)
    _ = _ := S.coendResolution _

end Paper18.Category.Drinfeld
