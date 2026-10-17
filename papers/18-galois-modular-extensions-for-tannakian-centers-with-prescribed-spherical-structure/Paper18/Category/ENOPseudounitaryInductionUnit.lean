import Paper18.Category.ENOPseudounitaryCenterLoops
import Paper18.Category.ENOPseudounitaryBounds

/-! # The unit loop and the actual dimension of central induction

These are the unit case of the induction-loop trace formula. The unit loop
is the identity by the actual adjunction, and the categorical dimension of
the induction object is the global dimension by its actual finite diagonal
decomposition.
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
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι) (J : PivotalStructure C)

lemma inductionCup_unit :
    inductionCup S (𝟙_ C) = inductionAdjunctionUnit J S (𝟙_ C) := by
  have hc : η_ (𝟙_ C) (𝟙_ C)ᘁ ≫ (𝟙_ C) ◁ (dualUnitIso (C := C)).hom =
      (ρ_ (𝟙_ C)).inv :=
    rightDualIso_coevaluation _ CategoryTheory.exactPairingUnit
  have hc' : η_ (𝟙_ C) (𝟙_ C)ᘁ =
      (ρ_ (𝟙_ C)).inv ≫ (𝟙_ C) ◁ (dualUnitIso (C := C)).inv := by
    rw [← hc]
    simp only [Category.assoc, ← whiskerLeft_comp, Iso.hom_inv_id,
      whiskerLeft_id, comp_id]
  dsimp only [inductionCup, inductionAdjunctionUnit, inductionAdjunctionUnitComponent]
  rw [pivotalUnitDualIso_eq_dualUnitIso, hc']
  monoidal

/-- The actual loop labelled by the tensor unit is the identity of the
actual central induction object. -/
@[simp] lemma inductionLoop_unit :
    inductionLoop S J (𝟙_ C) = 𝟙 (inductionObj S J (𝟙_ C)) := by
  apply (inductionHomLinearEquiv S J (𝟙_ C)
    (inductionObj S J (𝟙_ C))).injective
  rw [inductionLoop_under_adjunction, inductionCup_unit S J]
  change inductionAdjunctionUnit J S (𝟙_ C) =
    inductionAdjunctionUnit J S (𝟙_ C) ≫ 𝟙 _
  rw [comp_id]

/-- Isomorphic object labels give the same actual coend cup class. -/
lemma inductionCup_iso {A B : C} (e : A ≅ B) : inductionCup S A = inductionCup S B := by
  have h := inductionCup_of_resolution S B (fun _ : Unit => A)
    (fun _ => e.hom) (fun _ => e.inv) (by simp) (by intro a; simp)
  simpa using h.symm

lemma inductionLoop_iso {A B : C} (e : A ≅ B) :
    inductionLoop S J A = inductionLoop S J B := by
  unfold inductionLoop
  rw [inductionCup_iso S e]

@[simp] lemma inductionLoop_unitLabel [Simple (𝟙_ C)] :
    inductionLoop S J (S.simpleObject S.unitLabel) = 𝟙 (inductionObj S J (𝟙_ C)) := by
  rw [inductionLoop_iso S J S.unitIso, inductionLoop_unit]

variable [Simple (𝟙_ C)]

/-- The categorical global dimension is the actual categorical dimension
of the central-induction object at the unit. -/
theorem inductionUnderlying_rightDim_unit :
    J.rightDim (inductionUnderlying S (𝟙_ C)) = (J.pivotalData S).globalDimension := by
  rw [J.rightDim_iso (inductionUnderlyingIso S (𝟙_ C))]
  let Y := fun i => (S.simpleObject i ⊗ 𝟙_ C) ⊗ (S.simpleObject i)ᘁ
  have htotal : ∑ i, biproduct.π Y i ≫ biproduct.ι Y i = 𝟙 (⨁ Y) := by
    apply biproduct.hom_ext'
    intro i
    simp only [Preadditive.comp_sum, biproduct.ι_π_assoc, dite_comp, zero_comp,
      Finset.sum_dite_eq, Finset.mem_univ, if_true, eqToHom_refl, id_comp, comp_id]
  have ht := J.rightTrace_of_resolution Y (biproduct.ι Y) (biproduct.π Y)
    htotal (𝟙 (⨁ Y))
  simp only [id_comp, biproduct.ι_π_self] at ht
  have hd : J.rightDim (⨁ Y) = ∑ i, J.rightDim (Y i) := by
    simpa only [PivotalStructure.rightDim, PivotalStructure.rightDimension, map_sum] using
      congrArg (unitScalarEquiv (C := C)) ht
  rw [hd]
  unfold Paper18.PivotalData.globalDimension Paper18.PivotalData.ndim
  apply Finset.sum_congr rfl
  intro i _
  change J.rightDim ((S.simpleObject i ⊗ 𝟙_ C) ⊗ (S.simpleObject i)ᘁ) =
    J.rightDim (S.simpleObject i) * J.rightDim (S.simpleObject (S.dualLabel i))
  rw [J.rightDim_tensor, J.rightDim_tensor, J.rightDim_unit S,
    J.rightDim_iso (S.dualIso i), mul_one]

/-- The unit-label case of the actual induction-loop trace formula. -/
theorem inductionLoop_rightTrace_unitLabel :
    unitScalarEquiv (C := C)
      (J.rightTrace (inductionLoop S J (S.simpleObject S.unitLabel)).f) =
        (J.pivotalData S).globalDimension := by
  rw [inductionLoop_unitLabel]
  exact inductionUnderlying_rightDim_unit S J

end Paper18.Category.Drinfeld
