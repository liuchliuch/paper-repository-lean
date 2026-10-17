import Paper18.Category.DrinfeldSemisimpleTrace

/-! # Actual Schur orthogonality after pivotal rigid rotation -/
noncomputable section
universe v u w
namespace Paper18.Category.Drinfeld
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
attribute [local instance 2000] RightRigidCategory.rightDual

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]

lemma averagingRotationDown_eq (J : PivotalStructure C) (U A B : C)
    (u : B ⟶ dual C U ⊗ A) :
    averagingRotationDown J U A B u =
      (@tensorLeftHomEquiv C _ _ B (dual C U) U A (J.leftExactPairing U)).symm u := by
  dsimp only [averagingRotationDown, tensorLeftHomEquiv]
  change _ = U ◁ u ≫ (α_ U (dual C U) A).inv ≫
    J.leftEvaluation U ▷ A ≫ (λ_ A).hom
  monoidal

lemma averagingRotationUp_eq (U A B : C) (p : dual C U ⊗ A ⟶ B) :
    averagingRotationUp U A B p = tensorLeftHomEquiv A U (dual C U) B p := by
  dsimp only [averagingRotationUp, tensorLeftHomEquiv]
  change _ = (λ_ A).inv ≫ η_ U (dual C U) ▷ A ≫
    (α_ U (dual C U) A).hom ≫ U ◁ p
  monoidal

/-- The downward rotation is an actual Hom equivalence. -/
def averagingRotationDownEquiv (J : PivotalStructure C) (U A B : C) :
    (B ⟶ dual C U ⊗ A) ≃ (U ⊗ B ⟶ A) :=
  (@tensorLeftHomEquiv C _ _ B (dual C U) U A (J.leftExactPairing U)).symm

/-- The upward rotation is the actual chosen rigid Hom equivalence. -/
def averagingRotationUpEquiv (U A B : C) :
    (dual C U ⊗ A ⟶ B) ≃ (A ⟶ U ⊗ B) :=
  tensorLeftHomEquiv A U (dual C U) B

section Linear
variable [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [Simple (𝟙_ C)]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]

/-- On an actual simple object, the left trace determines every endomorphism
up to precisely its actual left categorical dimension. -/
lemma leftDim_smul_end (J : PivotalStructure C) (A : C) [Simple A] (f : A ⟶ A) :
    J.leftDim A • f = unitScalarEquiv (J.leftTrace f) • 𝟙 A := by
  obtain ⟨c, hc⟩ := CategoryTheory.endomorphism_simple_eq_smul_id ℂ f
  rw [← hc, J.leftTrace_smul_id, smul_smul, mul_comm]

/-- Weighted Schur orthogonality is derived from the actual pivotal trace
rotation identity, without assigning any numerical pairing data. -/
lemma averagingRotation_weighted (J : PivotalStructure C) (U A B : C) [Simple A]
    (u : B ⟶ dual C U ⊗ A) (p : dual C U ⊗ A ⟶ B) :
    J.leftDim A • (averagingRotationUp U A B p ≫ averagingRotationDown J U A B u) =
      unitScalarEquiv (J.leftTrace (u ≫ p)) • 𝟙 A := by
  rw [leftDim_smul_end, averagingRotation_trace]

/-- In particular, an actual scalar composition before rotation becomes
the categorical dimension ratio after rotation. -/
lemma averagingRotation_weighted_of_scalar (J : PivotalStructure C)
    (U A B : C) [Simple A] (u : B ⟶ dual C U ⊗ A)
    (p : dual C U ⊗ A ⟶ B) (c : ℂ) (h : u ≫ p = c • 𝟙 B) :
    J.leftDim A • (averagingRotationUp U A B p ≫ averagingRotationDown J U A B u) =
      (c * J.leftDim B) • 𝟙 A := by
  rw [averagingRotation_weighted, h, J.leftTrace_smul_id]

end Linear
end Paper18.Category.Drinfeld
