import Paper18.Category.DrinfeldInductionAdjunctionFunctor
import Paper18.Category.DrinfeldSemisimpleSliding
import Paper18.Category.ENOPseudounitaryCharacterAction

/-!
# Actual cup classes and loop morphisms on central induction

The cup class is an actual morphism into the actual induction coend, and
the loop morphism is obtained from its proved adjunction. Additivity below
is derived from actual biproduct resolutions and coend dinaturality.
Multiplication is derived from actual nested cups and caps. Their pivotal
trace is a further identity needed for the ENO FP projection, and is not
assumed here.
-/

noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped BigOperators
universe v u w w'

namespace Paper18.Category.Drinfeld
attribute [local instance 2000] RightRigidCategory.rightDual

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)

/-- The actual cup into the induction coend at the unit. -/
def inductionCup (T : C) : 𝟙_ C ⟶ inductionUnderlying S (𝟙_ C) :=
  η_ T Tᘁ ≫ (ρ_ T).inv ▷ Tᘁ ≫ inductionι S (𝟙_ C) T

include S in
lemma inductionCup_of_resolution (Y : C) {κ : Type w'} [Fintype κ]
    (A : κ → C) (u : ∀ a, A a ⟶ Y) (p : ∀ a, Y ⟶ A a)
    (h : ∑ a, p a ≫ u a = 𝟙 Y) (hup : ∀ a, u a ≫ p a = 𝟙 (A a)) :
    inductionCup S Y = ∑ a, inductionCup S (A a) := by
  unfold inductionCup
  rw [inductionι_of_resolution S (𝟙_ C) Y A u p h]
  simp only [Preadditive.comp_sum]
  apply Finset.sum_congr rfl
  intro a _
  calc
    _ = η_ Y Yᘁ ≫ p a ▷ Yᘁ ≫ A a ◁ rightAdjointMate (u a) ≫
        (ρ_ (A a)).inv ▷ (A a)ᘁ ≫ inductionι S (𝟙_ C) (A a) := by
      dsimp only [dualMap, dual]
      monoidal
    _ = η_ (A a) (A a)ᘁ ≫ A a ◁ rightAdjointMate (p a) ≫
        A a ◁ rightAdjointMate (u a) ≫
        (ρ_ (A a)).inv ▷ (A a)ᘁ ≫ inductionι S (𝟙_ C) (A a) := by
      rw [← coevaluation_comp_rightAdjointMate_assoc]
    _ = _ := by
      rw [← whiskerLeft_comp_assoc, ← comp_rightAdjointMate, hup]
      simp only [rightAdjointMate_id, whiskerLeft_id, id_comp]

/-- The actual cup class is the sum of the cups of the actual simple
summands, proved from the fixed finite biproduct decomposition. -/
lemma inductionCup_decomposition (Y : C) :
    inductionCup S Y = ∑ a : Fin (S.length Y),
      inductionCup S (S.simpleObject (S.label Y a)) := by
  apply inductionCup_of_resolution S Y
    (fun a => S.simpleObject (S.label Y a)) (S.coendInclusion Y) (S.coendProjection Y)
    (S.coendResolution Y)
  intro a
  simp [FiniteSemisimpleSkeleton.coendInclusion, FiniteSemisimpleSkeleton.coendProjection]

/-- Grouping actual simple summands by their labels expresses the actual
cup as an integral linear combination with the derived multiplicities. -/
lemma inductionCup_multiplicity (Y : C) :
    inductionCup S Y = ∑ i, (S.multiplicity Y i : ℂ) •
      inductionCup S (S.simpleObject i) := by
  rw [inductionCup_decomposition S Y]
  symm
  simp_rw [S.multiplicity_eq_sum, Nat.cast_sum, Finset.sum_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp

variable (J : PivotalStructure C)

/-- The actual central loop corresponding to a cup class, using the proved
complex-linear central induction adjunction. -/
def inductionLoop (T : C) : inductionObj S J (𝟙_ C) ⟶ inductionObj S J (𝟙_ C) :=
  (inductionHomLinearEquiv S J (𝟙_ C) (inductionObj S J (𝟙_ C))).symm
    (inductionCup S T)

@[simp] lemma inductionLoop_under_adjunction (T : C) :
    inductionHomLinearEquiv S J (𝟙_ C) (inductionObj S J (𝟙_ C))
      (inductionLoop S J T) = inductionCup S T :=
  LinearEquiv.apply_symm_apply _ _

@[simp] lemma inductionLoop_f (T : C) :
    (inductionLoop S J T).f = inductionAugmentation J S
      (inductionObj S J (𝟙_ C)) (inductionCup S T) := rfl

/-- The cup class is the character action applied to the actual adjunction
unit. This follows from the inverse identities of the proved adjunction. -/
lemma inductionCup_eq_characterAction (T : C) :
    inductionCup S T = characterAction J (inductionObj S J (𝟙_ C)) T
      (inductionAdjunctionUnit J S (𝟙_ C)) := by
  have h := (inductionHomLinearEquiv S J (𝟙_ C)
    (inductionObj S J (𝟙_ C))).symm_apply_apply (𝟙 (inductionObj S J (𝟙_ C)))
  have hi := congrArg (fun g => g.f) h
  change inductionAugmentation J S (inductionObj S J (𝟙_ C))
    (inductionAdjunctionUnit J S (𝟙_ C) ≫ 𝟙 _) = 𝟙 _ at hi
  simp only [comp_id] at hi
  have ht := inductionι_augmentation J S (inductionObj S J (𝟙_ C))
    (inductionAdjunctionUnit J S (𝟙_ C)) T
  rw [hi, comp_id] at ht
  dsimp only [inductionCup, characterAction]
  rw [← ht]

/-- Composition of actual central loop morphisms is tensor product of
their labels. The proof uses the actual adjunction and the nested cup-cap
identity for the character action. -/
lemma inductionLoop_comp (A B : C) :
    inductionLoop S J A ≫ inductionLoop S J B = inductionLoop S J (A ⊗ B) := by
  apply (inductionHomLinearEquiv S J (𝟙_ C)
    (inductionObj S J (𝟙_ C))).injective
  rw [inductionLoop_under_adjunction]
  change inductionAdjunctionUnit J S (𝟙_ C) ≫
      (inductionLoop S J A ≫ inductionLoop S J B).f = inductionCup S (A ⊗ B)
  have he : inductionAdjunctionUnit J S (𝟙_ C) ≫ (inductionLoop S J A).f =
      inductionCup S A := inductionLoop_under_adjunction S J A
  rw [Center.comp_f, ← Category.assoc, he, inductionLoop_f]
  dsimp only [inductionCup]
  rw [Category.assoc, Category.assoc, inductionι_augmentation]
  change characterAction J (inductionObj S J (𝟙_ C)) A (inductionCup S B) =
    inductionCup S (A ⊗ B)
  rw [inductionCup_eq_characterAction S J B, ← characterAction_tensor,
    ← inductionCup_eq_characterAction S J (A ⊗ B)]

lemma inductionLoop_multiplicity (T : C) :
    inductionLoop S J T = ∑ i, (S.multiplicity T i : ℂ) •
      inductionLoop S J (S.simpleObject i) := by
  unfold inductionLoop
  rw [inductionCup_multiplicity S T, map_sum]
  simp only [map_smul]

/-- Tensor objects give the derived fusion coefficients when expanded in
the actual central cup-loop family. -/
lemma inductionLoop_tensor_decomposition (i j : ι) :
    inductionLoop S J (S.simpleObject i ⊗ S.simpleObject j) =
      ∑ k, (S.fusionCoeff i j k : ℂ) • inductionLoop S J (S.simpleObject k) :=
  inductionLoop_multiplicity S J _

/-- The actual endomorphisms of the induction object carry the derived
fusion multiplication, with the actual categorical fusion coefficients. -/
lemma inductionLoop_fusion (i j : ι) :
    inductionLoop S J (S.simpleObject i) ≫ inductionLoop S J (S.simpleObject j) =
      ∑ k, (S.fusionCoeff i j k : ℂ) • inductionLoop S J (S.simpleObject k) := by
  rw [inductionLoop_comp, inductionLoop_tensor_decomposition]

end Paper18.Category.Drinfeld
