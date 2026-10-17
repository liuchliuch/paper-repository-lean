import Paper18.Category.HopfLinkGauss
import Paper18.Category.InvertibleMonodromy

/-!
# Actual invertibles in the categorical Gauss-sum argument

The permutation of simple objects, preservation of squared dimensions, and
transport of twists are derived from actual tensor inverse data. The resulting
Gauss reindexing uses no combinatorial InvertibleTensor certificate.
-/
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
variable (J : PivotalStructure C)

/-- The actual squared pivotal dimension of an object. -/
def squaredDimension (X : C) : ℂ := J.rightDim X * J.rightDim (dual C X)

lemma squaredDimension_iso {X Y : C} (e : X ≅ Y) :
    J.squaredDimension X = J.squaredDimension Y := by
  unfold squaredDimension
  rw [J.rightDim_iso e, J.rightDim_iso (dualMapIso e).symm]

lemma squaredDimension_tensor (X Y : C) :
    J.squaredDimension (X ⊗ Y) = J.squaredDimension X * J.squaredDimension Y := by
  unfold squaredDimension
  rw [J.rightDim_tensor, J.rightDim_iso (dualTensorIso X Y), J.rightDim_tensor]
  ring

lemma squaredDimension_simple (S : FiniteSemisimpleSkeleton C ι) (i : ι) :
    J.squaredDimension (S.simpleObject i) = (J.pivotalData S).ndim i := by
  change J.rightDim (S.simpleObject i) * J.rightDim (dual C (S.simpleObject i)) = _
  rw [← J.rightDim_iso (S.dualIso i)]
  rfl

/-- Reindexing the actual Gauss sum by actual rigid duality gives the
slope-weighted expression. -/
lemma pivotalGaussSum_dual_reindex (S : FiniteSemisimpleSkeleton C ι) :
    J.pivotalGaussSum S = ∑ i, J.twistScalar (S.simpleObject i) *
      ((J.pivotalData S).gamma i)⁻¹ * (J.pivotalData S).ndim i := by
  let D := J.pivotalData S
  let e : ι ≃ ι := ⟨S.dualLabel, S.dualLabel,
    S.fusionBasis.dual_involutive, S.fusionBasis.dual_involutive⟩
  change (∑ i, J.twistScalar (S.simpleObject i) * D.ndim i) = _
  calc
    _ = ∑ i, J.twistScalar (S.simpleObject (S.dualLabel i)) *
        D.ndim (S.dualLabel i) :=
      (Equiv.sum_comp e (fun i => J.twistScalar (S.simpleObject i) * D.ndim i)).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [J.twistScalar_dualLabel S]
      exact congrArg (fun n => J.twistScalar (S.simpleObject i) *
        ((J.pivotalData S).gamma i)⁻¹ * n) (D.ndim_dual i)

end PivotalStructure

namespace TensorInverse
variable {T : C} (A : TensorInverse T) (S : FiniteSemisimpleSkeleton C ι)
  (J : PivotalStructure C)

include S A in
/-- The actual chosen inverse identifies the dual dimension with the inverse
of the original dimension. -/
lemma rightDim_inverse_mul : J.rightDim T * J.rightDim A.inverse = 1 := by
  rw [← J.rightDim_tensor, J.rightDim_iso A.right, J.rightDim_unit S]

include S A in
lemma squaredDimension_eq_one : J.squaredDimension T = 1 := by
  unfold PivotalStructure.squaredDimension
  rw [← J.rightDim_iso (A.inverseIsoDual S)]
  exact A.rightDim_inverse_mul S J

/-- The actual tensor permutation preserves actual squared dimensions. -/
lemma simplePermutation_squaredDimension (i : ι) :
    J.squaredDimension (S.simpleObject (A.simplePermutation S i)) =
      J.squaredDimension (S.simpleObject i) := by
  rw [← J.squaredDimension_iso (A.simplePermutationIso S i),
    J.squaredDimension_tensor, A.squaredDimension_eq_one S J, one_mul]

/-- Actual balancing and actual scalar monodromy determine the twist on
an invertible tensor product. -/
lemma twistScalar_tensor (X : C) [Simple T] [Simple X] [Simple (T ⊗ X)] :
    J.twistScalar (T ⊗ X) = J.twistScalar T * J.twistScalar X *
      TensorAutomorphism.scalar A.monodromyCharacter X := by
  apply smul_left_injective ℂ (CategoryTheory.id_nonzero (T ⊗ X))
  change J.twistScalar (T ⊗ X) • 𝟙 (T ⊗ X) =
    (J.twistScalar T * J.twistScalar X *
      TensorAutomorphism.scalar A.monodromyCharacter X) • 𝟙 (T ⊗ X)
  rw [J.twistScalar_spec, J.twist_tensor, ← J.twistScalar_spec T,
    ← J.twistScalar_spec X, A.doubleBraiding_scalar]
  simp [tensorHom_def, smul_smul, mul_comm, mul_left_comm, mul_assoc]

/-- The simple permutation's twist formula follows from actual object
isomorphisms and the preceding categorical balancing theorem. -/
lemma simplePermutation_twistScalar (i : ι) :
    letI := A.simple S
    J.twistScalar (S.simpleObject (A.simplePermutation S i)) =
      J.twistScalar T * J.twistScalar (S.simpleObject i) *
        TensorAutomorphism.scalar A.monodromyCharacter (S.simpleObject i) := by
  letI := A.simple S
  letI := A.simple_tensor S (S.simpleObject i)
  rw [← J.twistScalar_iso (A.simplePermutationIso S i)]
  exact A.twistScalar_tensor J (S.simpleObject i)

/-- The character of the actual inverse is the inverse natural isomorphism. -/
lemma monodromyCharacter_inverse : A.symm.monodromyCharacter = A.monodromyCharacter.symm := by
  ext X
  apply (cancel_epi (A.monodromyCharacter.hom.app X)).1
  exact (A.monodromyCharacter_comp_inverse X).trans
    (A.monodromyCharacter.hom_inv_id_app X).symm

/-- Inverse monodromy scalars follow from the actual inverse natural map. -/
lemma monodromyScalar_inverse (X : C) [Simple X] :
    TensorAutomorphism.scalar A.symm.monodromyCharacter X =
      (TensorAutomorphism.scalar A.monodromyCharacter X)⁻¹ := by
  rw [A.monodromyCharacter_inverse]
  exact TensorAutomorphism.inv_scalar A.monodromyCharacter X

include S A in
/-- An actual scalar monodromy equation fixes the derived Schur scalar. -/
lemma monodromyScalar_eq (X : C) [Simple X] (c : ℂ)
    (h : (doubleBraiding T X).hom = c • 𝟙 (T ⊗ X)) :
    TensorAutomorphism.scalar A.monodromyCharacter X = c := by
  letI := A.simple_tensor S X
  apply smul_left_injective ℂ (CategoryTheory.id_nonzero (T ⊗ X))
  exact (A.doubleBraiding_scalar X).symm.trans h

include S A in
/-- The actual Gauss sum reindexed by the actual inverse tensor permutation.
The slope hypothesis is an equation of actual double-braiding morphisms. -/
lemma pivotalGaussSum_inverse_reindex
    (h : ∀ i, (doubleBraiding T (S.simpleObject i)).hom =
      (J.pivotalData S).gamma i • 𝟙 (T ⊗ S.simpleObject i)) :
    letI := A.symm.simple S
    J.pivotalGaussSum S = J.twistScalar A.inverse * J.pivotalGaussSum S := by
  letI := A.symm.simple S
  have hc (i : ι) : TensorAutomorphism.scalar A.symm.monodromyCharacter
      (S.simpleObject i) = ((J.pivotalData S).gamma i)⁻¹ := by
    rw [A.monodromyScalar_inverse,
      A.monodromyScalar_eq S (S.simpleObject i) _ (h i)]
  calc
    J.pivotalGaussSum S = ∑ i, J.twistScalar (S.simpleObject i) *
        J.squaredDimension (S.simpleObject i) := by
      unfold PivotalStructure.pivotalGaussSum
      apply Finset.sum_congr rfl
      intro i _
      rw [J.squaredDimension_simple S]
      rfl
    _ = ∑ i, J.twistScalar (S.simpleObject (A.symm.simplePermutation S i)) *
        J.squaredDimension (S.simpleObject (A.symm.simplePermutation S i)) :=
      (Equiv.sum_comp (A.symm.simplePermutation S)
        (fun i => J.twistScalar (S.simpleObject i) *
          J.squaredDimension (S.simpleObject i))).symm
    _ = J.twistScalar A.inverse * ∑ i, J.twistScalar (S.simpleObject i) *
        ((J.pivotalData S).gamma i)⁻¹ * (J.pivotalData S).ndim i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [A.symm.simplePermutation_twistScalar S J,
        A.symm.simplePermutation_squaredDimension S J, hc,
        J.squaredDimension_simple S]
      ring
    _ = _ := by rw [← J.pivotalGaussSum_dual_reindex S]

include S A in
/-- Once nonvanishing has been established, the actual Gauss reindexing
forces the twist of an actual slope representative's inverse to be one.
Nonvanishing from categorical nondegeneracy is a separate theorem. -/
lemma twistScalar_inverse_eq_one_of_nonzeroGauss
    (hτ : J.pivotalGaussSum S ≠ 0)
    (h : ∀ i, (doubleBraiding T (S.simpleObject i)).hom =
      (J.pivotalData S).gamma i • 𝟙 (T ⊗ S.simpleObject i)) :
    letI := A.symm.simple S
    J.twistScalar A.inverse = 1 := by
  letI := A.symm.simple S
  have he := A.pivotalGaussSum_inverse_reindex S J h
  exact mul_right_cancel₀ hτ (he.symm.trans (one_mul _).symm)

end TensorInverse
end Paper18.Category
