import Paper18.Category.FixedBoundaryBosonGrading
import Paper18.Category.SignKernelDimensions
import Paper18.Category.CentralizerFusion

/-! # Actual weak integrality from order-two monodromy

The actual monodromy character is involutive by the two braiding hexagons.
Its neutral category is the actual centralizer. An integral neutral category
therefore has integer total FP dimension; a nontrivial grading doubles that
integer. No pivotal structure on the ambient category is used.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped BigOperators
universe v u w
namespace Paper18.Category
attribute [local instance 2000] RightRigidCategory.rightDual

section Neutral
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [Preadditive C] [Linear ℂ C] {e : C} (E : TensorInverse e)

/-- The neutral object equation for actual invertible-object monodromy
is precisely membership in the actual categorical centralizer. -/
lemma TensorInverse.monodromy_positiveProperty_eq_centralizer :
    SignKernel.positiveProperty E.monodromyCharacter = centralizerProperty ({e} : Set C) := by
  funext X
  apply propext
  change FixedBoundary.Homogeneous E.monodromyCharacter 0 X ↔ X ∈ centralizer {e}
  rw [E.monodromy_neutral_iff]
  constructor
  · intro h Y hY
    obtain rfl := Set.mem_singleton_iff.mp hY
    exact h.symm
  · intro h
    exact (h e (Set.mem_singleton e)).symm
end Neutral

namespace FiniteSemisimpleSkeleton
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [RightRigidCategory C] [Simple (𝟙_ C)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)

/-- Actual integrality of an inherited full fusion subcategory makes its
support FP dimension an integer, by the actual ambient simple FP dimensions. -/
lemma supportFPdim_integer_of_fullSubcategoryIntegral
    (P : ObjectProperty C) [IsAdditiveFullProperty P] [P.IsMonoidal]
    (hP : S.FullSubcategoryIntegral P) : ∃ n : ℤ, S.supportFPdim P = n := by
  have hn (i : ι) : ∃ n : ℤ,
      (if P (S.simpleObject i) then S.fusionBasis.fpdim i ^ 2 else 0) = n := by
    by_cases hp : P (S.simpleObject i)
    · obtain ⟨n, hn⟩ := (S.fullSubcategoryIntegral_iff P).mp hP i hp
      rw [S.fpdim_simple] at hn
      exact ⟨n ^ 2, by simp only [if_pos hp, hn, Int.cast_pow]⟩
    · exact ⟨0, by simp only [if_neg hp, Int.cast_zero]⟩
  choose n hn using hn
  refine ⟨∑ i, n i, ?_⟩
  simp only [FiniteSemisimpleSkeleton.supportFPdim, Int.cast_sum, ← hn]

variable [BraidedCategory C]

/-- The actual monodromy-neutral fusion category has integer FP dimension
when the actual centralizer of the invertible object is integral. -/
lemma monodromy_positive_support_integer {e : C} (E : TensorInverse e)
    (hI : S.CentralizerIntegral {e}) :
    ∃ n : ℤ, S.supportFPdim (SignKernel.positiveProperty E.monodromyCharacter) = n := by
  rw [E.monodromy_positiveProperty_eq_centralizer]
  exact S.supportFPdim_integer_of_fullSubcategoryIntegral (centralizerProperty {e}) hI

/-- An actual order-two invertible object with integral actual centralizer
forces weak integrality of the actual ambient fusion category. This proof
uses no ambient pivotal, spherical, positive, or nondegenerate structure. -/
theorem weaklyIntegral_of_orderTwo_centralizerIntegral {e : C} (E : TensorInverse e)
    (q : e ⊗ e ≅ 𝟙_ C) (hI : S.CentralizerIntegral {e}) :
    S.fusionBasis.WeaklyIntegral := by
  obtain ⟨n, hn⟩ := S.monodromy_positive_support_integer E hI
  by_cases h : ∀ X : C, E.monodromyCharacter.hom.app X = 𝟙 X
  · have hp (i : ι) : SignKernel.positiveProperty E.monodromyCharacter (S.simpleObject i) :=
      (SignKernel.mem_positive E.monodromyCharacter _).mpr (h _)
    have hd : S.supportFPdim (SignKernel.positiveProperty E.monodromyCharacter) =
        S.fusionBasis.totalFPdim := by
      simp only [FiniteSemisimpleSkeleton.supportFPdim, hp, if_true, FusionBasis.totalFPdim]
    exact ⟨n, hd.symm.trans hn⟩
  · obtain ⟨X, hX⟩ := not_forall.mp h
    have hd := SignKernel.supportFPdim_indexTwo_of_nontrivial S E.monodromyCharacter
      (E.monodromy_involutive_of_square q) X hX
    refine ⟨2 * n, ?_⟩
    rw [hd, hn, Int.cast_mul, Int.cast_ofNat]

end FiniteSemisimpleSkeleton
end Paper18.Category
