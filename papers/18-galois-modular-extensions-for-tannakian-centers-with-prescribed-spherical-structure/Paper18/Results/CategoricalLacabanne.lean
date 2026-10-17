import Paper18.Category.DrinfeldSemisimple
import Paper18.Category.DrinfeldCharacterMonodromy
import Paper18.Category.PivotalSlope
import Paper18.Category.HopfLinkInvertible
import Paper18.Category.HopfLinkNondegenerate

/-! # The actual slope representative in Lemma 2.1

The center skeleton used in the factorization is constructed from the actual
category. Genuine Müger nondegeneracy gives the nonzero categorical Gauss sum
needed for the inverse-twist assertion.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
universe v u w
namespace Paper18.Category
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [RightRigidCategory C] [Preadditive C] [Linear ℂ C]
  [MonoidalPreadditive C] [MonoidalLinear ℂ C] [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ C)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  (J : PivotalStructure C) (hC : IsNondegenerate (C := C))

include S hC

theorem lacabanne_representative :
    ∃ t : C, ∃ A : TensorInverse t, A.monodromyCharacter = J.slope := by
  obtain ⟨i,A,hA⟩ := Drinfeld.monodromyCharacter_surjective_of_centerSkeleton
    S J.slope J (Drinfeld.centerSkeleton S J) hC
  exact ⟨S.simpleObject i,A,hA⟩

theorem lacabanne_representative_unique :
    ∃ t : C, ∃ A : TensorInverse t,
      (∀ X : C, Simple X → (doubleBraiding t X).hom =
        (J.rightDim X / J.rightDim (dual C X)) • 𝟙 (t ⊗ X)) ∧
      (∀ u : C, TensorInverse u →
        (∀ X : C, Simple X → (doubleBraiding u X).hom =
          (J.rightDim X / J.rightDim (dual C X)) • 𝟙 (u ⊗ X)) → Nonempty (t ≅ u)) := by
  obtain ⟨t,A,hA⟩ := lacabanne_representative S J hC
  refine ⟨t,A,?_,?_⟩
  · intro X hX
    letI := hX
    rw [A.doubleBraiding_scalar, hA, J.slope_scalar S]
  · intro u B hB
    have he : B.monodromyCharacter = J.slope := by
      apply B.monodromyCharacter_eq_of_simple_spec S J.slope
      intro i
      rw [J.slope_scalar S]
      exact hB (S.simpleObject i) (S.simple i)
    exact ⟨isoOfEqualMonodromy S hC A B (hA.trans he.symm)⟩

omit hC in
theorem lacabanne_inverse_twist_of_nonzeroGauss {t : C} (A : TensorInverse t)
    (hA : A.monodromyCharacter = J.slope) (hτ : J.pivotalGaussSum S ≠ 0) :
    (J.twistIso A.inverse).hom = 𝟙 A.inverse := by
  have hγ (i : ι) : (doubleBraiding t (S.simpleObject i)).hom =
      (J.pivotalData S).gamma i • 𝟙 (t ⊗ S.simpleObject i) := by
    rw [A.doubleBraiding_scalar, hA, J.slope_scalar_gamma S]
  letI := A.symm.simple S
  have hθ := A.twistScalar_inverse_eq_one_of_nonzeroGauss S J hτ hγ
  calc
    (J.twistIso A.inverse).hom = J.twistScalar A.inverse • 𝟙 A.inverse :=
      (J.twistScalar_spec A.inverse).symm
    _ = 𝟙 A.inverse := by rw [hθ, one_smul]

/-- Original Lemma 2.1, including the inverse twist and uniqueness. Every
categorical hypothesis is a structure or property of the actual category. -/
theorem lemma2_1 :
    ∃ t : C, ∃ A : TensorInverse t,
      (∀ X : C, Simple X → (doubleBraiding t X).hom =
        (J.rightDim X / J.rightDim (dual C X)) • 𝟙 (t ⊗ X)) ∧
      (J.twistIso A.inverse).hom = 𝟙 A.inverse ∧
      (∀ u : C, TensorInverse u →
        (∀ X : C, Simple X → (doubleBraiding u X).hom =
          (J.rightDim X / J.rightDim (dual C X)) • 𝟙 (u ⊗ X)) → Nonempty (t ≅ u)) := by
  obtain ⟨t,A,hA⟩ := lacabanne_representative S J hC
  have hspec (X : C) (hX : Simple X) : (doubleBraiding t X).hom =
      (J.rightDim X / J.rightDim (dual C X)) • 𝟙 (t ⊗ X) := by
    letI := hX
    rw [A.doubleBraiding_scalar, hA, J.slope_scalar S]
  refine ⟨t,A,hspec,?_,?_⟩
  · exact lacabanne_inverse_twist_of_nonzeroGauss S J A hA
      (J.pivotalGaussSum_ne_zero S hC)
  · intro u B hB
    have he : B.monodromyCharacter = J.slope := by
      apply B.monodromyCharacter_eq_of_simple_spec S J.slope
      intro i
      rw [J.slope_scalar S]
      exact hB (S.simpleObject i) (S.simple i)
    exact ⟨isoOfEqualMonodromy S hC A B (hA.trans he.symm)⟩

end Paper18.Category
