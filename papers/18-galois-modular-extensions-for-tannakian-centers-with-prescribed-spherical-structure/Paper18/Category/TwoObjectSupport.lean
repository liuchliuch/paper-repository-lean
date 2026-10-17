import Paper18.Category.CentralizerDimensionBasic
import Paper18.Category.InvertibleObjects

/-! # Actual simple support at total FP dimension two

The unit and a nontrivial invertible already account for two units of
positive FP dimension. Equality with two therefore excludes every further
actual simple object, without assuming a classification of rank-two categories.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped BigOperators
universe v u w
namespace Paper18.Category.FiniteSemisimpleSkeleton
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [RightRigidCategory C] [Simple (𝟙_ C)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)

lemma twoObject_supportFPdim {e : C} (E : TensorInverse e)
    (hne : ¬ Nonempty (e ≅ 𝟙_ C)) :
    S.supportFPdim (fun X => Nonempty (X ≅ 𝟙_ C) ∨ Nonempty (X ≅ e)) = 2 := by
  letI := E.simple S
  obtain ⟨i,⟨ei⟩⟩ := S.simple_isomorphic_representative e
  have hi : i ≠ S.unitLabel := by
    intro h
    exact hne ⟨ei ≪≫ (eqToIso (congrArg S.simpleObject h)) ≪≫ S.unitIso⟩
  have hu (k : ι) : Nonempty (S.simpleObject k ≅ 𝟙_ C) ↔ k = S.unitLabel := by
    constructor
    · rintro ⟨a⟩
      exact S.iso_injective _ _ ⟨a ≪≫ S.unitIso.symm⟩
    · rintro rfl
      exact ⟨S.unitIso⟩
  have he (k : ι) : Nonempty (S.simpleObject k ≅ e) ↔ k = i := by
    constructor
    · rintro ⟨a⟩
      exact S.iso_injective _ _ ⟨a ≪≫ ei⟩
    · rintro rfl
      exact ⟨ei.symm⟩
  have hdu : S.fusionBasis.fpdim S.unitLabel = 1 := by
    rw [← S.fpdim_simple, S.fpdim_iso S.unitIso, S.fpdim_unit]
  have hde : S.fusionBasis.fpdim i = 1 := by
    rw [← S.fpdim_simple, ← S.fpdim_iso ei]
    exact S.fpdim_eq_one_of_tensorInvertible ⟨E⟩
  unfold supportFPdim
  simp_rw [hu, he]
  have hterm (k : ι) :
      (if k = S.unitLabel ∨ k = i then S.fusionBasis.fpdim k ^ 2 else 0) =
        (if k = S.unitLabel then (1 : ℝ) else 0) + (if k = i then (1 : ℝ) else 0) := by
    by_cases hk : k = S.unitLabel
    · subst k
      simp [hdu, Ne.symm hi]
    · by_cases hki : k = i
      · subst k
        simp [hde, hi]
      · simp [hk,hki]
  simp_rw [hterm]
  rw [Finset.sum_add_distrib]
  norm_num

/-- Actual support of a full additive subcategory at dimension two.
The only two possible simple objects are derived from positivity of all
actual simple FP dimensions. -/
theorem simple_support_of_fpdim_two (P : ObjectProperty C) [IsAdditiveFullProperty P]
    {e : C} (E : TensorInverse e) (hne : ¬ Nonempty (e ≅ 𝟙_ C))
    (hu : P (𝟙_ C)) (he : P e) (hd : S.supportFPdim P = 2)
    (X : C) [Simple X] (hX : P X) :
    Nonempty (X ≅ 𝟙_ C) ∨ Nonempty (X ≅ e) := by
  let Q : ObjectProperty C := fun Y => Nonempty (Y ≅ 𝟙_ C) ∨ Nonempty (Y ≅ e)
  have hQP : ∀ Y, Q Y → P Y := by
    intro Y hY
    change Nonempty (Y ≅ 𝟙_ C) ∨ Nonempty (Y ≅ e) at hY
    rcases hY with hY | hY
    · exact IsAdditiveFullProperty.of_iso P (Classical.choice hY) hu
    · exact IsAdditiveFullProperty.of_iso P (Classical.choice hY) he
  obtain ⟨i,⟨a⟩⟩ := S.simple_isomorphic_representative X
  have hp : P (S.simpleObject i) := IsAdditiveFullProperty.of_iso P a.symm hX
  have hq : Q (S.simpleObject i) := by
    by_contra hn
    have hlt := S.supportFPdim_lt_of_missing hQP i hp hn
    rw [hd, S.twoObject_supportFPdim E hne] at hlt
    exact (lt_irrefl (2 : ℝ)) hlt
  change Nonempty (S.simpleObject i ≅ 𝟙_ C) ∨ Nonempty (S.simpleObject i ≅ e) at hq
  rcases hq with hq | hq
  · exact Or.inl ⟨a ≪≫ Classical.choice hq⟩
  · exact Or.inr ⟨a ≪≫ Classical.choice hq⟩

end Paper18.Category.FiniteSemisimpleSkeleton
