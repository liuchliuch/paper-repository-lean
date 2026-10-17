import Paper18.Category.FusionCategory

/-! # Simple objects under actual fully faithful linear functors -/
noncomputable section
open Classical
open CategoryTheory CategoryTheory.Limits
open scoped BigOperators
universe v u w v' u' w'
namespace Paper18.Category

variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  {D : Type u'} [Category.{v'} D] [Preadditive D] [Linear ℂ D]

/-- The Hom equivalence of a fully faithful complex-linear functor is linear. -/
def fullyFaithfulHomLinearEquiv (F : C ⥤ D) [F.Additive] [F.Linear ℂ] [F.Full] [F.Faithful]
    (X Y : C) : (X ⟶ Y) ≃ₗ[ℂ] (F.obj X ⟶ F.obj Y) :=
  LinearEquiv.ofBijective (F.mapLinearMap ℂ)
    ⟨F.map_injective, F.map_surjective⟩

namespace FiniteSemisimpleSkeleton

variable [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  [HasKernels D] [HasFiniteBiproducts D]
  [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  {κ : Type w'} [Fintype κ] (T : FiniteSemisimpleSkeleton D κ)
  (F : C ⥤ D) [F.Additive] [F.Linear ℂ] [F.Full] [F.Faithful]

include T in
/-- Full faithfulness and linearity preserve simplicity in actual finite
semisimple categories, by the derived endomorphism criterion. -/
theorem simple_map (X : C) [Simple X] : Simple (F.obj X) := by
  apply T.simple_of_finrank_end_eq_one
  rw [← (fullyFaithfulHomLinearEquiv F X X).finrank_eq]
  exact CategoryTheory.finrank_endomorphism_simple_eq_one ℂ X

/-- The label of the actual simple image of a chosen source representative. -/
def simpleImageLabel (i : ι) : κ := by
  letI := T.simple_map F (S.simpleObject i)
  exact Classical.choose (T.simple_isomorphic_representative (F.obj (S.simpleObject i)))

/-- The image label is identified by an actual categorical isomorphism. -/
def simpleImageIso (i : ι) :
    F.obj (S.simpleObject i) ≅ T.simpleObject (S.simpleImageLabel T F i) := by
  letI := T.simple_map F (S.simpleObject i)
  exact Classical.choice (Classical.choose_spec
    (T.simple_isomorphic_representative (F.obj (S.simpleObject i))))

/-- Distinct actual source simples have distinct image labels. -/
theorem simpleImageLabel_injective : Function.Injective (S.simpleImageLabel T F) := by
  intro i j h
  apply S.iso_injective
  exact ⟨F.preimageIso (S.simpleImageIso T F i ≪≫
    eqToIso (congrArg T.simpleObject h) ≪≫ (S.simpleImageIso T F j).symm)⟩

/-- The image multiplicity matrix of a fully faithful linear functor is the
matrix of the injection on actual simple isomorphism classes. -/
theorem imageCoeff_fullyFaithful (i : ι) (j : κ) :
    S.imageCoeff T F i j = if j = S.simpleImageLabel T F i then 1 else 0 := by
  unfold imageCoeff
  rw [T.multiplicity_iso (S.simpleImageIso T F i), T.multiplicity_simple]

section Monoidal
open CategoryTheory.MonoidalCategory
attribute [local instance 2000] RightRigidCategory.rightDual
variable [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [RightRigidCategory C] [Simple (𝟙_ C)]
  [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalLinear ℂ D]
  [RightRigidCategory D] [Simple (𝟙_ D)] [F.Monoidal]

/-- The injection of actual simple classes preserves their derived FP
dimensions. -/
theorem fpdim_simpleImageLabel (i : ι) :
    T.fusionBasis.fpdim (S.simpleImageLabel T F i) = S.fusionBasis.fpdim i := by
  calc
    _ = T.fpdim (T.simpleObject (S.simpleImageLabel T F i)) := (T.fpdim_simple _).symm
    _ = T.fpdim (F.obj (S.simpleObject i)) := (T.fpdim_iso (S.simpleImageIso T F i)).symm
    _ = _ := by rw [S.fpdim_map_simple T F, S.fpdim_simple]

include F in
/-- The total FP dimension of a full fusion subcategory is at most that
of its ambient category, using the actual injection on simple objects. -/
theorem totalFPdim_le_of_fullyFaithful :
    S.fusionBasis.totalFPdim ≤ T.fusionBasis.totalFPdim := by
  calc
    _ = ∑ i, T.fusionBasis.fpdim (S.simpleImageLabel T F i) ^ 2 := by
      simp only [S.fpdim_simpleImageLabel T F]
      rfl
    _ = ∑ j ∈ Finset.univ.image (S.simpleImageLabel T F), T.fusionBasis.fpdim j ^ 2 := by
      rw [Finset.sum_image]
      intro i _ j _ h
      exact S.simpleImageLabel_injective T F h
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun j _ _ => sq_nonneg _)

end Monoidal

section Independence
open CategoryTheory.MonoidalCategory
variable [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [RightRigidCategory C] [Simple (𝟙_ C)]

/-- The total categorical FP dimension does not depend on the complete
simple family chosen to compute it. -/
theorem totalFPdim_independent {κ : Type w'} [Fintype κ]
    (T : FiniteSemisimpleSkeleton C κ) :
    S.fusionBasis.totalFPdim = T.fusionBasis.totalFPdim :=
  le_antisymm (S.totalFPdim_le_of_fullyFaithful T (𝟭 C))
    (T.totalFPdim_le_of_fullyFaithful S (𝟭 C))

end Independence

end FiniteSemisimpleSkeleton
end Paper18.Category
