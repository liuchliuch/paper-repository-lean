import Paper18.Category.TwoObjectSupport

/-! # Actual centralizers of an additive subcategory of FP dimension two -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
universe v u w
namespace Paper18.Category.FiniteSemisimpleSkeleton
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [RightRigidCategory C] [Simple (𝟙_ C)] [BraidedCategory C]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)

/-- The actual centralizer of an actual additive subcategory of dimension two
is the actual centralizer of its nontrivial invertible. Every object of the
subcategory is handled through its actual finite simple decomposition. -/
theorem centralizer_eq_singleton_of_fpdim_two (P : ObjectProperty C)
    [IsAdditiveFullProperty P] {e : C} (E : TensorInverse e)
    (hne : ¬ Nonempty (e ≅ 𝟙_ C)) (hu : P (𝟙_ C)) (he : P e)
    (hd : S.supportFPdim P = 2) : centralizer (P : Set C) = centralizer {e} := by
  ext X
  constructor
  · intro h Y hY
    rcases Set.mem_singleton_iff.mp hY with rfl
    exact h _ he
  · intro h Y hY
    have hXe : Centralizes X e := h e (Set.mem_singleton _)
    apply (centralizes_iso_right (S.decomposition Y)).mpr
    apply Centralizes.symm
    apply centralizes_biproduct_left
    intro a
    have hp := S.property_label P (⟨Y, hY⟩ : P.FullSubcategory) a
    rcases S.simple_support_of_fpdim_two P E hne hu he hd
      (S.simpleObject (S.label Y a)) hp with hunit | hinv
    · exact (centralizes_unit_left X).of_iso_left (Classical.choice hunit)
    · exact hXe.symm.of_iso_left (Classical.choice hinv)

end Paper18.Category.FiniteSemisimpleSkeleton
