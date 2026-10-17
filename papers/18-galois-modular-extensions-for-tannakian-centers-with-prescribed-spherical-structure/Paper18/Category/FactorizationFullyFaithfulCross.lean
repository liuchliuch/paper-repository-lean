import Paper18.Category.FactorizationBasic
import Paper18.Category.DrinfeldBiproducts
import Paper18.Category.NondegenerateBasic
import Paper18.Category.FunctorImage

/-!
# Actual Hom spaces between the two canonical center images

For a Müger nondegenerate category, a nonzero map between a positive simple
and a negative simple forces both labels to be the tensor unit. Decomposing
actual objects then computes every cross Hom dimension by unit multiplicities.
-/
noncomputable section
open Classical
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits CategoryTheory.Functor.Monoidal
open scoped BigOperators
universe v u w
namespace Paper18.Category.Drinfeld
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ C)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  (hC : IsNondegenerate (C := C))
include hC

/-- A nonzero actual morphism between the two simple images forces both
simple labels to be the tensor unit. -/
lemma positive_negative_simple_nonzero {i j : ι}
    (f : (positive C).obj (S.simpleObject i) ⟶ (negative C).obj (S.simpleObject j))
    (hf : f ≠ 0) : i = S.unitLabel ∧ j = S.unitLabel := by
  have hfu : f.f ≠ 0 := by
    intro h
    apply hf
    apply Center.ext
    exact h
  letI : IsIso f.f := CategoryTheory.isIso_of_hom_simple (X := S.simpleObject i)
    (Y := S.simpleObject j) hfu
  have hi : i = S.unitLabel := by
    apply ((nondegenerate_iff_simple_center S).mp hC) i
    apply (positive_mem_essentialImage_negative_iff (S.simpleObject i)).mp
    exact ⟨S.simpleObject j, ⟨Center.isoMk f⟩⟩
  have hij : i = j := S.iso_injective i j ⟨asIso f.f⟩
  exact ⟨hi, hij.symm.trans hi⟩

/-- All cross morphisms vanish away from the common unit label. -/
lemma positive_negative_simple_hom_eq_zero (i j : ι)
    (h : i ≠ S.unitLabel ∨ j ≠ S.unitLabel)
    (f : (positive C).obj (S.simpleObject i) ⟶ (negative C).obj (S.simpleObject j)) :
    f = 0 := by
  by_contra hf
  obtain ⟨hi, hj⟩ := positive_negative_simple_nonzero S hC f hf
  rcases h with h | h
  · exact h hi
  · exact h hj

/-- The unit is the only nonzero cross Hom block, and that block is
one-dimensional by actual Schur's lemma. -/
lemma finrank_positive_negative_simple (i j : ι) :
    Module.finrank ℂ
      ((positive C).obj (S.simpleObject i) ⟶ (negative C).obj (S.simpleObject j)) =
        (if i = S.unitLabel then 1 else 0) * (if j = S.unitLabel then 1 else 0) := by
  by_cases hi : i = S.unitLabel
  · subst i
    by_cases hj : j = S.unitLabel
    · subst j
      let eP := (positive C).mapIso S.unitIso
      let eN := (negative C).mapIso S.unitIso ≪≫
        (εIso (negative C)).symm ≪≫ εIso (positive C)
      rw [finrank_hom_iso eP eN,
        ← (fullyFaithfulHomLinearEquiv (positive C) (𝟙_ C) (𝟙_ C)).finrank_eq]
      simpa using CategoryTheory.finrank_endomorphism_simple_eq_one ℂ (𝟙_ C)
    · letI : Subsingleton
          ((positive C).obj (S.simpleObject S.unitLabel) ⟶ (negative C).obj (S.simpleObject j)) :=
        ⟨fun f g => (positive_negative_simple_hom_eq_zero S hC _ _ (Or.inr hj) f).trans
          (positive_negative_simple_hom_eq_zero S hC _ _ (Or.inr hj) g).symm⟩
      simp only [Module.finrank_zero_of_subsingleton, if_neg hj, mul_zero]
  · letI : Subsingleton
        ((positive C).obj (S.simpleObject i) ⟶ (negative C).obj (S.simpleObject j)) :=
      ⟨fun f g => (positive_negative_simple_hom_eq_zero S hC _ _ (Or.inl hi) f).trans
        (positive_negative_simple_hom_eq_zero S hC _ _ (Or.inl hi) g).symm⟩
    simp only [Module.finrank_zero_of_subsingleton, if_neg hi, zero_mul]

/-- Actual finite semisimple decompositions give the complete cross Hom
dimension formula, without semisimplicity of the center as an input. -/
lemma finrank_positive_negative (X Y : C) :
    Module.finrank ℂ ((positive C).obj X ⟶ (negative C).obj Y) =
      S.multiplicity X S.unitLabel * S.multiplicity Y S.unitLabel := by
  let eP : (positive C).obj X ≅
      ⨁ fun a : Fin (S.length X) => (positive C).obj (S.simpleObject (S.label X a)) :=
    (positive C).mapIso (S.decomposition X) ≪≫ (positive C).mapBiproduct _
  let eN : (negative C).obj Y ≅
      ⨁ fun a : Fin (S.length Y) => (negative C).obj (S.simpleObject (S.label Y a)) :=
    (negative C).mapIso (S.decomposition Y) ≪≫ (negative C).mapBiproduct _
  rw [finrank_hom_iso eP eN, finrank_biproduct_hom]
  simp_rw [finrank_hom_biproduct, finrank_positive_negative_simple S hC]
  rw [S.multiplicity_eq_sum X, S.multiplicity_eq_sum Y]
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul]
  simp only [eq_comm]

end Paper18.Category.Drinfeld
