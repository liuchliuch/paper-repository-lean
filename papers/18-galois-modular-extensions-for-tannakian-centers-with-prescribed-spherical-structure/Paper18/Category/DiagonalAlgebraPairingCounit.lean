import Paper18.Category.DiagonalAlgebraPairingBasic

/-! # The actual normalized central counit of a connected algebra -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped MonObj
universe v u w
namespace Paper18.Category.DiagonalAlgebra
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ C)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  (A : C) [MonObj A]
  (hA : Module.finrank ℂ (𝟙_ C ⟶ A) = 1)

include hA

/-- Connectedness and the actual monoid unit law force a nonzero unit. -/
lemma connected_one_ne_zero : η[A] ≠ 0 := by
  intro hz
  have hl : (λ_ A).hom = 0 := by
    rw [← MonObj.one_mul A, hz]
    simp
  have hi : 𝟙 A = 0 := by
    rw [← Iso.inv_hom_id (λ_ A), hl, comp_zero]
  obtain ⟨f, hf⟩ := Module.finrank_pos_iff_exists_ne_zero.mp
    (show 0 < Module.finrank ℂ (𝟙_ C ⟶ A) by rw [hA]; omega)
  exact hf (by rw [← comp_id f, hi, comp_zero])

include S

/-- The normalized actual central counit is an actual splitting of the unit. -/
def connectedCounit : A ⟶ 𝟙_ C := by
  letI : Mono η[A] := CategoryTheory.mono_of_nonzero_from_simple (connected_one_ne_zero A hA)
  exact (S.splitMono η[A]).retraction

@[reassoc (attr := simp)]
lemma one_connectedCounit : η[A] ≫ connectedCounit S A hA = 𝟙 _ := by
  letI : Mono η[A] := CategoryTheory.mono_of_nonzero_from_simple (connected_one_ne_zero A hA)
  exact (S.splitMono η[A]).id

/-- Every actual map from the unit is recovered from its scalar component
along the normalized connected counit. -/
lemma connectedCounit_resolution (f : 𝟙_ C ⟶ A) :
    (f ≫ connectedCounit S A hA) ≫ η[A] = f := by
  obtain ⟨c, rfl⟩ := exists_smul_eq_of_finrank_eq_one hA (connected_one_ne_zero A hA) f
  simp only [Linear.smul_comp, one_connectedCounit, id_comp]

/-- Vanishing of the central counit detects a map out of the unit. -/
lemma connectedCounit_detects_zero (f : 𝟙_ C ⟶ A)
    (h : f ≫ connectedCounit S A hA = 0) : f = 0 := by
  rw [← connectedCounit_resolution S A hA f, h, zero_comp]

end Paper18.Category.DiagonalAlgebra
