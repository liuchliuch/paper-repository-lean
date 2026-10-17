import Paper18.Category.FunctorImage
import Paper18.Category.PivotalDimension

/-!
# Actual tensor invertibility and its action on simple objects

An inverse is an actual object with actual isomorphisms to the tensor unit.
Tensoring is proved to be an equivalence; no permutation or simplicity law is
included in the definition.
-/
noncomputable section
open Classical
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped BigOperators
universe v u w
namespace Paper18.Category
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- An actual two-sided inverse for an object of a monoidal category. -/
structure TensorInverse (X : C) where
  inverse : C
  left : inverse ⊗ X ≅ 𝟙_ C
  right : X ⊗ inverse ≅ 𝟙_ C

/-- Tensor invertibility is existence of actual inverse data. -/
def IsTensorInvertible (X : C) : Prop := Nonempty (TensorInverse X)

namespace TensorInverse
variable {X : C} (A : TensorInverse X)

/-- The same actual isomorphisms exhibit the inverse as invertible. -/
def symm : TensorInverse A.inverse := ⟨X, A.right, A.left⟩

/-- Actual inverse data produces an actual autoequivalence by left tensoring.
The standard equivalence constructor proves the triangle law by adjointification. -/
def tensorLeftEquivalence : C ≌ C :=
  CategoryTheory.Equivalence.mk (tensorLeft X) (tensorLeft A.inverse)
    ((leftUnitorNatIso C).symm ≪≫ (tensoringLeft C).mapIso A.left.symm ≪≫
      tensorLeftTensor A.inverse X)
    ((tensorLeftTensor X A.inverse).symm ≪≫ (tensoringLeft C).mapIso A.right ≪≫
      leftUnitorNatIso C)

def tensorLeftIsEquivalence (A : TensorInverse X) : (tensorLeft X).IsEquivalence := by
  exact inferInstanceAs A.tensorLeftEquivalence.functor.IsEquivalence

variable [Preadditive C] [Linear ℂ C] [HasKernels C] [HasFiniteBiproducts C]
  [∀ Y Z : C, FiniteDimensional ℂ (Y ⟶ Z)]
  [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)

include S A in
/-- Left tensoring with an actual invertible object preserves categorical simplicity. -/
lemma simple_tensor (Y : C) [Simple Y] : Simple (X ⊗ Y) := by
  letI := A.tensorLeftIsEquivalence
  exact S.simple_map (tensorLeft X) Y

include S A in
/-- Every actual invertible object is simple when the tensor unit is simple. -/
lemma simple [Simple (𝟙_ C)] : Simple X := by
  letI := A.simple_tensor S (𝟙_ C)
  exact Simple.of_iso (ρ_ X).symm

/-- Tensoring with an actual invertible object acts by a genuine permutation
of the complete set of actual simple representatives. -/
def simplePermutation : ι ≃ ι := by
  letI := A.tensorLeftIsEquivalence
  let f := S.simpleImageLabel S (tensorLeft X)
  have hi : Function.Injective f := S.simpleImageLabel_injective S (tensorLeft X)
  exact Equiv.ofBijective f ⟨hi, Finite.surjective_of_injective hi⟩

/-- The permutation is witnessed by actual tensor-product isomorphisms. -/
def simplePermutationIso (i : ι) : X ⊗ S.simpleObject i ≅ S.simpleObject (A.simplePermutation S i) := by
  letI := A.tensorLeftIsEquivalence
  exact S.simpleImageIso S (tensorLeft X) i

end TensorInverse

namespace IsTensorInvertible
lemma of_iso {X Y : C} (e : X ≅ Y) (hY : IsTensorInvertible Y) : IsTensorInvertible X := by
  obtain ⟨A⟩ := hY
  exact ⟨⟨A.inverse, (Iso.refl _ ⊗ᵢ e) ≪≫ A.left,
    (e ⊗ᵢ Iso.refl _) ≪≫ A.right⟩⟩

lemma unit : IsTensorInvertible (𝟙_ C) :=
  ⟨⟨𝟙_ C, λ_ (𝟙_ C), ρ_ (𝟙_ C)⟩⟩

lemma tensor {X Y : C} (hX : IsTensorInvertible X) (hY : IsTensorInvertible Y) :
    IsTensorInvertible (X ⊗ Y) := by
  obtain ⟨A⟩ := hX
  obtain ⟨B⟩ := hY
  refine ⟨⟨B.inverse ⊗ A.inverse, ?_, ?_⟩⟩
  · exact (α_ B.inverse A.inverse (X ⊗ Y)) ≪≫
      (Iso.refl _ ⊗ᵢ ((α_ A.inverse X Y).symm ≪≫
        (A.left ⊗ᵢ Iso.refl Y) ≪≫ λ_ Y)) ≪≫ B.left
  · exact (α_ X Y (B.inverse ⊗ A.inverse)) ≪≫
      (Iso.refl _ ⊗ᵢ ((α_ Y B.inverse A.inverse).symm ≪≫
        (B.right ⊗ᵢ Iso.refl _) ≪≫ λ_ A.inverse)) ≪≫ A.right
end IsTensorInvertible

namespace FiniteSemisimpleSkeleton
attribute [local instance 2000] RightRigidCategory.rightDual
variable [Preadditive C] [Linear ℂ C] [HasKernels C] [HasFiniteBiproducts C]
  [∀ Y Z : C, FiniteDimensional ℂ (Y ⟶ Z)]
  [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [RightRigidCategory C] [Simple (𝟙_ C)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)

/-- Every actual simple has FP dimension at least one, by the unit
constituent of its product with its dual. -/
lemma fpdim_simple_ge_one (X : C) [Simple X] : 1 ≤ S.fpdim X := by
  obtain ⟨i, ⟨e⟩⟩ := S.simple_isomorphic_representative X
  rw [S.fpdim_iso e, S.fpdim_simple]
  have hu : S.fusionBasis.N i (S.fusionBasis.dual i) S.fusionBasis.one = 1 := by
    rw [S.fusionBasis.N_right, S.fusionBasis.dual_involutive,
      S.fusionBasis.N_one_left]
    simp
  have ht := Finset.single_le_sum
    (s := Finset.univ) (f := fun k =>
      (S.fusionBasis.N i (S.fusionBasis.dual i) k : ℝ) * S.fusionBasis.fpdim k)
    (fun k _ => mul_nonneg (Nat.cast_nonneg _) (S.fusionBasis.fpdim_pos k).le)
    (Finset.mem_univ S.fusionBasis.one)
  dsimp only at ht
  rw [hu, Nat.cast_one, S.fusionBasis.fpdim_one, one_mul,
    S.fusionBasis.fpdim_mul, S.fusionBasis.fpdim_dual] at ht
  have hp := S.fusionBasis.fpdim_pos i
  nlinarith

/-- Actual tensor invertibility forces FP dimension one. -/
lemma fpdim_eq_one_of_tensorInvertible {X : C} (h : IsTensorInvertible X) : S.fpdim X = 1 := by
  obtain ⟨A⟩ := h
  letI := A.simple S
  letI := A.symm.simple S
  have hx := S.fpdim_simple_ge_one X
  have hy := S.fpdim_simple_ge_one A.inverse
  have hm : S.fpdim X * S.fpdim A.inverse = 1 := by
    rw [← S.fpdim_tensor, S.fpdim_iso A.right, S.fpdim_unit]
  nlinarith

/-- A unit summand exhausts an object of FP dimension one. The proof uses
actual Hom multiplicities, their positivity, and the semisimple End criterion. -/
def isoUnitOfFpdimEqOne (Y : C) (hY : S.fpdim Y = 1)
    (hu : S.multiplicity Y S.unitLabel = 1) : Y ≅ 𝟙_ C := by
  have hd : S.fusionBasis.fpdim S.unitLabel = 1 := S.fusionBasis.fpdim_one
  let f := fun k => (S.multiplicity Y k : ℝ) * S.fusionBasis.fpdim k
  have hp (k : ι) : 0 ≤ f k :=
    mul_nonneg (Nat.cast_nonneg _) (S.fusionBasis.fpdim_pos k).le
  have hfu : f S.unitLabel = 1 := by simp only [f, hu, Nat.cast_one, hd, one_mul]
  have hz : ∑ k ∈ Finset.univ.erase S.unitLabel, f k = 0 := by
    have he := Finset.sum_erase_add Finset.univ f (Finset.mem_univ S.unitLabel)
    change (∑ k, f k) = 1 at hY
    rw [← he, hfu] at hY
    linarith
  have hm (k : ι) : S.multiplicity Y k = if k = S.unitLabel then 1 else 0 := by
    split_ifs with hk
    · simpa only [hk] using hu
    · have hk' : k ∈ Finset.univ.erase S.unitLabel := Finset.mem_erase.mpr ⟨hk, Finset.mem_univ _⟩
      have hle := Finset.single_le_sum (fun i _ => hp i) hk'
      rw [hz] at hle
      have hzero : f k = 0 := le_antisymm hle (hp k)
      have hmul : (S.multiplicity Y k : ℝ) = 0 :=
        (mul_eq_zero.mp hzero).resolve_right (ne_of_gt (S.fusionBasis.fpdim_pos k))
      exact_mod_cast hmul
  letI : Simple Y := S.simple_of_finrank_end_eq_one Y (by
    rw [S.finrank_hom_eq_sum]
    simp [hm])
  let r := S.retractOfMultiplicityPos Y S.unitLabel (by omega)
  have hi : r.i ≠ 0 := by
    intro h
    exact CategoryTheory.id_nonzero (S.simpleObject S.unitLabel) (by
      rw [← r.retract, h, zero_comp])
  letI := CategoryTheory.isIso_of_hom_simple hi
  exact (asIso r.i).symm ≪≫ S.unitIso

/-- FP dimension one produces an actual two-sided tensor inverse for each
actual simple representative. -/
def tensorInverseOfFpdimEqOne (i : ι) (h : S.fusionBasis.fpdim i = 1) :
    TensorInverse (S.simpleObject i) := by
  have hd : S.fusionBasis.fpdim (S.dualLabel i) = 1 := by
    rw [← S.fusionBasis_dual, S.fusionBasis.fpdim_dual, h]
  have hm (j : ι) : S.fusionCoeff j (S.dualLabel j) S.unitLabel = 1 := by
    rw [S.fusionCoeff_right, S.dualLabel_involutive,
      S.fusionCoeff_one_left S.unitLabel S.unitIso]
    simp
  refine ⟨S.simpleObject (S.dualLabel i), ?_, ?_⟩
  · apply S.isoUnitOfFpdimEqOne
    · rw [S.fpdim_tensor, S.fpdim_simple, S.fpdim_simple, h, hd, one_mul]
    · have ht := hm (S.dualLabel i)
      simpa only [S.dualLabel_involutive] using ht
  · apply S.isoUnitOfFpdimEqOne
    · rw [S.fpdim_tensor, S.fpdim_simple, S.fpdim_simple, h, hd, one_mul]
    · exact hm i

/-- The numerical FP-dimension-one criterion is equivalent to actual
tensor invertibility, with an inverse object constructed in the reverse direction. -/
lemma tensorInvertible_iff_fpdim_eq_one (X : C) [Simple X] :
    IsTensorInvertible X ↔ S.fpdim X = 1 := by
  constructor
  · exact S.fpdim_eq_one_of_tensorInvertible
  · intro h
    obtain ⟨i, ⟨e⟩⟩ := S.simple_isomorphic_representative X
    have hi : S.fusionBasis.fpdim i = 1 := by
      rw [S.fpdim_iso e, S.fpdim_simple] at h
      exact h
    exact IsTensorInvertible.of_iso e ⟨S.tensorInverseOfFpdimEqOne i hi⟩

end FiniteSemisimpleSkeleton
end Paper18.Category
