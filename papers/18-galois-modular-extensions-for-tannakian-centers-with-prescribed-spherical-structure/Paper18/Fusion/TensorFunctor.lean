import Paper18.Fusion.Dimension

/-! Multiplicity data of tensor functors. FP dimension preservation is a
proved consequence of the unit and tensor multiplicity laws. -/
noncomputable section
open Classical
open scoped BigOperators
universe u v
namespace Paper18

/-- A unital map of fusion multiplicities. -/
structure FusionRuleMap {ι : Type u} {κ : Type v} [Fintype ι] [Fintype κ]
    (U : FusionBasis ι) (V : FusionBasis κ) where
  imageCoeff : ι → κ → ℕ
  image_one : imageCoeff U.one V.one = 1 ∧ ∀ y, y ≠ V.one → imageCoeff U.one y = 0
  tensor_coeff : ∀ x x' y,
    ∑ z, U.N x x' z * imageCoeff z y =
      ∑ a, ∑ b, imageCoeff x a * imageCoeff x' b * V.N a b y

namespace FusionRuleMap
variable {ι : Type u} {κ : Type v} [Fintype ι] [Fintype κ]
  {U : FusionBasis ι} {V : FusionBasis κ} (F : FusionRuleMap U V)

/-- A strong tensor functor cannot send a simple object to zero: the unit
constituent of `x ⊗ x*` would otherwise disappear. -/
lemma image_nonzero (x : ι) : ∃ y, 0 < F.imageCoeff x y := by
  by_contra! h
  have hz : ∀ y, F.imageCoeff x y = 0 := fun y => Nat.eq_zero_of_le_zero (h y)
  have he := F.tensor_coeff x (U.dual x) V.one
  have hself : U.N x (U.dual x) U.one = 1 := by
    rw [U.N_dual, U.N_one_right]
    simp
  have hbound := Finset.single_le_sum
    (s := Finset.univ) (f := fun z => U.N x (U.dual x) z * F.imageCoeff z V.one)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ U.one)
  dsimp only at hbound
  rw [hself, F.image_one.1, mul_one] at hbound
  simp only [hz, zero_mul, Finset.sum_const_zero] at he
  omega

/-- Pull back the target dimension along the multiplicity map. -/
def mappedDim (x : ι) : ℝ := ∑ y, (F.imageCoeff x y : ℝ) * V.fpdim y

lemma mappedDim_pos (x : ι) : 0 < F.mappedDim x := by
  obtain ⟨y, hy⟩ := F.image_nonzero x
  exact Finset.sum_pos' (fun z _ => mul_nonneg (Nat.cast_nonneg _) (V.fpdim_pos z).le)
    ⟨y, Finset.mem_univ _, mul_pos (by exact_mod_cast hy) (V.fpdim_pos y)⟩

lemma mappedDim_one : F.mappedDim U.one = 1 := by
  unfold mappedDim
  rw [Finset.sum_eq_single V.one]
  · simp [F.image_one.1]
  · intro y _ hy
    simp [F.image_one.2 y hy]
  · simp

lemma tensor_coeff_real (x x' : ι) (y : κ) :
    ∑ z, (U.N x x' z : ℝ) * (F.imageCoeff z y : ℝ) =
      ∑ a, ∑ b, (F.imageCoeff x a : ℝ) * (F.imageCoeff x' b : ℝ) * (V.N a b y : ℝ) := by
  exact_mod_cast F.tensor_coeff x x' y

lemma mappedDim_tensor (x x' : ι) :
    ∑ z, (U.N x x' z : ℝ) * F.mappedDim z = F.mappedDim x * F.mappedDim x' := by
  calc
    _ = ∑ y, (∑ z, (U.N x x' z : ℝ) * (F.imageCoeff z y : ℝ)) * V.fpdim y := by
      simp only [mappedDim, Finset.mul_sum, Finset.sum_mul, mul_assoc]
      rw [Finset.sum_comm]
    _ = ∑ y, (∑ a, ∑ b,
        (F.imageCoeff x a : ℝ) * (F.imageCoeff x' b : ℝ) * (V.N a b y : ℝ)) *
        V.fpdim y := by simp_rw [F.tensor_coeff_real]
    _ = ∑ a, ∑ b, ((F.imageCoeff x a : ℝ) * (F.imageCoeff x' b : ℝ)) *
        (∑ y, (V.N a b y : ℝ) * V.fpdim y) := by
      simp only [Finset.sum_mul, Finset.mul_sum, mul_assoc]
      rw [Finset.sum_comm]
      congr 1; ext a
      rw [Finset.sum_comm]
    _ = ∑ a, ∑ b, ((F.imageCoeff x a : ℝ) * (F.imageCoeff x' b : ℝ)) *
        (V.fpdim a * V.fpdim b) := by simp_rw [V.fpdim_mul]
    _ = _ := by
      simp only [mappedDim, Fintype.sum_mul_sum]
      apply Finset.sum_congr rfl; intro a _
      apply Finset.sum_congr rfl; intro b _
      ring

/-- FP dimensions are preserved by any unital tensor multiplicity map.
This follows from uniqueness of the positive normalized dimension character. -/
theorem fpdim_preserved (x : ι) :
    ∑ y, (F.imageCoeff x y : ℝ) * V.fpdim y = U.fpdim x :=
  (FusionBasis.PositiveDimension.mk F.mappedDim F.mappedDim_pos
    F.mappedDim_one F.mappedDim_tensor).eq_fpdim x

end FusionRuleMap

/-- A dominant unital map of fusion multiplicities. -/
structure FusionMap {ι : Type u} {κ : Type v} [Fintype ι] [Fintype κ]
    (U : FusionBasis ι) (V : FusionBasis κ) extends FusionRuleMap U V where
  dominant : ∀ y : κ, ∃ x : ι, 0 < imageCoeff x y

namespace FusionMap
variable {ι : Type u} {κ : Type v} [Fintype ι] [Fintype κ]
  {U : FusionBasis ι} {V : FusionBasis κ} (F : FusionMap U V)

/-- Dimension preservation is derived, not a field of a dominant map. -/
theorem fpdim_preserved (x : ι) :
    ∑ y, (F.imageCoeff x y : ℝ) * V.fpdim y = U.fpdim x :=
  F.toFusionRuleMap.fpdim_preserved x

end FusionMap

/-- The orbit/stabilizer dimension description of an equivariantization.
Construction from an actual group action is handled at the category level. -/
structure EquivariantDimensionModel {ι : Type u} {κ : Type v} [Fintype ι] [Fintype κ]
    (C : FusionBasis ι) (E : FusionBasis κ) where
  forget : FusionMap E C
  underlying : κ → ι
  orbitIndex : κ → ℕ
  representationDim : κ → ℕ
  dimension_formula : ∀ x, E.fpdim x =
    C.fpdim (underlying x) * (orbitIndex x * representationDim x : ℕ)

end Paper18
