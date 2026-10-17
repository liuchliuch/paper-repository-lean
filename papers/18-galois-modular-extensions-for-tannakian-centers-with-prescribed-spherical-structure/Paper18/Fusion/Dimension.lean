import Paper18.Fusion.Basic
import Paper18.Results.PF

/-! Uniqueness of a positive normalized dimension character. -/
noncomputable section
open Classical
open scoped BigOperators
universe u
namespace Paper18
namespace FusionBasis

/-- A nonzero tensor product has at least one simple constituent. -/
lemma exists_constituent {ι : Type u} [Fintype ι] (B : FusionBasis ι) (x y : ι) :
    ∃ z, 0 < B.N x y z := by
  by_contra! h
  have hz : ∀ z, B.N x y z = 0 := fun z => Nat.eq_zero_of_le_zero (h z)
  have he := B.fpdim_mul x y
  simp only [hz, Nat.cast_zero, zero_mul, Finset.sum_const_zero] at he
  have := mul_pos (B.fpdim_pos x) (B.fpdim_pos y)
  linarith

/-- Every pair of simples is connected by left multiplication by a simple. -/
lemma exists_left_multiplier {ι : Type u} [Fintype ι] (B : FusionBasis ι) (i j : ι) :
    ∃ s, 0 < B.N s j i := by
  obtain ⟨s, hs⟩ := B.exists_constituent i (B.dual j)
  exact ⟨s, by rwa [B.N_right]⟩

/-- A positive normalized dimension character of the fusion multiplicities. -/
structure PositiveDimension {ι : Type u} [Fintype ι] (B : FusionBasis ι) where
  dim : ι → ℝ
  pos : ∀ x, 0 < dim x
  unit : dim B.one = 1
  tensor : ∀ x y, ∑ z, (B.N x y z : ℝ) * dim z = dim x * dim y

/-- The sum of all left fusion matrices. -/
def dimensionMatrix {ι : Type u} [Fintype ι] (B : FusionBasis ι) : Matrix ι ι ℝ :=
  fun i j => ∑ x, (B.N x i j : ℝ)

lemma dimensionMatrix_pos {ι : Type u} [Fintype ι] (B : FusionBasis ι) (i j : ι) :
    0 < B.dimensionMatrix i j := by
  obtain ⟨x, hx⟩ := B.exists_left_multiplier j i
  exact Finset.sum_pos' (fun _ _ => Nat.cast_nonneg _)
    ⟨x, Finset.mem_univ _, by exact_mod_cast hx⟩

lemma dimensionMatrix_eigen {ι : Type u} [Fintype ι] (B : FusionBasis ι)
    (d : ι → ℝ) (hd : ∀ x y, ∑ z, (B.N x y z : ℝ) * d z = d x * d y) (i : ι) :
    ∑ j, B.dimensionMatrix i j * d j = (∑ x, d x) * d i := by
  simp only [dimensionMatrix, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [hd]

/-- The normalized positive dimension character equals the FP dimension.
No separate dimension-preservation hypothesis is needed for a tensor functor. -/
theorem PositiveDimension.eq_fpdim {ι : Type u} [Fintype ι]
    {B : FusionBasis ι} (d : PositiveDimension B) (x : ι) : d.dim x = B.fpdim x := by
  letI : Nonempty ι := ⟨B.one⟩
  have he1 := B.dimensionMatrix_eigen d.dim d.tensor
  have he2 := B.dimensionMatrix_eigen B.fpdim B.fpdim_mul
  have hlam : (∑ x, d.dim x) = ∑ x, B.fpdim x :=
    nonnegMatrix_positive_eigenvalue_unique B.dimensionMatrix _ _
      (fun i j => (B.dimensionMatrix_pos i j).le) d.dim B.fpdim
      d.pos B.fpdim_pos he1 he2
  rw [hlam] at he1
  obtain ⟨c, _, hc⟩ := posMatrix_positive_eigenspace_one_dim B.dimensionMatrix _
    B.dimensionMatrix_pos d.dim B.fpdim d.pos B.fpdim_pos he1 he2
  have hunit := hc B.one
  rw [d.unit, B.fpdim_one, mul_one] at hunit
  rw [hc x, ← hunit, one_mul]

end FusionBasis
end Paper18
