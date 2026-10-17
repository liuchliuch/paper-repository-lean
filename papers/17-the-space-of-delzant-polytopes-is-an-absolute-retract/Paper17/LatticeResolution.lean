import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic

/-!
# Integer lattice steps in smooth fan resolution (Lemma 2.2)

These statements concern the actual integer generators. A nonunimodular
matrix produces an actual nonzero lattice point in its half-open fundamental
parallelepiped, and replacing a generator by such an integral vector has the
computed, strictly smaller multiplicity. Projective fan subdivision is a
separate geometric step and is not assumed as a certificate here.
-/
noncomputable section
open scoped BigOperators
namespace Paper17

/-- A nonunimodular square integral matrix does not span every lattice vector. -/
theorem exists_lattice_vector_outside {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (hdet : 1 < A.det.natAbs) :
    ∃ z : Fin n → ℤ, ∀ c : Fin n → ℤ, Matrix.vecMul c A ≠ z := by
  have hn : ¬ Function.Surjective (fun c => Matrix.vecMul c A) := by
    intro hs
    have hu : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp
      (Matrix.vecMul_surjective_iff_isUnit.mp hs)
    have hh := Int.isUnit_iff_natAbs_eq.mp hu
    omega
  simpa only [Function.Surjective, not_forall, not_exists] using hn

/-- The half-open fundamental parallelepiped contains a nonzero integer point
when the absolute determinant is greater than one. -/
theorem exists_nonzero_parallelepiped_point {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℤ) (hdet : 1 < A.det.natAbs) :
    ∃ z : Fin n → ℤ, z ≠ 0 ∧ ∃ a : Fin n → ℝ,
      (∀ i, 0 ≤ a i ∧ a i < 1) ∧
      (∀ j, (z j : ℝ) = ∑ i, a i * (A i j : ℝ)) := by
  obtain ⟨v, hv⟩ := exists_lattice_vector_outside A hdet
  let B : Matrix (Fin n) (Fin n) ℝ := A.map (fun z => (z : ℝ))
  have hd0 : A.det ≠ 0 := by
    intro hz
    simp [hz] at hdet
  have hBd0 : B.det ≠ 0 := by
    rw [show B.det = (A.det : ℝ) from (Int.cast_det A).symm]
    exact_mod_cast hd0
  have hBu : IsUnit B := (Matrix.isUnit_iff_isUnit_det B).mpr (isUnit_iff_ne_zero.mpr hBd0)
  obtain ⟨c, hc⟩ := Matrix.vecMul_surjective_iff_isUnit.mpr hBu (fun j => (v j : ℝ))
  let z : Fin n → ℤ := v - Matrix.vecMul (fun i => ⌊c i⌋) A
  refine ⟨z, ?_, fun i => Int.fract (c i),
    fun i => ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩, ?_⟩
  · intro hz
    apply hv (fun i => ⌊c i⌋)
    exact (sub_eq_zero.mp hz).symm
  · intro j
    have hcj : ∑ i, c i * (A i j : ℝ) = (v j : ℝ) := by
      simpa only [Matrix.vecMul, dotProduct, Matrix.map_apply, B] using congrFun hc j
    change ((v j - ∑ i, ⌊c i⌋ * A i j : ℤ) : ℝ) = _
    push_cast
    simp only [Int.fract, sub_mul, Finset.sum_sub_distrib]
    rw [hcj]

/-- Replacing one integer generator by a specified real combination gives the
actual determinant identity used in each affected stellar-subdivision cone. -/
theorem determinant_replace_generator {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℤ) (u : Fin n → ℤ) (b : Fin n → ℝ)
    (hcoord : ∀ j, (u j : ℝ) = ∑ i, b i * (A i j : ℝ)) (k : Fin n) :
    (((A.updateRow k u).det : ℤ) : ℝ) = b k * (A.det : ℝ) := by
  have hmap : (A.updateRow k u).map (fun z => (z : ℝ)) =
      (A.map (fun z => (z : ℝ))).updateRow k (fun j => (u j : ℝ)) := by
    ext i j
    by_cases hi : i = k <;> simp [Matrix.updateRow, Matrix.map_apply, Function.update_apply, hi]
  have hrow : (fun j => (u j : ℝ)) = ∑ i, b i • (A.map (fun z => (z : ℝ))) i := by
    ext j
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.map_apply] using hcoord j
  rw [Int.cast_det, hmap, hrow, Matrix.det_updateRow_sum, smul_eq_mul, ← Int.cast_det]

/-- Positive coefficients strictly below one give a strictly smaller positive
integer multiplicity, without any rounding or assumed determinant bound. -/
theorem multiplicity_strictly_decreases {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℤ) (u : Fin n → ℤ) (b : Fin n → ℝ)
    (hcoord : ∀ j, (u j : ℝ) = ∑ i, b i * (A i j : ℝ))
    (hdet : A.det ≠ 0) (k : Fin n) (hb0 : 0 < b k) (hb1 : b k < 1) :
    0 < (A.updateRow k u).det.natAbs ∧ (A.updateRow k u).det.natAbs < A.det.natAbs := by
  have heq := determinant_replace_generator A u b hcoord k
  have hd : 0 < |(A.det : ℝ)| := abs_pos.mpr (by exact_mod_cast hdet)
  have habs : |(((A.updateRow k u).det : ℤ) : ℝ)| = b k * |(A.det : ℝ)| := by
    rw [heq, abs_mul, abs_of_pos hb0]
  have hpos : 0 < |(((A.updateRow k u).det : ℤ) : ℝ)| := by rw [habs]; positivity
  have hlt : |(((A.updateRow k u).det : ℤ) : ℝ)| < |(A.det : ℝ)| := by
    rw [habs]
    exact mul_lt_of_lt_one_left hd hb1
  have hnatpos : (0 : ℝ) < ((A.updateRow k u).det.natAbs : ℝ) := by
    simpa only [Int.cast_natAbs, Int.cast_abs] using hpos
  have hnatlt : ((A.updateRow k u).det.natAbs : ℝ) < (A.det.natAbs : ℝ) := by
    simpa only [Int.cast_natAbs, Int.cast_abs] using hlt
  constructor
  · exact_mod_cast hnatpos
  · exact_mod_cast hnatlt

end Paper17
