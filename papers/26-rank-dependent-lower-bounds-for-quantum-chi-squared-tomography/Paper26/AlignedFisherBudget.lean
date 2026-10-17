import Paper26.ContinuousPOVM
import Paper26.MatrixCoordinates
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add

/-!
# Native single-copy Fisher budget at the aligned flat state

The effects are actual positive semidefinite complex matrices. The derivatives
are the Born directional derivatives of the canonical off-diagonal density
matrix tangent. All cross-block and zero-probability bounds are proved from
positive semidefiniteness. The final integration permits an arbitrary measurable
outcome space. No coordinate pullback or adaptive-chain conclusion is asserted.
-/

noncomputable section
open scoped BigOperators Matrix ComplexOrder ENNReal
open MeasureTheory Paper26.QuantumModel Paper26.ContinuousPOVM

namespace Paper26.AlignedFisherBudget

variable {κ σ : Type*} [Fintype κ] [DecidableEq κ] [Fintype σ] [DecidableEq σ]

def headBlock (E : Matrix (κ ⊕ σ) (κ ⊕ σ) ℂ) : Matrix κ κ ℂ :=
  E.submatrix Sum.inl Sum.inl

def crossBlock (E : Matrix (κ ⊕ σ) (κ ⊕ σ) ℂ) : Matrix σ κ ℂ :=
  E.submatrix Sum.inr Sum.inl

def tailBlock (E : Matrix (κ ⊕ σ) (κ ⊕ σ) ℂ) : Matrix σ σ ℂ :=
  E.submatrix Sum.inr Sum.inr

def headTrace (E : Matrix (κ ⊕ σ) (κ ⊕ σ) ℂ) : ℝ := (headBlock E).trace.re

def tailTrace (E : Matrix (κ ⊕ σ) (κ ⊕ σ) ℂ) : ℝ := (tailBlock E).trace.re

/-- Native two-by-two PSD minor bound, valid also at zero diagonal entries. -/
theorem psd_entry_normSq_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : Matrix ι ι ℂ) (hE : E.PosSemidef) (i j : ι) :
    Complex.normSq (E i j) ≤ (E i i).re * (E j j).re := by
  let e : Fin 2 → ι := ![i, j]
  have hdet := (RCLike.nonneg_iff.mp (hE.submatrix e).det_nonneg).1
  rw [Matrix.det_fin_two] at hdet
  simp only [Matrix.submatrix_apply, e, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one] at hdet
  have hij : E j i = star (E i j) := by
    exact (congrFun (congrFun hE.isHermitian.eq j) i).symm
  rw [hij, ← hE.isHermitian.coe_re_apply_self i,
    ← hE.isHermitian.coe_re_apply_self j] at hdet
  simpa only [Complex.star_def, Complex.mul_conj, ← Complex.ofReal_mul,
    ← Complex.ofReal_sub, Complex.ofReal_re, RCLike.re_eq_complex_re, RCLike.ofReal_eq_complex_ofReal,
    sub_nonneg] using hdet

theorem psd_diagonal_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : Matrix ι ι ℂ) (hE : E.PosSemidef) (i : ι) : 0 ≤ (E i i).re := by
  simpa [← Pi.single_star, star_one] using hE.re_dotProduct_nonneg (Pi.single i 1)

theorem headTrace_nonneg (E : Matrix (κ ⊕ σ) (κ ⊕ σ) ℂ) (hE : E.PosSemidef) :
    0 ≤ headTrace E := by
  simp only [headTrace, Matrix.trace, Matrix.diag_apply, Complex.re_sum]
  exact Finset.sum_nonneg fun i _ => psd_diagonal_nonneg E hE (Sum.inl i)

theorem tailTrace_nonneg (E : Matrix (κ ⊕ σ) (κ ⊕ σ) ℂ) (hE : E.PosSemidef) :
    0 ≤ tailTrace E := by
  simp only [tailTrace, Matrix.trace, Matrix.diag_apply, Complex.re_sum]
  exact Finset.sum_nonneg fun i _ => psd_diagonal_nonneg E hE (Sum.inr i)

theorem cross_entry_bound (E : Matrix (κ ⊕ σ) (κ ⊕ σ) ℂ) (hE : E.PosSemidef)
    (i : σ) (j : κ) :
    Complex.normSq (crossBlock E i j) ≤ (headBlock E j j).re * (tailBlock E i i).re := by
  simpa only [crossBlock, headBlock, tailBlock, Matrix.submatrix_apply, mul_comm] using
    psd_entry_normSq_le E hE (Sum.inr i) (Sum.inl j)

/-- The complete off-diagonal block, with all entries retained. -/
theorem cross_frobenius_le (E : Matrix (κ ⊕ σ) (κ ⊕ σ) ℂ) (hE : E.PosSemidef) :
    ShellAccounting.frobeniusSq (crossBlock E) ≤ headTrace E * tailTrace E := by
  unfold ShellAccounting.frobeniusSq
  simp only [Complex.sq_norm]
  calc
    _ ≤ ∑ i, ∑ j, (headBlock E j j).re * (tailBlock E i i).re :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => cross_entry_bound E hE i j
    _ = _ := by
      simp only [headTrace, tailTrace, Matrix.trace, Matrix.diag_apply, Complex.re_sum,
        Finset.sum_mul, Finset.mul_sum]

theorem cross_eq_zero_of_headTrace_zero (E : Matrix (κ ⊕ σ) (κ ⊕ σ) ℂ)
    (hE : E.PosSemidef) (h0 : headTrace E = 0) : crossBlock E = 0 := by
  have hF : ShellAccounting.frobeniusSq (crossBlock E) = 0 :=
    le_antisymm (by simpa only [h0, zero_mul] using cross_frobenius_le E hE)
      (ShellAccounting.frobeniusSq_nonneg _)
  unfold ShellAccounting.frobeniusSq at hF
  have hrows := (Finset.sum_eq_zero_iff_of_nonneg
    (fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg ‖crossBlock E i j‖)).1 hF
  ext i j
  have hj := (Finset.sum_eq_zero_iff_of_nonneg
    (fun j _ => sq_nonneg ‖crossBlock E i j‖)).1 (hrows i (Finset.mem_univ i)) j (Finset.mem_univ j)
  exact norm_eq_zero.1 (sq_eq_zero_iff.1 hj)

/-- Canonical source and complementary column embeddings. -/
def sourceColumns : Matrix (κ ⊕ σ) κ ℂ := Matrix.fromRows 1 0

def complementColumns : Matrix (κ ⊕ σ) σ ℂ := Matrix.fromRows 0 1

/-- The actual density tangent `(V K U† + U K† V†)/r`. -/
def tangent (K : Matrix σ κ ℂ) : Matrix (κ ⊕ σ) (κ ⊕ σ) ℂ :=
  ((Fintype.card κ : ℝ)⁻¹) •
    (complementColumns * K * sourceColumnsᴴ + sourceColumns * Kᴴ * complementColumnsᴴ)

theorem tangent_blocks (K : Matrix σ κ ℂ) :
    tangent K = ((Fintype.card κ : ℝ)⁻¹) • Matrix.fromBlocks 0 Kᴴ K 0 := by
  simp only [tangent, sourceColumns, complementColumns,
    Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose,
    Matrix.conjTranspose_one, Matrix.conjTranspose_zero, Matrix.fromRows_mul,
    Matrix.one_mul, Matrix.zero_mul]
  congr 1
  ext i j
  cases i <;> cases j <;> simp

/-- Directional derivative of the actual Born trace along a density tangent. -/
def directionalDerivative (E : Matrix (κ ⊕ σ) (κ ⊕ σ) ℂ) (K : Matrix σ κ ℂ) : ℝ :=
  (Matrix.trace (tangent K * E)).re

def direction (i : σ) (j : κ) (c : Fin 2) : Matrix σ κ ℂ :=
  Matrix.single i j (if c = 0 then 1 else Complex.I)

def coordinateDerivative (E : Matrix (κ ⊕ σ) (κ ⊕ σ) ℂ)
    (i : σ) (j : κ) (c : Fin 2) : ℝ := directionalDerivative E (direction i j c)

theorem tangent_single (i : σ) (j : κ) (z : ℂ) :
    tangent (Matrix.single i j z) = ((Fintype.card κ : ℝ)⁻¹) •
      (Matrix.single (Sum.inr i) (Sum.inl j) z +
        Matrix.single (Sum.inl j) (Sum.inr i) (star z)) := by
  rw [tangent_blocks]
  congr 1
  ext a b
  cases a <;> cases b <;> simp [Matrix.single, apply_ite] <;> split_ifs <;> simp_all
  all_goals aesop

theorem directionalDerivative_single (E : Matrix (κ ⊕ σ) (κ ⊕ σ) ℂ)
    (i : σ) (j : κ) (z : ℂ) :
    directionalDerivative E (Matrix.single i j z) =
      ((Fintype.card κ : ℝ)⁻¹) *
        (z * E (Sum.inl j) (Sum.inr i) + star z * E (Sum.inr i) (Sum.inl j)).re := by
  rw [directionalDerivative, tangent_single, Matrix.smul_mul, Matrix.trace_smul,
    Matrix.add_mul, Matrix.trace_add, Matrix.trace_single_mul, Matrix.trace_single_mul]
  simp only [Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, smul_eq_mul]

theorem coordinateDerivative_real (E : Matrix (κ ⊕ σ) (κ ⊕ σ) ℂ)
    (hE : E.IsHermitian) (i : σ) (j : κ) :
    coordinateDerivative E i j 0 = 2 * (crossBlock E i j).re / (Fintype.card κ : ℝ) := by
  have h : E (Sum.inl j) (Sum.inr i) = star (E (Sum.inr i) (Sum.inl j)) :=
    (congrFun (congrFun hE.eq (Sum.inl j)) (Sum.inr i)).symm
  simp [coordinateDerivative, direction, directionalDerivative_single, h,
    crossBlock]
  ring

theorem coordinateDerivative_imag (E : Matrix (κ ⊕ σ) (κ ⊕ σ) ℂ)
    (hE : E.IsHermitian) (i : σ) (j : κ) :
    coordinateDerivative E i j 1 = 2 * (crossBlock E i j).im / (Fintype.card κ : ℝ) := by
  have h : E (Sum.inl j) (Sum.inr i) = star (E (Sum.inr i) (Sum.inl j)) :=
    (congrFun (congrFun hE.eq (Sum.inl j)) (Sum.inr i)).symm
  simp only [coordinateDerivative, direction]
  norm_num only [show (1 : Fin 2) ≠ 0 by decide, if_false]
  rw [directionalDerivative_single, h]
  simp only [Complex.star_def, Complex.conj_I, Complex.mul_re,
    Complex.I_re, Complex.I_im, Complex.conj_re, Complex.conj_im, Complex.neg_re,
    Complex.neg_im, Complex.add_re]
  change _ = 2 * (E (Sum.inr i) (Sum.inl j)).im / _
  ring

/-- The tagged directions are exactly the inverse actual real/imaginary
entry-coordinate basis, rather than a surrogate parameter encoding. -/
theorem direction_eq_entryCoordinate (r s : ℕ) (i : Fin s) (j : Fin r) (c : Fin 2) :
    direction i j c = (MatrixCoordinates.entryCoordinates r s).symm
      (Pi.single (i, j, c) 1) := by
  ext a b
  fin_cases c <;>
    simp [direction, Matrix.single, MatrixCoordinates.entryCoordinates_symm_entry,
      Pi.single_apply, eq_comm, and_comm] <;> split_ifs <;> simp

def derivativeNormSq (E : Matrix (κ ⊕ σ) (κ ⊕ σ) ℂ) : ℝ :=
  ∑ i, ∑ j, ∑ c : Fin 2, (coordinateDerivative E i j c) ^ 2

theorem derivativeNormSq_eq (E : Matrix (κ ⊕ σ) (κ ⊕ σ) ℂ) (hE : E.IsHermitian) :
    derivativeNormSq E = 4 * ShellAccounting.frobeniusSq (crossBlock E) /
      (Fintype.card κ : ℝ) ^ 2 := by
  simp only [derivativeNormSq, Fin.sum_univ_two, coordinateDerivative_real E hE,
    coordinateDerivative_imag E hE, ShellAccounting.frobeniusSq, Complex.sq_norm,
    Complex.normSq_apply, Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The Born probability density at the aligned rank-`r` flat state. -/
def probability (E : Matrix (κ ⊕ σ) (κ ⊕ σ) ℂ) : ℝ :=
  headTrace E / (Fintype.card κ : ℝ)

/-- The actual Fisher trace contribution, with the zero-probability
convention made explicit. -/
def perEffectFisher (E : Matrix (κ ⊕ σ) (κ ⊕ σ) ℂ) : ℝ :=
  if probability E = 0 then 0 else derivativeNormSq E / probability E

theorem probability_nonneg (E : Matrix (κ ⊕ σ) (κ ⊕ σ) ℂ) (hE : E.PosSemidef) :
    0 ≤ probability E := div_nonneg (headTrace_nonneg E hE) (Nat.cast_nonneg _)

theorem derivativeNormSq_nonneg (E : Matrix (κ ⊕ σ) (κ ⊕ σ) ℂ) :
    0 ≤ derivativeNormSq E := by
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
    Finset.sum_nonneg fun c _ => sq_nonneg _

theorem probability_zero_derivative_zero [Nonempty κ]
    (E : Matrix (κ ⊕ σ) (κ ⊕ σ) ℂ) (hE : E.PosSemidef) (h0 : probability E = 0) :
    derivativeNormSq E = 0 := by
  have hr : (Fintype.card κ : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have ha : headTrace E = 0 := (div_eq_zero_iff.mp h0).resolve_right hr
  rw [derivativeNormSq_eq E hE.isHermitian, cross_eq_zero_of_headTrace_zero E hE ha]
  simp [ShellAccounting.frobeniusSq]

theorem perEffectFisher_nonneg (E : Matrix (κ ⊕ σ) (κ ⊕ σ) ℂ)
    (hE : E.PosSemidef) : 0 ≤ perEffectFisher E := by
  unfold perEffectFisher
  split_ifs
  · exact le_rfl
  · exact div_nonneg (derivativeNormSq_nonneg E) (probability_nonneg E hE)

/-- Single-effect Fisher budget, proved solely from PSD and the actual
directional derivatives. -/
theorem perEffectFisher_le [Nonempty κ]
    (E : Matrix (κ ⊕ σ) (κ ⊕ σ) ℂ) (hE : E.PosSemidef) :
    perEffectFisher E ≤ 4 * tailTrace E / (Fintype.card κ : ℝ) := by
  have hr : (0 : ℝ) < Fintype.card κ := by exact_mod_cast Fintype.card_pos
  unfold perEffectFisher
  split_ifs with hp
  · exact div_nonneg (mul_nonneg (by norm_num) (tailTrace_nonneg E hE)) hr.le
  · have hp0 : 0 < probability E := lt_of_le_of_ne (probability_nonneg E hE) (Ne.symm hp)
    have ha : headTrace E ≠ 0 := by intro h; apply hp; simp [probability, h]
    rw [derivativeNormSq_eq E hE.isHermitian]
    calc
      _ ≤ (4 * (headTrace E * tailTrace E) / (Fintype.card κ : ℝ) ^ 2) / probability E :=
        div_le_div_of_nonneg_right
          (div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left (cross_frobenius_le E hE) (by norm_num))
            (sq_nonneg _)) hp0.le
      _ = _ := by unfold probability; field_simp

theorem canonical_probability_matrix [Nonempty κ]
    (E : Matrix (κ ⊕ σ) (κ ⊕ σ) ℂ) :
    (Matrix.trace ((GraphFamily.density (0 : Matrix σ κ ℂ)).matrix * E)).re =
      probability E := by
  rw [GraphFamily.density_matrix, GraphFamily.projectorMatrix_blocks]
  simp only [GraphFamily.metric, Matrix.conjTranspose_zero, Matrix.mul_zero,
    add_zero, inv_one, Matrix.zero_mul,
    Matrix.smul_mul, Matrix.trace_smul]
  simp [Matrix.trace, Matrix.mul_apply, Matrix.one_apply, Fintype.sum_sum_type, probability,
    headTrace, headBlock, Complex.real_smul, div_eq_mul_inv, mul_comm]

/-- The Born trace on the actual affine tangent path is affine with
exactly the derivative used in the Fisher sum. -/
theorem born_tangent_affine [Nonempty κ]
    (E : Matrix (κ ⊕ σ) (κ ⊕ σ) ℂ) (K : Matrix σ κ ℂ) (t : ℝ) :
    (Matrix.trace (((GraphFamily.density (0 : Matrix σ κ ℂ)).matrix + t • tangent K) * E)).re =
      probability E + t * directionalDerivative E K := by
  rw [Matrix.add_mul, Matrix.trace_add, Complex.add_re, canonical_probability_matrix,
    Matrix.smul_mul, Matrix.trace_smul]
  simp only [directionalDerivative, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]

/-- A genuine real directional derivative of the actual Born matrix trace. -/
theorem hasDerivAt_born_tangent [Nonempty κ]
    (E : Matrix (κ ⊕ σ) (κ ⊕ σ) ℂ) (K : Matrix σ κ ℂ) (t : ℝ) :
    HasDerivAt (fun u : ℝ =>
      (Matrix.trace (((GraphFamily.density (0 : Matrix σ κ ℂ)).matrix + u • tangent K) * E)).re)
      (directionalDerivative E K) t := by
  simp_rw [born_tangent_affine]
  simpa only [zero_add, one_mul] using
    (hasDerivAt_const t (probability E)).add ((hasDerivAt_id t).mul_const (directionalDerivative E K))

section ArbitraryOutcomes
variable {Ω : Type*} [MeasurableSpace Ω]
variable (M : DominatedPOVM (κ ⊕ σ) Ω)

theorem probability_eq_born [Nonempty κ] (y : Ω) :
    probability (M.effect y) = M.born (GraphFamily.density (0 : Matrix σ κ ℂ)) y :=
  (canonical_probability_matrix (M.effect y)).symm

theorem measurable_directionalDerivative (K : Matrix σ κ ℂ) :
    Measurable (fun y => directionalDerivative (M.effect y) K) := by
  unfold directionalDerivative Matrix.trace
  simp only [Matrix.diag_apply, Matrix.mul_apply]
  have hc := Finset.measurable_sum Finset.univ fun i _ =>
    Finset.measurable_sum Finset.univ fun j _ =>
      (M.entry_measurable j i).const_mul (tangent K i j)
  exact Complex.continuous_re.measurable.comp hc

theorem measurable_probability : Measurable (fun y => probability (M.effect y)) := by
  unfold probability headTrace Matrix.trace
  simp only [Matrix.diag_apply, headBlock, Matrix.submatrix_apply, Complex.re_sum]
  exact (Finset.measurable_sum Finset.univ fun i _ =>
    (M.entry_measurable (Sum.inl i) (Sum.inl i)).re).div_const _

theorem measurable_perEffectFisher : Measurable (fun y => perEffectFisher (M.effect y)) := by
  have hd : Measurable (fun y => derivativeNormSq (M.effect y)) :=
    Finset.measurable_sum Finset.univ fun i _ =>
      Finset.measurable_sum Finset.univ fun j _ =>
        Finset.measurable_sum Finset.univ fun c _ =>
          (measurable_directionalDerivative M (direction i j c)).pow_const 2
  exact Measurable.ite (measurableSet_eq_fun (measurable_probability M) measurable_const)
    measurable_const (hd.div (measurable_probability M))

theorem integrable_tailTrace : Integrable (fun y => tailTrace (M.effect y)) M.reference := by
  unfold tailTrace Matrix.trace
  simp only [Matrix.diag_apply, tailBlock, Matrix.submatrix_apply, Complex.re_sum]
  exact integrable_finset_sum Finset.univ fun i _ =>
    (M.entry_integrable (Sum.inr i) (Sum.inr i)).re

theorem integral_tailTrace : ∫ y, tailTrace (M.effect y) ∂M.reference = (Fintype.card σ : ℝ) := by
  unfold tailTrace Matrix.trace
  simp only [Matrix.diag_apply, tailBlock, Matrix.submatrix_apply, Complex.re_sum]
  rw [integral_finset_sum Finset.univ (fun i _ =>
    show Integrable (fun y => (M.effect y (Sum.inr i) (Sum.inr i)).re) M.reference from
      (M.entry_integrable (Sum.inr i) (Sum.inr i)).re)]
  have h (i : σ) : ∫ y, (M.effect y (Sum.inr i) (Sum.inr i)).re ∂M.reference = 1 := by
    have hi := integral_re (M.entry_integrable (Sum.inr i) (Sum.inr i))
    simp only [RCLike.re_eq_complex_re] at hi
    rw [hi, M.total]
    simp
  simp_rw [h]
  simp

theorem integrable_perEffectFisher [Nonempty κ] :
    Integrable (fun y => perEffectFisher (M.effect y)) M.reference := by
  apply (((integrable_tailTrace M).const_mul 4).div_const (Fintype.card κ : ℝ)).mono'
    (measurable_perEffectFisher M).aestronglyMeasurable
  filter_upwards [M.positive_ae] with y hy
  rw [Real.norm_eq_abs, abs_of_nonneg (perEffectFisher_nonneg (M.effect y) hy)]
  exact perEffectFisher_le (M.effect y) hy

/-- Arbitrary-outcome single-copy aligned Fisher budget. The only POVM
normalization used is the entrywise identity integral already in the actual
`DominatedPOVM`; no Fisher or zero-score assertion is assumed. -/
theorem aligned_fisher_budget [Nonempty κ] :
    ∫ y, perEffectFisher (M.effect y) ∂M.reference ≤
      4 * (Fintype.card σ : ℝ) / (Fintype.card κ : ℝ) := by
  calc
    _ ≤ ∫ y, 4 * tailTrace (M.effect y) / (Fintype.card κ : ℝ) ∂M.reference :=
      integral_mono_ae (integrable_perEffectFisher M)
        (((integrable_tailTrace M).const_mul 4).div_const _)
        (M.positive_ae.mono fun y hy => perEffectFisher_le (M.effect y) hy)
    _ = _ := by rw [integral_div, integral_const_mul, integral_tailTrace M]

end ArbitraryOutcomes
end Paper26.AlignedFisherBudget
