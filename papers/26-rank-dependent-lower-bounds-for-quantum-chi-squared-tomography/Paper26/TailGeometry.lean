import Paper26.Normalization
import Paper26.TailConvexity
import Paper26.ShellAccounting
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Complex.Order
import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite

/-!
# Tail Gram geometry for Lemma 2.3

All Gram and Frobenius quantities below are actual rectangular complex
matrices. The column dimension controls the quartic lower bound; it is not
replaced by the ambient row dimension.
-/

noncomputable section
open scoped BigOperators Matrix ComplexOrder

namespace Paper26.TailGeometry

open Paper26.ShellAccounting

variable {σ κ : Type*} [Fintype σ] [Fintype κ]

/-- The real part of the trace is controlled by the Frobenius norm and the
matrix dimension. Only the diagonal terms enter Cauchy--Schwarz. -/
theorem sq_re_trace_le_card_mul_frobeniusSq (G : Matrix κ κ ℂ) :
    (Matrix.trace G).re ^ 2 ≤ (Fintype.card κ : ℝ) * frobeniusSq G := by
  have hdiag : (∑ i, (G i i).re ^ 2) ≤ frobeniusSq G := by
    apply Finset.sum_le_sum
    intro i _
    have hre : (G i i).re ^ 2 ≤ ‖G i i‖ ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      nlinarith [sq_nonneg (G i i).im]
    exact hre.trans (Finset.single_le_sum (fun j _ => sq_nonneg ‖G i j‖)
      (Finset.mem_univ i))
  calc
    (Matrix.trace G).re ^ 2 = (∑ i, (G i i).re) ^ 2 := by
      simp [Matrix.trace, Matrix.diag_apply, Complex.re_sum]
    _ ≤ (Fintype.card κ : ℝ) * ∑ i, (G i i).re ^ 2 := by
      simpa using (sq_sum_le_card_mul_sum_sq (s := Finset.univ)
        (f := fun i => (G i i).re))
    _ ≤ (Fintype.card κ : ℝ) * frobeniusSq G :=
      mul_le_mul_of_nonneg_left hdiag (Nat.cast_nonneg _)

/-- The two rectangular Gram matrices have the same Frobenius square. -/
theorem frobeniusSq_gram_comm (Z : Matrix σ κ ℂ) :
    frobeniusSq (Z * Zᴴ) = frobeniusSq (Zᴴ * Z) := by
  rw [frobeniusSq_eq_trace, frobeniusSq_eq_trace]
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  have ht : Matrix.trace (Z * Zᴴ * (Z * Zᴴ)) =
      Matrix.trace (Zᴴ * Z * (Zᴴ * Z)) := by
    calc
      _ = Matrix.trace (Z * (Zᴴ * Z * Zᴴ)) := by
        simp only [Matrix.mul_assoc]
      _ = Matrix.trace ((Zᴴ * Z * Zᴴ) * Z) := Matrix.trace_mul_comm _ _
      _ = _ := by simp only [Matrix.mul_assoc]
  exact congrArg Complex.re ht

/-- The low-rank Gram inequality needed for the quartic tail coercivity:
`‖Z‖_F^4 ≤ (#columns) ‖ZZ†‖_F²`. It is valid even for an empty column type. -/
theorem gram_frobenius_inequality (Z : Matrix σ κ ℂ) :
    (frobeniusSq Z) ^ 2 ≤ (Fintype.card κ : ℝ) * frobeniusSq (Z * Zᴴ) := by
  have ht : frobeniusSq Z = (Matrix.trace (Zᴴ * Z)).re := by
    rw [frobeniusSq_eq_trace, Matrix.trace_mul_comm]
  rw [ht]
  have hg := sq_re_trace_le_card_mul_frobeniusSq (Zᴴ * Z)
  rwa [← frobeniusSq_gram_comm Z] at hg


variable [DecidableEq σ]

/-- The actual inverse-Jordan quadratic form in the original matrix basis. -/
def quadraticEnergy (A Y : Matrix σ σ ℂ) : ℝ :=
  (Matrix.trace (Y * Normalization.jordanInverse A Y)).re

/-- The quartic tail energy `H_A(Z)` from Lemma 2.3. -/
abbrev tailEnergy (A : Matrix σ σ ℂ) (Z : Matrix σ κ ℂ) : ℝ :=
  TailConvexity.H A Z

omit [DecidableEq σ] in
/-- The origin has zero tail energy, without a positivity assumption. -/
@[simp] theorem tailEnergy_zero (A : Matrix σ σ ℂ) :
    TailConvexity.H A (0 : Matrix σ κ ℂ) = 0 := by
  simp [TailConvexity.H, TailConvexity.Q, TailConvexity.pairing]

omit [DecidableEq σ] in
/-- Nonnegative sublevels contain the origin. -/
theorem tail_sublevel_nonempty (A : Matrix σ σ ℂ) {t : ℝ} (ht : 0 ≤ t) :
    ({Z : Matrix σ κ ℂ | TailConvexity.H A Z ≤ t} : Set (Matrix σ κ ℂ)).Nonempty := by
  refine ⟨0, ?_⟩
  simpa only [Set.mem_setOf_eq, tailEnergy_zero] using ht

/-- Fixed-positive-matrix inversion of the Jordan operator is continuous.
The proof uses its explicit spectral inverse on every matrix input. -/
theorem continuous_jordanInverse (A : Matrix σ σ ℂ) (hA : A.PosDef) :
    Continuous (Normalization.jordanInverse A : Matrix σ σ ℂ → Matrix σ σ ℂ) := by
  obtain ⟨U, a, hU₁, hU₂, ha, hAeq⟩ :=
    Normalization.exists_positive_spectral_representation A hA
  have heq : (Normalization.jordanInverse A : Matrix σ σ ℂ → Matrix σ σ ℂ) =
      fun X => Normalization.conjugate U
        (Normalization.inverseJordan a (Normalization.coordinates U X)) := by
    funext X
    rw [hAeq, Normalization.jordanInverse_eq_transported U X a hU₁ hU₂ ha]
    rfl
  rw [heq]
  have hc : Continuous (Normalization.coordinates U : Matrix σ σ ℂ → Matrix σ σ ℂ) := by
    exact (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  have hi : Continuous (Normalization.inverseJordan a : Matrix σ σ ℂ → Matrix σ σ ℂ) := by
    apply continuous_matrix
    intro i j
    exact continuous_const.mul (continuous_apply_apply i j)
  have hu : Continuous (Normalization.conjugate U : Matrix σ σ ℂ → Matrix σ σ ℂ) := by
    exact (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  exact hu.comp (hi.comp hc)

/-- For fixed positive `A`, the genuine tail energy is continuous in all
real and imaginary coordinates of the rectangular complex matrix. -/
theorem continuous_tailEnergy (A : Matrix σ σ ℂ) (hA : A.PosDef) :
    Continuous (tailEnergy A : Matrix σ κ ℂ → ℝ) := by
  have hg : Continuous (fun Z : Matrix σ κ ℂ => Z * Zᴴ) :=
    continuous_id.matrix_mul continuous_id.matrix_conjTranspose
  exact Complex.continuous_re.comp
    (hg.matrix_mul ((continuous_jordanInverse A hA).comp hg)).matrix_trace

/-- Exact transport of the quadratic form under a unitary spectral
representation; this is an equality about original-basis matrix traces. -/
theorem quadraticEnergy_conjugate (U : Matrix σ σ ℂ) (a : σ → ℝ)
    (X : Matrix σ σ ℂ) (hU₁ : Uᴴ * U = 1) (hU₂ : U * Uᴴ = 1)
    (ha : ∀ i, 0 < a i) :
    quadraticEnergy (Normalization.conjugate U (Normalization.diagonalMatrix a))
      (Normalization.conjugate U X) =
      (Matrix.trace (X * Normalization.inverseJordan a X)).re := by
  unfold quadraticEnergy
  rw [Normalization.jordanInverse_eq_transported U _ a hU₁ hU₂ ha]
  unfold Normalization.transportedInverseJordan
  rw [Normalization.coordinates_conjugate U X hU₁,
    ← Normalization.conjugate_mul U _ _ hU₁,
    Normalization.trace_conjugate U _ hU₁]

/-- The diagonal inverse-Jordan quadratic form has positive spectral weights
on every ordered entry of a Hermitian matrix. -/
theorem inverseJordan_trace_sum (a : σ → ℝ) (X : Matrix σ σ ℂ)
    (hX : X.IsHermitian) :
    (Matrix.trace (X * Normalization.inverseJordan a X)).re =
      ∑ i, ∑ j, (2 / (a i + a j)) * Complex.normSq (X i j) := by
  have hh : (X + Normalization.diagonalMatrix a)ᴴ =
      X + Normalization.diagonalMatrix a := by
    rw [Matrix.conjTranspose_add, hX.eq, Normalization.diagonalMatrix_conjTranspose]
  have h := Normalization.buresEnergy_eq_trace (X + Normalization.diagonalMatrix a) a hh
  simpa only [Normalization.buresEnergy, Normalization.spectralEnergy,
    Matrix.add_apply, add_sub_cancel_right] using h.symm

/-- Unitary coordinates preserve the actual entrywise Frobenius square. -/
theorem frobeniusSq_coordinates (U Y : Matrix σ σ ℂ) (hU : U * Uᴴ = 1) :
    frobeniusSq (Normalization.coordinates U Y) = frobeniusSq Y := by
  rw [Normalization.coordinates, frobeniusSq_mul_unitary _ U hU,
    frobeniusSq_unitary_mul Y Uᴴ (by simpa using hU)]

/-- Positive definiteness implies an actual coercive quadratic bound on every
Hermitian input. The constant is derived from the spectrum of `A`, not supplied
as an assumption about the target energy. -/
theorem exists_quadratic_bound (A : Matrix σ σ ℂ) (hA : A.PosDef) :
    ∃ C : ℝ, 0 < C ∧ ∀ Y : Matrix σ σ ℂ, Y.IsHermitian →
      frobeniusSq Y ≤ C * quadraticEnergy A Y := by
  obtain ⟨U, a, hU₁, hU₂, ha, hAeq⟩ :=
    Normalization.exists_positive_spectral_representation A hA
  let C : ℝ := 1 + ∑ i, a i
  have hsum : 0 ≤ ∑ i, a i := Finset.sum_nonneg (fun i _ => (ha i).le)
  have hC : 0 < C := by dsimp [C]; linarith
  have hai (i : σ) : a i ≤ ∑ j, a j :=
    Finset.single_le_sum (fun j _ => (ha j).le) (Finset.mem_univ i)
  have hw (i j : σ) : 1 ≤ C * (2 / (a i + a j)) := by
    rw [← mul_div_assoc]
    apply (le_div_iff₀ (add_pos (ha i) (ha j))).mpr
    have hi := hai i
    have hj := hai j
    dsimp [C]
    linarith
  refine ⟨C, hC, ?_⟩
  intro Y hY
  let X := Normalization.coordinates U Y
  have hX : X.IsHermitian :=
    Normalization.coordinates_hermitian U Y hY.eq
  have hspec : quadraticEnergy A Y =
      ∑ i, ∑ j, (2 / (a i + a j)) * Complex.normSq (X i j) := by
    have ht := quadraticEnergy_conjugate U a X hU₁ hU₂ ha
    rw [Normalization.conjugate_coordinates U Y hU₂] at ht
    rw [hAeq, ht, inverseJordan_trace_sum a X hX]
  rw [hspec, ← frobeniusSq_coordinates U Y hU₂]
  change (∑ i, ∑ j, ‖X i j‖ ^ 2) ≤ _
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  rw [Complex.sq_norm]
  have hm := mul_le_mul_of_nonneg_right (hw i j) (Complex.normSq_nonneg (X i j))
  simpa only [one_mul, mul_assoc] using hm

/-- Strictly positive quartic coercivity of the true tail energy. The harmless
`card κ + 1` in this existence statement also covers a zero-dimensional domain;
the exact rank factor is available separately in `gram_frobenius_inequality`. -/
theorem exists_tail_quartic_bound (A : Matrix σ σ ℂ) (hA : A.PosDef) :
    ∃ C : ℝ, 0 < C ∧ ∀ Z : Matrix σ κ ℂ,
      (frobeniusSq Z) ^ 2 ≤ C * tailEnergy A Z := by
  obtain ⟨C, hC, hq⟩ := exists_quadratic_bound A hA
  refine ⟨((Fintype.card κ : ℝ) + 1) * C, by positivity, ?_⟩
  intro Z
  have hgram := gram_frobenius_inequality Z
  have hqZ := hq (Z * Zᴴ) (Matrix.posSemidef_self_mul_conjTranspose Z).1
  have hnonneg := frobeniusSq_nonneg (Z * Zᴴ)
  have hmul := mul_le_mul_of_nonneg_left hqZ
    (show 0 ≤ (Fintype.card κ : ℝ) + 1 by positivity)
  change (frobeniusSq Z) ^ 2 ≤
    (((Fintype.card κ : ℝ) + 1) * C) * quadraticEnergy A (Z * Zᴴ)
  nlinarith

/-- The fixed-positive-matrix quartic energy is nonnegative, proved from
its internally derived coercive bound. -/
theorem tailEnergy_nonneg (A : Matrix σ σ ℂ) (hA : A.PosDef) (Z : Matrix σ κ ℂ) :
    0 ≤ TailConvexity.H A Z := by
  obtain ⟨C, hC, hbound⟩ := exists_tail_quartic_bound (κ := κ) A hA
  have hb := hbound Z
  have hs := sq_nonneg (frobeniusSq Z)
  change (frobeniusSq Z) ^ 2 ≤ C * TailConvexity.H A Z at hb
  nlinarith

omit [DecidableEq σ] in
/-- Each entry is controlled by the full rectangular Frobenius square. -/
theorem entry_sq_le_frobeniusSq (Z : Matrix σ κ ℂ) (i : σ) (j : κ) :
    ‖Z i j‖ ^ 2 ≤ frobeniusSq Z := by
  have hi : ‖Z i j‖ ^ 2 ≤ ∑ k, ‖Z i k‖ ^ 2 :=
    Finset.single_le_sum (fun k _ => sq_nonneg ‖Z i k‖) (Finset.mem_univ j)
  have hj : (∑ k, ‖Z i k‖ ^ 2) ≤ ∑ l, ∑ k, ‖Z l k‖ ^ 2 :=
    Finset.single_le_sum
      (fun l _ => Finset.sum_nonneg (fun k _ => sq_nonneg ‖Z l k‖)) (Finset.mem_univ i)
  exact hi.trans hj

/-- Every sublevel set of `H_A` is compact in the actual finite-dimensional
complex matrix space. No finite-volume or coercivity input is assumed. -/
theorem tail_sublevel_isCompact (A : Matrix σ σ ℂ) (hA : A.PosDef) (t : ℝ) :
    IsCompact {Z : Matrix σ κ ℂ | tailEnergy A Z ≤ t} := by
  obtain ⟨C, hC, hbound⟩ := exists_tail_quartic_bound (κ := κ) A hA
  have hc : IsCompact ((Metric.closedBall (0 : ℂ) (C * |t| + 2)).matrix :
      Set (Matrix σ κ ℂ)) := (isCompact_closedBall (0 : ℂ) (C * |t| + 2)).matrix
  apply hc.of_isClosed_subset (isClosed_le (continuous_tailEnergy A hA) continuous_const)
  intro Z hZ
  change ∀ i j, Z i j ∈ Metric.closedBall (0 : ℂ) (C * |t| + 2)
  intro i j
  rw [Metric.mem_closedBall, dist_zero_right]
  have hsq : (frobeniusSq Z) ^ 2 ≤ C * |t| :=
    (hbound Z).trans (mul_le_mul_of_nonneg_left (hZ.trans (le_abs_self t)) hC.le)
  have hnonneg := frobeniusSq_nonneg Z
  have hCt : 0 ≤ C * |t| := mul_nonneg hC.le (abs_nonneg t)
  have hF : frobeniusSq Z ≤ C * |t| + 1 := by nlinarith
  have he := entry_sq_le_frobeniusSq Z i j
  have hn := norm_nonneg (Z i j)
  nlinarith

/-- Standard finite product Lebesgue measure on the real and imaginary
coordinates of a rectangular complex matrix. Writing the definition on the
underlying function type fixes the measure explicitly without installing a
global matrix metric or measure-space instance. -/
def matrixLebesgue : MeasureTheory.Measure (σ → κ → ℂ) := MeasureTheory.volume

/-- Finite Lebesgue volume of every fixed-positive-`A` tail sublevel set. The
measure is the standard product of real/imaginary Lebesgue coordinates. -/
theorem tail_sublevel_volume_lt_top (A : Matrix σ σ ℂ) (hA : A.PosDef) (t : ℝ) :
    matrixLebesgue {Z : Matrix σ κ ℂ | TailConvexity.H A Z ≤ t} < ⊤ := by
  have hc : IsCompact {Z : σ → κ → ℂ | TailConvexity.H A Z ≤ t} :=
    tail_sublevel_isCompact A hA t
  unfold matrixLebesgue
  exact hc.measure_lt_top

end Paper26.TailGeometry
