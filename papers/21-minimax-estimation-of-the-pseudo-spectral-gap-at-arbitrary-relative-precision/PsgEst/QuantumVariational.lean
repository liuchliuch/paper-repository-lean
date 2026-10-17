import PsgEst.TraceExponential
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.HermitianFunctionalCalculus

/-!
# Finite-dimensional Gibbs variational inequality

The proof compares the actual spectral bases of two real self-adjoint matrices.
Their squared overlaps form a doubly stochastic matrix. Summing the scalar
Fenchel inequality against those overlaps gives the trace inequality, without
Lieb concavity or any concentration theorem as a premise.
-/

open Matrix BigOperators Real
open scoped Matrix.Norms.L2Operator

namespace PsgEst.QuantumVariational

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Scalar Fenchel inequality for the exponential and `x log x - x`. -/
theorem scalar_fenchel (x a : ℝ) (hx : 0 < x) :
    x * a - x * log x + x ≤ exp a := by
  calc x * a - x * log x + x = x * ((a - log x) + 1) := by ring
    _ ≤ x * exp (a - log x) :=
      mul_le_mul_of_nonneg_left (Real.add_one_le_exp _) hx.le
    _ = exp a := by rw [Real.exp_sub, Real.exp_log hx]; field_simp

/-- Change of coordinates between the actual orthogonal eigenvector bases. -/
noncomputable def overlapUnitary {X K : Matrix ι ι ℝ}
    (hX : X.IsHermitian) (hK : K.IsHermitian) : Matrix.unitaryGroup ι ℝ :=
  star hX.eigenvectorUnitary * hK.eigenvectorUnitary

/-- Squared eigenbasis overlap, a nonnegative doubly stochastic weight. -/
noncomputable def overlapWeight {X K : Matrix ι ι ℝ}
    (hX : X.IsHermitian) (hK : K.IsHermitian) (i j : ι) : ℝ :=
  (overlapUnitary hX hK i j) ^ 2

theorem overlap_nonneg {X K : Matrix ι ι ℝ}
    (hX : X.IsHermitian) (hK : K.IsHermitian) (i j : ι) :
    0 ≤ overlapWeight hX hK i j := sq_nonneg _

theorem overlap_row_sum {X K : Matrix ι ι ℝ}
    (hX : X.IsHermitian) (hK : K.IsHermitian) (i : ι) :
    ∑ j, overlapWeight hX hK i j = 1 := by
  have h := congrArg (fun M : Matrix ι ι ℝ => M i i)
    (unitary.coe_mul_star_self (overlapUnitary hX hK))
  simpa only [Matrix.mul_apply, Matrix.star_apply, star_trivial,
    Matrix.one_apply_eq, overlapWeight, pow_two] using h

theorem overlap_col_sum {X K : Matrix ι ι ℝ}
    (hX : X.IsHermitian) (hK : K.IsHermitian) (j : ι) :
    ∑ i, overlapWeight hX hK i j = 1 := by
  have h := congrArg (fun M : Matrix ι ι ℝ => M j j)
    (unitary.coe_star_mul_self (overlapUnitary hX hK))
  simpa only [Matrix.mul_apply, Matrix.star_apply, star_trivial,
    Matrix.one_apply_eq, overlapWeight, pow_two] using h

/-- Swapping the two spectral bases transposes the squared overlap. -/
theorem overlap_flip {X K : Matrix ι ι ℝ}
    (hX : X.IsHermitian) (hK : K.IsHermitian) (i j : ι) :
    overlapWeight hX hK i j = overlapWeight hK hX j i := by
  have hu : (overlapUnitary hK hX : Matrix ι ι ℝ) =
      star (overlapUnitary hX hK : Matrix ι ι ℝ) := by
    change star (hK.eigenvectorUnitary : Matrix ι ι ℝ) *
        (hX.eigenvectorUnitary : Matrix ι ι ℝ) =
      star (star (hX.eigenvectorUnitary : Matrix ι ι ℝ) *
        (hK.eigenvectorUnitary : Matrix ι ι ℝ))
    rw [Matrix.star_mul, star_star]
  have he := congrArg (fun M : Matrix ι ι ℝ => M j i) hu
  simp only [Matrix.star_apply, star_trivial] at he
  exact congrArg (fun t : ℝ => t ^ 2) he.symm

/-- Relative entropy of positive definite real matrices, using the actual
continuous functional calculus logarithm. Positivity is required by the theorems
rather than encoded as a convention in this definition. -/
noncomputable def relativeEntropy (X A : Matrix ι ι ℝ) : ℝ :=
  Matrix.trace (X * CFC.log X) - Matrix.trace (X * CFC.log A)

/-- Diagonal trace calculation after changing between two orthogonal bases. -/
theorem trace_diagonal_overlap (O : Matrix ι ι ℝ) (a b : ι → ℝ) :
    Matrix.trace (Matrix.diagonal a * O * Matrix.diagonal b * star O) =
      ∑ i, ∑ j, O i j ^ 2 * (a i * b j) := by
  unfold Matrix.trace
  apply Finset.sum_congr rfl
  intro i _
  change (Matrix.diagonal a * O * Matrix.diagonal b * star O) i i = _
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.star_apply, star_trivial]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The trace of the product of spectral functions is the double sum against
squared overlaps of their actual eigenvector bases. -/
theorem trace_spectralMap_mul {X K : Matrix ι ι ℝ}
    (hX : X.IsHermitian) (hK : K.IsHermitian) (f g : ℝ → ℝ) :
    Matrix.trace (spectralMap hX f * spectralMap hK g) =
      ∑ i, ∑ j, overlapWeight hX hK i j * (f (hX.eigenvalues i) * g (hK.eigenvalues j)) := by
  let U : Matrix ι ι ℝ := hX.eigenvectorUnitary
  let V : Matrix ι ι ℝ := hK.eigenvectorUnitary
  let D : Matrix ι ι ℝ := Matrix.diagonal (fun i => f (hX.eigenvalues i))
  let E : Matrix ι ι ℝ := Matrix.diagonal (fun j => g (hK.eigenvalues j))
  have hcycle : Matrix.trace ((U * D * star U) * (V * E * star V)) =
      Matrix.trace (D * (star U * V) * E * star (star U * V)) := by
    calc Matrix.trace ((U * D * star U) * (V * E * star V)) =
        Matrix.trace (U * (D * (star U * (V * (E * star V))))) := by
          congr 1
          simp only [Matrix.mul_assoc]
      _ = Matrix.trace ((D * (star U * (V * (E * star V)))) * U) :=
        Matrix.trace_mul_comm _ _
      _ = Matrix.trace (D * (star U * V) * E * star (star U * V)) := by
        congr 1
        simp only [Matrix.star_mul, star_star, Matrix.mul_assoc]
  calc Matrix.trace (spectralMap hX f * spectralMap hK g) =
      Matrix.trace (D * (star U * V) * E * star (star U * V)) := hcycle
    _ = ∑ i, ∑ j, (star U * V) i j ^ 2 *
        (f (hX.eigenvalues i) * g (hK.eigenvalues j)) :=
      trace_diagonal_overlap (star U * V) _ _
    _ = _ := by rfl

/-- Gibbs inequality, initially written with the spectral logarithm of `X`.
The exponential on the right is the actual matrix power-series exponential. -/
theorem gibbs_spectralLog {X K : Matrix ι ι ℝ} (hK : K.IsHermitian) (hX : X.PosDef) :
    Matrix.trace (X * K) - Matrix.trace (X * spectralMap hX.1 Real.log) + Matrix.trace X ≤
      traceExp K := by
  let x : ι → ℝ := hX.1.eigenvalues
  let a : ι → ℝ := hK.eigenvalues
  let p : ι → ι → ℝ := overlapWeight hX.1 hK
  have hx (i : ι) : 0 < x i := hX.eigenvalues_pos i
  have hrow (i : ι) : ∑ j, p i j = 1 := overlap_row_sum hX.1 hK i
  have hcol (j : ι) : ∑ i, p i j = 1 := overlap_col_sum hX.1 hK j
  have hproduct : Matrix.trace (X * K) = ∑ i, ∑ j, p i j * (x i * a j) := by
    simpa only [spectralMap_id, id_eq] using trace_spectralMap_mul hX.1 hK id id
  have hentropy : Matrix.trace (X * spectralMap hX.1 Real.log) = ∑ i, x i * log (x i) := by
    have hmul : X * spectralMap hX.1 Real.log = spectralMap hX.1 (fun t => t * log t) := by
      simpa only [spectralMap_id, id_eq] using spectralMap_mul hX.1 id Real.log
    rw [hmul, trace_spectralMap]
  have htrace : Matrix.trace X = ∑ i, x i := by
    simpa using hX.1.trace_eq_sum_eigenvalues
  have hleft (i : ι) :
      (∑ j, p i j * (x i * a j - x i * log (x i) + x i)) =
        (∑ j, p i j * (x i * a j)) - x i * log (x i) + x i := by
    simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.sum_mul, hrow, one_mul]
  have hright : (∑ i, ∑ j, p i j * exp (a j)) = ∑ j, exp (a j) := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, hcol, one_mul]
  have hpair : (∑ i, ∑ j, p i j * (x i * a j - x i * log (x i) + x i)) ≤
      ∑ i, ∑ j, p i j * exp (a j) := by
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    exact mul_le_mul_of_nonneg_left (scalar_fenchel (x i) (a j) (hx i))
      (overlap_nonneg hX.1 hK i j)
  simp_rw [hleft, Finset.sum_add_distrib, Finset.sum_sub_distrib] at hpair
  rw [hright] at hpair
  rw [hproduct, hentropy, htrace, traceExp_eq_sum_eigenvalues hK]
  exact hpair

/-- The CFC logarithm and the same orthogonal spectral calculus used above. -/
theorem log_eq_spectralMap {X : Matrix ι ι ℝ} (hX : X.IsHermitian) :
    CFC.log X = spectralMap hX Real.log := by
  rw [CFC.log, hX.cfc_eq]
  simp only [Matrix.IsHermitian.cfc, spectralMap, Function.comp_def,
    RCLike.ofReal_real_eq_id, id_eq]

/-- The self-adjointness of the actual CFC logarithm. -/
theorem log_isHermitian {X : Matrix ι ι ℝ} (hX : X.IsHermitian) :
    (CFC.log X).IsHermitian := by
  rw [log_eq_spectralMap hX]
  exact spectralMap_isHermitian hX Real.log

/-- Gibbs variational inequality with the actual matrix logarithm. -/
theorem gibbs {X K : Matrix ι ι ℝ} (hK : K.IsHermitian) (hX : X.PosDef) :
    Matrix.trace (X * K) - Matrix.trace (X * CFC.log X) + Matrix.trace X ≤
      traceExp K := by
  rw [log_eq_spectralMap hX.1]
  exact gibbs_spectralLog hK hX

/-- The positive definite maximizer is the actual power-series exponential. -/
theorem gibbs_attainment {K : Matrix ι ι ℝ} (hK : K.IsHermitian) :
    (NormedSpace.exp ℝ K).PosDef ∧
    Matrix.trace (NormedSpace.exp ℝ K * K) -
      Matrix.trace (NormedSpace.exp ℝ K * CFC.log (NormedSpace.exp ℝ K)) +
      Matrix.trace (NormedSpace.exp ℝ K) = traceExp K := by
  refine ⟨matrixExp_posDef hK, ?_⟩
  rw [CFC.log_exp K hK, sub_self, zero_add]
  rfl

/-- Relative entropy agrees with the usual trace of `X(log X-log A)`. -/
theorem relativeEntropy_eq_trace_mul_sub (X A : Matrix ι ι ℝ) :
    relativeEntropy X A = Matrix.trace (X * (CFC.log X - CFC.log A)) := by
  rw [relativeEntropy, Matrix.mul_sub, Matrix.trace_sub]

/-- Entropy trace in the actual spectral basis. -/
theorem trace_mul_self_log {X : Matrix ι ι ℝ} (hX : X.IsHermitian) :
    Matrix.trace (X * CFC.log X) = ∑ i, hX.eigenvalues i * log (hX.eigenvalues i) := by
  rw [log_eq_spectralMap hX]
  have hmul : X * spectralMap hX Real.log = spectralMap hX (fun t => t * log t) := by
    simpa only [spectralMap_id, id_eq] using spectralMap_mul hX id Real.log
  rw [hmul, trace_spectralMap]

/-- Relative entropy expanded in the two genuine eigenbases. -/
theorem relativeEntropy_eq_overlap {X A : Matrix ι ι ℝ}
    (hX : X.IsHermitian) (hA : A.IsHermitian) :
    relativeEntropy X A = ∑ i, ∑ j, overlapWeight hX hA i j *
      (hX.eigenvalues i * (log (hX.eigenvalues i) - log (hA.eigenvalues j))) := by
  have hcross : Matrix.trace (X * CFC.log A) =
      ∑ i, ∑ j, overlapWeight hX hA i j * (hX.eigenvalues i * log (hA.eigenvalues j)) := by
    rw [log_eq_spectralMap hA]
    simpa only [spectralMap_id, id_eq] using trace_spectralMap_mul hX hA id Real.log
  rw [relativeEntropy, trace_mul_self_log hX, hcross]
  simp only [mul_sub, Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_mul, overlap_row_sum, one_mul]

/-- Orientation with `A` labeling rows and `X` columns, convenient for the
Sylvester-resolvent integral representation of relative entropy. -/
theorem relativeEntropy_eq_overlap_reverse {X A : Matrix ι ι ℝ}
    (hX : X.IsHermitian) (hA : A.IsHermitian) :
    relativeEntropy X A = ∑ i, ∑ j, overlapWeight hA hX i j *
      (hX.eigenvalues j * (log (hX.eigenvalues j) - log (hA.eigenvalues i))) := by
  rw [relativeEntropy_eq_overlap hX hA, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [overlap_flip]

/-- Variational upper bound for `tr exp(H+log A)`, using actual relative entropy. -/
theorem variational_bound {H A X : Matrix ι ι ℝ}
    (hH : H.IsHermitian) (hA : A.PosDef) (hX : X.PosDef) :
    Matrix.trace (X * H) - relativeEntropy X A + Matrix.trace X ≤
      traceExp (H + CFC.log A) := by
  have hK : (H + CFC.log A).IsHermitian := hH.add (log_isHermitian hA.1)
  have h := gibbs hK hX
  rw [Matrix.mul_add, Matrix.trace_add] at h
  unfold relativeEntropy
  linarith

/-- The upper bound is attained at `X=exp(H+log A)`, with no supremum or
concavity theorem assumed. -/
theorem variational_attainment {H A : Matrix ι ι ℝ}
    (hH : H.IsHermitian) (hA : A.PosDef) :
    let X := NormedSpace.exp ℝ (H + CFC.log A)
    X.PosDef ∧ Matrix.trace (X * H) - relativeEntropy X A + Matrix.trace X =
      traceExp (H + CFC.log A) := by
  let X := NormedSpace.exp ℝ (H + CFC.log A)
  have hK : (H + CFC.log A).IsHermitian := hH.add (log_isHermitian hA.1)
  have h := gibbs_attainment hK
  refine ⟨h.1, ?_⟩
  have heq := h.2
  rw [Matrix.mul_add, Matrix.trace_add] at heq
  unfold relativeEntropy
  linarith

end PsgEst.QuantumVariational
