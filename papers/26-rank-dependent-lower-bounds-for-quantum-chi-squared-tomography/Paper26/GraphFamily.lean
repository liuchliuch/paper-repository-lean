import Paper26.QuantumModel
import Paper26.ContinuousPOVM
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Topology.Instances.Matrix

/-!
# The actual graph family of flat rank-r density matrices

For an arbitrary rectangular complex matrix `X : Matrix σ κ ℂ`, the graph
columns are `Y = [I; X]` and their Gram matrix is `A = I + X†X`.  Positivity
of `A` is proved for every `X`.  The actual orthogonal projector is
`P = Y A⁻¹ Y†`; Hermiticity, idempotence, trace and exact rank are all proved
from this formula.  For a nonempty column type its normalization is an
actual `QuantumModel.Density`, with exact rank `card κ`.

The matrix maps below are continuous for the ordinary product topology on
complex entries.  The density-valued graph chart is measurable for the
canonical coordinate sigma-algebra already defined by `ContinuousPOVM`.
No derivative, prior-density, Fisher-information or budget theorem is
assumed or encoded in the graph family.
-/

noncomputable section
open scoped BigOperators Matrix ComplexOrder
open MeasureTheory

namespace Paper26.GraphFamily

open QuantumModel

local instance matrixMeasurableSpace (m n : Type*) : MeasurableSpace (Matrix m n ℂ) :=
  inferInstanceAs (MeasurableSpace (m → n → ℂ))

local instance matrixBorelSpace (m n : Type*) [Fintype m] [Fintype n] :
    BorelSpace (Matrix m n ℂ) :=
  inferInstanceAs (BorelSpace (m → n → ℂ))

variable {κ σ : Type*} [Fintype κ] [DecidableEq κ] [Fintype σ] [DecidableEq σ]

/-- Actual graph columns: the top block is the identity and the bottom block is `X`. -/
def columns (X : Matrix σ κ ℂ) : Matrix (κ ⊕ σ) κ ℂ :=
  Matrix.fromRows 1 X

/-- The positive definite Gram matrix of the graph columns. -/
def metric (X : Matrix σ κ ℂ) : Matrix κ κ ℂ := 1 + Xᴴ * X

@[simp] theorem columns_inl (X : Matrix σ κ ℂ) (i j : κ) :
    columns X (Sum.inl i) j = (1 : Matrix κ κ ℂ) i j := rfl

@[simp] theorem columns_inr (X : Matrix σ κ ℂ) (i : σ) (j : κ) :
    columns X (Sum.inr i) j = X i j := rfl

/-- The full graph Gram identity, with the prescribed sum split. -/
theorem columns_gram (X : Matrix σ κ ℂ) : (columns X)ᴴ * columns X = metric X := by
  simp only [columns, Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose,
    Matrix.fromCols_mul_fromRows, Matrix.conjTranspose_one, Matrix.one_mul, metric]

/-- The identity summand makes the graph Gram matrix positive definite for every `X`. -/
theorem metric_posDef (X : Matrix σ κ ℂ) : (metric X).PosDef :=
  Matrix.PosDef.one.add_posSemidef (Matrix.posSemidef_conjTranspose_mul_self X)

theorem metric_det_ne_zero (X : Matrix σ κ ℂ) : (metric X).det ≠ 0 :=
  ((Matrix.isUnit_iff_isUnit_det _).mp (metric_posDef X).isUnit).ne_zero

@[simp] theorem metric_mul_inverse (X : Matrix σ κ ℂ) : metric X * (metric X)⁻¹ = 1 :=
  Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (metric_det_ne_zero X))

@[simp] theorem inverse_mul_metric (X : Matrix σ κ ℂ) : (metric X)⁻¹ * metric X = 1 :=
  Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (metric_det_ne_zero X))

/-- The actual graph-space projector, without a square-root or a selected frame. -/
def projectorMatrix (X : Matrix σ κ ℂ) : Matrix (κ ⊕ σ) (κ ⊕ σ) ℂ :=
  columns X * (metric X)⁻¹ * (columns X)ᴴ

theorem projectorMatrix_hermitian (X : Matrix σ κ ℂ) : (projectorMatrix X).IsHermitian :=
  Matrix.isHermitian_mul_mul_conjTranspose _ (metric_posDef X).isHermitian.inv

/-- The projector acts as the identity on the graph columns. -/
theorem projectorMatrix_mul_columns (X : Matrix σ κ ℂ) :
    projectorMatrix X * columns X = columns X := by
  simp only [projectorMatrix, Matrix.mul_assoc]
  rw [columns_gram, inverse_mul_metric, Matrix.mul_one]

theorem projectorMatrix_idempotent (X : Matrix σ κ ℂ) :
    projectorMatrix X * projectorMatrix X = projectorMatrix X := by
  change projectorMatrix X * (columns X * (metric X)⁻¹ * (columns X)ᴴ) = _
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, projectorMatrix_mul_columns]
  rfl

/-- The formula constructs the actual projector object used in the quantum model. -/
def projector (X : Matrix σ κ ℂ) : OrthogonalProjector (κ ⊕ σ) where
  matrix := projectorMatrix X
  hermitian := projectorMatrix_hermitian X
  idempotent := projectorMatrix_idempotent X

@[simp] theorem projector_matrix (X : Matrix σ κ ℂ) :
    (projector X).matrix = projectorMatrix X := rfl

/-- Its trace is exactly the number of graph columns. -/
theorem projector_trace (X : Matrix σ κ ℂ) :
    Matrix.trace (projector X).matrix = (Fintype.card κ : ℂ) := by
  rw [projector_matrix, projectorMatrix, Matrix.trace_mul_comm]
  rw [← Matrix.mul_assoc, columns_gram, metric_mul_inverse]
  simp

/-- Hermitian idempotence turns the proved trace into the actual matrix rank. -/
theorem projector_rank (X : Matrix σ κ ℂ) :
    (projector X).matrix.rank = Fintype.card κ := by
  have h : ((projector X).matrix.rank : ℂ) = (Fintype.card κ : ℂ) :=
    (projector X).trace_eq_rank.symm.trans (projector_trace X)
  exact_mod_cast h

/-- The explicit four blocks of the graph projector, as in the source graph chart. -/
theorem projectorMatrix_blocks (X : Matrix σ κ ℂ) :
    projectorMatrix X = Matrix.fromBlocks (metric X)⁻¹ ((metric X)⁻¹ * Xᴴ)
      (X * (metric X)⁻¹) (X * (metric X)⁻¹ * Xᴴ) := by
  unfold projectorMatrix columns
  rw [Matrix.fromRows_mul, Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose,
    Matrix.conjTranspose_one, Matrix.fromRows_mul_fromCols]
  simp only [Matrix.one_mul, Matrix.mul_one]

/-- The actual flat graph-family state. -/
def density [Nonempty κ] (X : Matrix σ κ ℂ) : Density (κ ⊕ σ) :=
  (projector X).flat (by rw [projector_rank]; exact Fintype.card_pos)

@[simp] theorem density_matrix [Nonempty κ] (X : Matrix σ κ ℂ) :
    (density X).matrix = ((Fintype.card κ : ℝ)⁻¹) • projectorMatrix X := by
  change (((projector X).matrix.rank : ℝ)⁻¹) • (projector X).matrix = _
  rw [projector_rank, projector_matrix]

theorem density_rank [Nonempty κ] (X : Matrix σ κ ℂ) :
    (density X).matrix.rank = Fintype.card κ := by
  rw [density, OrthogonalProjector.flat_rank, projector_rank]

theorem density_rankAtMost [Nonempty κ] (X : Matrix σ κ ℂ) :
    density X ∈ Density.RankAtMost (Fintype.card κ) :=
  (density_rank X).le

/-- The graph column map is continuous for the ordinary complex-entry topology. -/
theorem continuous_columns : Continuous (columns : Matrix σ κ ℂ → Matrix (κ ⊕ σ) κ ℂ) := by
  apply continuous_matrix
  intro i j
  cases i with
  | inl i => exact continuous_const
  | inr i => exact continuous_apply_apply i j

theorem continuous_metric : Continuous (metric : Matrix σ κ ℂ → Matrix κ κ ℂ) :=
  continuous_const.add (continuous_id.matrix_conjTranspose.matrix_mul continuous_id)

/-- The graph inverse varies continuously: its determinant never vanishes. -/
theorem continuous_inverse_metric :
    Continuous (fun X : Matrix σ κ ℂ => (metric X)⁻¹) := by
  have hc : Continuous (metric : Matrix σ κ ℂ → Matrix κ κ ℂ) := continuous_metric
  have hi : Continuous (fun X : Matrix σ κ ℂ => ((metric X).det)⁻¹) :=
    hc.matrix_det.inv₀ (fun X => metric_det_ne_zero X)
  simpa only [Matrix.inv_def, Ring.inverse_eq_inv] using hi.smul hc.matrix_adjugate

theorem continuous_projectorMatrix :
    Continuous (projectorMatrix : Matrix σ κ ℂ → Matrix (κ ⊕ σ) (κ ⊕ σ) ℂ) :=
  (continuous_columns.matrix_mul continuous_inverse_metric).matrix_mul
    continuous_columns.matrix_conjTranspose

/-- Continuity of the actual density entries, without choosing a matrix norm. -/
theorem continuous_density_matrix [Nonempty κ] :
    Continuous (fun X : Matrix σ κ ℂ => (density X).matrix) := by
  simp only [density_matrix]
  exact continuous_const.smul continuous_projectorMatrix

/-- Canonical measurability of the actual graph-family state map. -/
theorem measurable_density [Nonempty κ] :
    Measurable (density : Matrix σ κ ℂ → Density (κ ⊕ σ)) := by
  have hc : Continuous (fun X : σ → κ → ℂ => ((density X).matrix :
      (κ ⊕ σ) → (κ ⊕ σ) → ℂ)) := continuous_density_matrix
  have hm : Measurable (fun X : σ → κ → ℂ => ((density X).matrix :
      (κ ⊕ σ) → (κ ⊕ σ) → ℂ)) := hc.measurable
  intro s hs
  rcases hs with ⟨t, ht, rfl⟩
  exact hm ht

end Paper26.GraphFamily
