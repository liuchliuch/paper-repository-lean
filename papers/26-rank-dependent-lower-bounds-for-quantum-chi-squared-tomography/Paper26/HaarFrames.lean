import Paper26.QuantumModel
import Paper26.TailLossConstraints
import Mathlib.MeasureTheory.Function.SpecialFunctions.RCLike
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Group.Arithmetic

/-!
# Actual orthonormal frames and their flat projector states

The frame object consists of an actual rectangular complex matrix and the
identity `UᴴU = I`. Its projector, rank, density, row-unitary action, and bottom
Gram block are proved from that identity. The measurable structure is the
comap of the canonical product measurable structure on the complex entries.

`IsHaarFrameDistribution` records only a probability measure and invariance
under all unitary row rotations. No truncated-Haar matrix-ball law, graph
chart density, or normalization integral is built into that definition.
-/

noncomputable section
open scoped BigOperators Matrix ComplexOrder
open MeasureTheory

namespace Paper26.HaarFrames

local instance matrixMeasurableSpace (m n : Type*) : MeasurableSpace (Matrix m n ℂ) :=
  inferInstanceAs (MeasurableSpace (m → n → ℂ))

variable {ι κ σ : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ] [Fintype σ] [DecidableEq σ]

/-- A genuine rectangular complex orthonormal frame. -/
structure Frame (ι κ : Type*) [Fintype ι] [Fintype κ] [DecidableEq κ] where
  matrix : Matrix ι κ ℂ
  orthonormal : matrixᴴ * matrix = 1

namespace Frame

@[ext] theorem ext {U V : Frame ι κ} (h : U.matrix = V.matrix) : U = V := by
  cases U
  cases V
  cases h
  rfl

/-- Its column-space projector, as the paper's actual projector object. -/
def projector (U : Frame ι κ) : QuantumModel.OrthogonalProjector ι where
  matrix := U.matrix * U.matrixᴴ
  hermitian := Matrix.isHermitian_mul_conjTranspose_self U.matrix
  idempotent := by
    calc
      (U.matrix * U.matrixᴴ) * (U.matrix * U.matrixᴴ) =
          U.matrix * (U.matrixᴴ * U.matrix) * U.matrixᴴ := by
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [U.orthonormal]; simp

@[simp] theorem projector_matrix (U : Frame ι κ) :
    U.projector.matrix = U.matrix * U.matrixᴴ := rfl

theorem projector_trace (U : Frame ι κ) :
    Matrix.trace U.projector.matrix = (Fintype.card κ : ℂ) := by
  rw [projector_matrix, Matrix.trace_mul_comm, U.orthonormal]
  simp

/-- The frame's column dimension is its projector's actual matrix rank. -/
theorem projector_rank (U : Frame ι κ) : U.projector.matrix.rank = Fintype.card κ := by
  have h : (U.projector.matrix.rank : ℂ) = (Fintype.card κ : ℂ) :=
    U.projector.trace_eq_rank.symm.trans U.projector_trace
  exact_mod_cast h

theorem columns_le_rows (U : Frame ι κ) : Fintype.card κ ≤ Fintype.card ι := by
  rw [← U.projector_rank]
  exact Matrix.rank_le_card_height _

theorem projector_rank_pos [Nonempty κ] (U : Frame ι κ) : 0 < U.projector.matrix.rank := by
  rw [projector_rank]
  exact Fintype.card_pos

/-- The flat input state, normalized by its proved positive rank. -/
def density [Nonempty κ] (U : Frame ι κ) : QuantumModel.Density ι :=
  U.projector.flat U.projector_rank_pos

@[simp] theorem density_matrix [Nonempty κ] (U : Frame ι κ) :
    U.density.matrix = ((Fintype.card κ : ℝ)⁻¹) • (U.matrix * U.matrixᴴ) := by
  change ((U.projector.matrix.rank : ℝ)⁻¹) • U.projector.matrix = _
  rw [projector_rank, projector_matrix]

theorem density_rank [Nonempty κ] (U : Frame ι κ) :
    U.density.matrix.rank = Fintype.card κ := by
  rw [density, QuantumModel.OrthogonalProjector.flat_rank, projector_rank]

theorem density_rankAtMost [Nonempty κ] (U : Frame ι κ) :
    U.density ∈ QuantumModel.Density.RankAtMost (Fintype.card κ) := by
  change U.density.matrix.rank ≤ Fintype.card κ
  exact U.density_rank.le

/-- Multiplying all rows by an ambient unitary preserves orthonormal columns. -/
def rotate (V : Matrix.unitaryGroup ι ℂ) (U : Frame ι κ) : Frame ι κ where
  matrix := (V : Matrix ι ι ℂ) * U.matrix
  orthonormal := by
    have hV : (V : Matrix ι ι ℂ)ᴴ * (V : Matrix ι ι ℂ) = 1 := V.property.1
    calc
      ((V : Matrix ι ι ℂ) * U.matrix)ᴴ * ((V : Matrix ι ι ℂ) * U.matrix) =
          U.matrixᴴ * ((V : Matrix ι ι ℂ)ᴴ * (V : Matrix ι ι ℂ)) * U.matrix := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [hV]; simpa using U.orthonormal

@[simp] theorem rotate_matrix (V : Matrix.unitaryGroup ι ℂ) (U : Frame ι κ) :
    (U.rotate V).matrix = (V : Matrix ι ι ℂ) * U.matrix := rfl

@[simp] theorem rotate_one (U : Frame ι κ) : U.rotate 1 = U := by
  apply Frame.ext
  change (1 : Matrix ι ι ℂ) * U.matrix = U.matrix
  exact Matrix.one_mul _

theorem rotate_mul (V W : Matrix.unitaryGroup ι ℂ) (U : Frame ι κ) :
    U.rotate (V * W) = (U.rotate W).rotate V := by
  apply Frame.ext
  change ((V : Matrix ι ι ℂ) * (W : Matrix ι ι ℂ)) * U.matrix =
    (V : Matrix ι ι ℂ) * ((W : Matrix ι ι ℂ) * U.matrix)
  exact Matrix.mul_assoc _ _ _

theorem rotate_projector (V : Matrix.unitaryGroup ι ℂ) (U : Frame ι κ) :
    (U.rotate V).projector.matrix =
      (V : Matrix ι ι ℂ) * U.projector.matrix * (V : Matrix ι ι ℂ)ᴴ := by
  simp only [projector_matrix, rotate_matrix, Matrix.conjTranspose_mul, Matrix.mul_assoc]

theorem rotate_density [Nonempty κ] (V : Matrix.unitaryGroup ι ℂ) (U : Frame ι κ) :
    (U.rotate V).density.matrix =
      (V : Matrix ι ι ℂ) * U.density.matrix * (V : Matrix ι ι ℂ)ᴴ := by
  simp only [density_matrix, rotate_matrix, Matrix.conjTranspose_mul, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.mul_assoc]

/-- The last rows of a frame in the `κ ⊕ σ` source decomposition. -/
def bottom (U : Frame (κ ⊕ σ) κ) : Matrix σ κ ℂ :=
  U.matrix.submatrix Sum.inr id

/-- The actual projector bottom block is the Gram matrix of the last rows. -/
theorem bottom_projector (U : Frame (κ ⊕ σ) κ) :
    TailLossConstraints.bottomBlock U.projector.matrix = U.bottom * U.bottomᴴ := by
  ext i j
  simp only [TailLossConstraints.bottomBlock, projector_matrix, bottom,
    Matrix.submatrix_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, id_eq]

/-- The exact bottom-block premise required by the loss-to-tail constraints. -/
theorem bottom_density [Nonempty κ] (U : Frame (κ ⊕ σ) κ) :
    TailLossConstraints.bottomBlock U.density.matrix =
      TailLossConstraints.scaledGram (Fintype.card κ : ℝ) U.bottom := by
  ext i j
  simp only [TailLossConstraints.bottomBlock, density_matrix, bottom,
    Matrix.submatrix_apply, Matrix.smul_apply, TailLossConstraints.scaledGram,
    Matrix.mul_apply, Matrix.conjTranspose_apply, id_eq, one_div, Complex.real_smul,
    smul_eq_mul]

/-- Canonical product sigma-algebra on the actual complex entries, pulled
back along `Frame.matrix`; no arbitrary measurable-space parameter occurs. -/
instance measurableSpace : MeasurableSpace (Frame ι κ) :=
  MeasurableSpace.comap (fun U : Frame ι κ => (U.matrix : ι → κ → ℂ)) inferInstance

theorem measurable_matrix :
    Measurable (fun U : Frame ι κ => (U.matrix : ι → κ → ℂ)) := comap_measurable _

theorem measurable_entry (i : ι) (j : κ) :
    Measurable (fun U : Frame ι κ => U.matrix i j) :=
  (measurable_pi_apply j).comp ((measurable_pi_apply i).comp measurable_matrix)

/-- Checking the complex coordinates suffices for a frame-valued map. -/
theorem measurable_of_matrix {Ω : Type*} [MeasurableSpace Ω]
    (f : Ω → Frame ι κ)
    (hf : Measurable (fun x => ((f x).matrix : ι → κ → ℂ))) : Measurable f := by
  intro s hs
  rcases hs with ⟨t, ht, rfl⟩
  exact hf ht

theorem measurable_rotate (V : Matrix.unitaryGroup ι ℂ) :
    Measurable (fun U : Frame ι κ => U.rotate V) := by
  apply measurable_of_matrix
  apply measurable_pi_iff.2
  intro i
  apply measurable_pi_iff.2
  intro j
  change Measurable (fun U : Frame ι κ => ∑ k, (V : Matrix ι ι ℂ) i k * U.matrix k j)
  exact Finset.measurable_sum Finset.univ fun k _ =>
    (measurable_entry k j).const_mul ((V : Matrix ι ι ℂ) i k)

theorem measurable_projector_matrix :
    Measurable (fun U : Frame ι κ => (U.projector.matrix : ι → ι → ℂ)) := by
  apply measurable_pi_iff.2
  intro i
  apply measurable_pi_iff.2
  intro j
  change Measurable (fun U : Frame ι κ => ∑ k, U.matrix i k * star (U.matrix j k))
  apply Finset.measurable_sum Finset.univ
  intro k _
  simpa only [Complex.star_def] using
    (measurable_entry i k).mul (Complex.continuous_conj.measurable.comp (measurable_entry j k))

theorem measurable_density_matrix [Nonempty κ] :
    Measurable (fun U : Frame ι κ => (U.density.matrix : ι → ι → ℂ)) := by
  apply measurable_pi_iff.2
  intro i
  apply measurable_pi_iff.2
  intro j
  have hp : Measurable (fun U : Frame ι κ => U.projector.matrix i j) :=
    (measurable_pi_apply j).comp
      ((measurable_pi_apply i).comp (measurable_projector_matrix (ι := ι) (κ := κ)))
  simpa only [density_matrix, projector_matrix, Matrix.smul_apply, Complex.real_smul]
    using hp.const_mul (((Fintype.card κ : ℝ)⁻¹ : ℝ) : ℂ)

theorem measurable_bottom :
    Measurable (fun U : Frame (κ ⊕ σ) κ => (U.bottom : σ → κ → ℂ)) := by
  apply measurable_pi_iff.2
  intro i
  apply measurable_pi_iff.2
  intro j
  exact measurable_entry (Sum.inr i) j

end Frame

/-- Haar frame distributions are invariant probability measures on the
actual frame space. This definition contains no truncation or chart law. -/
structure IsHaarFrameDistribution (μ : Measure (Frame ι κ)) : Prop where
  probability : IsProbabilityMeasure μ
  row_invariant : ∀ V : Matrix.unitaryGroup ι ℂ,
    Measure.map (fun U : Frame ι κ => U.rotate V) μ = μ

end Paper26.HaarFrames
