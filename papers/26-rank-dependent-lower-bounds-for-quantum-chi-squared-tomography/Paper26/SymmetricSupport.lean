import Paper26.TensorCopies
import Paper26.HaarFrames
import Paper26.TailConvexity

/-! Actual symmetric support for pure tensor inputs in Section 4.
The standard symmetric-projector input specifies its fixed-vector range and
the classical binomial dimension. It contains no Born, success or loss bound.
The pure-input support and effect domination are derived below. -/
noncomputable section
open scoped BigOperators Matrix ComplexOrder

namespace Paper26.SymmetricSupport
open QuantumModel HaarFrames

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def tensorVector (ψ : ι → ℂ) (n : ℕ) (x : Fin n → ι) : ℂ := ∏ i, ψ (x i)

omit [Fintype ι] [DecidableEq ι] in
theorem tensorVector_permutation (ψ : ι → ℂ) (n : ℕ)
    (e : Equiv.Perm (Fin n)) (x : Fin n → ι) :
    tensorVector ψ n (x ∘ e) = tensorVector ψ n x := by
  exact Equiv.prod_comp e (fun i => ψ (x i))

/-- Exact standard symmetric-subspace data (Harrow 2013, Equation (1),
Proposition 1, Theorem 3 and the occupation-number basis discussion;
Proposition 6 subsequently supplies its Haar moment). The input retains
the actual fixed-vector characterization rather than merely assuming that
the P26 input family has a small-dimensional support. -/
structure SymmetricProjectorInput (ι : Type*) [Fintype ι] (n : ℕ) where
  projector : OrthogonalProjector (Fin n → ι)
  fixed_vectors : ∀ z : (Fin n → ι) → ℂ,
    projector.matrix *ᵥ z = z ↔
      ∀ (e : Equiv.Perm (Fin n)) (x : Fin n → ι), z (x ∘ e) = z x
  dimension : projector.matrix.rank = (n + Fintype.card ι - 1).choose n

theorem projector_tensorVector {n : ℕ} (P : SymmetricProjectorInput ι n)
    (ψ : ι → ℂ) : P.projector.matrix *ᵥ tensorVector ψ n = tensorVector ψ n := by
  apply (P.fixed_vectors _).2
  exact tensorVector_permutation ψ n

/-- A one-column frame's actual `n`-copy state is an outer product. -/
theorem frame_tensor_outer (U : Frame ι (Fin 1)) (n : ℕ) :
    (TensorCopies.density U.density n).matrix =
      Matrix.vecMulVec (tensorVector (fun i => U.matrix i 0) n)
        (star (tensorVector (fun i => U.matrix i 0) n)) := by
  ext x y
  simp only [TensorCopies.density_matrix, Frame.density_matrix, Fintype.card_fin,
    Nat.cast_one, inv_one, one_smul, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fin.sum_univ_one, Matrix.vecMulVec_apply, Pi.star_apply, tensorVector,
    Finset.prod_mul_distrib, star_prod]

/-- The actual pure tensor input lies in the specified symmetric range. -/
theorem contains_frame_tensor {n : ℕ} (P : SymmetricProjectorInput ι n)
    (U : Frame ι (Fin 1)) :
    P.projector.matrix * (TensorCopies.density U.density n).matrix =
      (TensorCopies.density U.density n).matrix := by
  rw [frame_tensor_outer, Matrix.mul_vecMulVec, projector_tensorVector]

def frameTensorProjector (U : Frame ι (Fin 1)) (n : ℕ) :
    OrthogonalProjector (Fin n → ι) where
  matrix := (TensorCopies.density U.density n).matrix
  hermitian := (TensorCopies.density U.density n).hermitian
  idempotent := by
    change TensorCopies.matrix U.density.matrix n * TensorCopies.matrix U.density.matrix n = _
    rw [← TensorCopies.matrix_mul]
    have h : U.density.matrix * U.density.matrix = U.density.matrix := by
      simpa only [Frame.density_matrix, Fintype.card_fin, Nat.cast_one, inv_one, one_smul]
        using U.projector.idempotent
    rw [h]
    rfl

/-- The difference of nested orthogonal projections is another orthogonal
projection; in particular it is PSD. -/
theorem projector_difference_psd {η : Type*} [Fintype η] [DecidableEq η]
    (P Q : OrthogonalProjector η) (hPQ : P.matrix * Q.matrix = Q.matrix) :
    (P.matrix - Q.matrix).PosSemidef := by
  have hQP : Q.matrix * P.matrix = Q.matrix := by
    have h := congrArg Matrix.conjTranspose hPQ
    simpa only [Matrix.conjTranspose_mul, P.hermitian.eq, Q.hermitian.eq] using h
  have hHerm : (P.matrix - Q.matrix).IsHermitian := P.hermitian.sub Q.hermitian
  have hIdem : (P.matrix - Q.matrix) * (P.matrix - Q.matrix) = P.matrix - Q.matrix := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, P.idempotent, Q.idempotent, hPQ, hQP]
    abel
  exact (OrthogonalProjector.mk (P.matrix - Q.matrix) hHerm hIdem).positive

/-- The pointwise effect bound used before the posterior concentration
argument in Section 4, with no dimension or success conclusion assumed. -/
theorem frame_tensor_effect_le {n : ℕ} (P : SymmetricProjectorInput ι n)
    (U : Frame ι (Fin 1)) (E : Matrix (Fin n → ι) (Fin n → ι) ℂ)
    (hE : E.PosSemidef) :
    (Matrix.trace ((TensorCopies.density U.density n).matrix * E)).re ≤
      (Matrix.trace (P.projector.matrix * E)).re := by
  have hpos := projector_difference_psd P.projector (frameTensorProjector U n)
    (contains_frame_tensor P U)
  have h := TailConvexity.pairing_nonneg_psd _ E hpos hE
  change 0 ≤ (Matrix.trace ((P.projector.matrix -
    (TensorCopies.density U.density n).matrix) * E)).re at h
  simpa only [Matrix.sub_mul, Matrix.trace_sub, Complex.sub_re, sub_nonneg] using h

end Paper26.SymmetricSupport
