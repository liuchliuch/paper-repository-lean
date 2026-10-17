import Paper26.QuantumModel
import Mathlib.Analysis.Matrix.Order
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Lemma 2.2: tail mass and projector distance

The fidelity, Bures distance, densities, projectors, compressions, traces, and
leading-eigenspace condition below are actual finite complex matrix objects.
The paper-specific inequalities `tailMass <= epsilon` and
`subspaceTail <= 4 * epsilon` are proved here, and do not occur in an input.

The precise standard external inputs are separated into three structures:
* `BuresMetricInput`: the range of root fidelity, the metric symmetry/triangle
  inequality, and the comparison `BuresDistance^2 <= SLDChiSquared`.
  Source: Flammia--O'Donnell, Quantum 8, 1381 (2024), Definition 2.23 and
  Proposition 2.31, https://doi.org/10.22331/q-2024-06-20-1381 ; the actual
  root-fidelity formula is Jozsa, J. Modern Optics 41 (1994), 2315--2323,
  https://doi.org/10.1080/09500349414552171 .
* `CompressionInput`: the nonnegative decreasing eigenvalues of a Hermitian
  compression, their trace and flat-fidelity formulas, and Cauchy interlacing
  against the leading-r compression.  The characteristic polynomial field
  specifies these as eigenvalues of the actual `P sigma P`, including the
  complementary zero eigenvalues.  These are the standard min-max/compression
  theorems (Bhatia, Matrix Analysis, Chapter III, variational principles).
* `PrincipalAngleInput`: the standard CS/principal-angle decomposition for
  two equal-rank orthogonal projectors.  The cosines lie in [0,1], their
  squares are the eigenvalues of actual `P Q P`, and the two raw trace/fidelity
  identities are explicit.  Source: Bjorck--Golub, Math. Comp. 27 (1973),
  579--594, https://doi.org/10.1090/S0025-5718-1973-0348991-3 .

No best-approximation conclusion, epsilon-dependent statement, or tail bound
is an external field.  The full original scalar/spectral argument is proved
from these explicitly quantified standard matrix-theoretic inputs.
-/

noncomputable section
open scoped BigOperators ComplexOrder Matrix MatrixOrder ENNReal

namespace Paper26.TailMass

open QuantumModel

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Uhlmann root fidelity, using the actual positive matrix square roots. -/
def rootFidelity (ρ σ : Density ι) : ℝ :=
  (Matrix.trace (CFC.sqrt (CFC.sqrt ρ.matrix * σ.matrix * CFC.sqrt ρ.matrix))).re

/-- The Bures metric with the normalization used by the paper. -/
def buresDistance (ρ σ : Density ι) : ℝ := Real.sqrt (2 - 2 * rootFidelity ρ σ)

/-- Standard, dimension-independent fidelity/metric facts, retained as exact inputs. -/
structure BuresMetricInput (ι : Type*) [Fintype ι] [DecidableEq ι] : Prop where
  fidelity_range : ∀ ρ σ : Density ι, 0 ≤ rootFidelity ρ σ ∧ rootFidelity ρ σ ≤ 1
  distance_symm : ∀ ρ σ : Density ι, buresDistance ρ σ = buresDistance σ ρ
  distance_triangle : ∀ ρ σ τ : Density ι,
    buresDistance ρ τ ≤ buresDistance ρ σ + buresDistance σ τ
  distance_sq_le_chiB : ∀ ρ σ : Density ι,
    ENNReal.ofReal (buresDistance ρ σ ^ 2) ≤ chiB ρ σ

/-- An actual orthogonal projector with its exact rank stated separately. -/
structure RankProjector (ι : Type*) [Fintype ι] (r : ℕ) where
  projector : OrthogonalProjector ι
  rank_eq : projector.matrix.rank = r

namespace RankProjector

variable {r : ℕ}
abbrev matrix (P : RankProjector ι r) : Matrix ι ι ℂ := P.projector.matrix

def flat (P : RankProjector ι r) (hr : 0 < r) : Density ι :=
  P.projector.flat (P.rank_eq.symm ▸ hr)

end RankProjector

/-- A leading-r eigenspace, allowing any simultaneous spectral basis, including
arbitrary choices within a degenerate eigenspace. -/
def Leading {r : ℕ} (σ : Density ι) (Q : RankProjector ι r) : Prop :=
  ∃ (U : Matrix ι ι ℂ) (a : ι → ℝ) (S : Finset ι),
    Uᴴ * U = 1 ∧ U * Uᴴ = 1 ∧ S.card = r ∧
    σ.matrix = U * Matrix.diagonal (fun i => (a i : ℂ)) * Uᴴ ∧
    Q.matrix = U * Matrix.diagonal (fun i => if i ∈ S then (1 : ℂ) else 0) * Uᴴ ∧
    ∀ i ∈ S, ∀ j ∉ S, a j ≤ a i

/-- Actual mass of sigma outside the leading projector. -/
def tailMass {r : ℕ} (σ : Density ι) (Q : RankProjector ι r) : ℝ :=
  (Matrix.trace ((1 - Q.matrix) * σ.matrix)).re

/-- Actual normalized squared subspace residual from Equation (17). -/
def subspaceTail {r : ℕ} (P Q : RankProjector ι r) : ℝ :=
  (Matrix.trace (P.matrix * (1 - Q.matrix))).re / (r : ℝ)

/-- Exact standard compression spectral data; this does not state either desired bound. -/
structure CompressionInput (ι : Type*) [Fintype ι] [DecidableEq ι] (r : ℕ) where
  values : Density ι → RankProjector ι r → Fin r → ℝ
  nonneg : ∀ σ P i, 0 ≤ values σ P i
  decreasing : ∀ σ P, Antitone (values σ P)
  charpoly : ∀ (σ : Density ι) (P : RankProjector ι r),
    Matrix.charpoly (P.matrix * σ.matrix * P.matrix) =
      Polynomial.X ^ (Fintype.card ι - r) *
        ∏ i : Fin r, (Polynomial.X - Polynomial.C (values σ P i : ℂ))
  trace_eq : ∀ (σ : Density ι) (P : RankProjector ι r), (Matrix.trace (P.matrix * σ.matrix)).re = ∑ i, values σ P i
  flat_fidelity : ∀ (σ : Density ι) (P : RankProjector ι r) (hr : 0 < r),
    rootFidelity (P.flat hr) σ = (∑ i, Real.sqrt (values σ P i)) / Real.sqrt (r : ℝ)
  leading_interlacing : ∀ σ P Q, Leading σ Q → ∀ i, values σ P i ≤ values σ Q i

/-- Exact CS-decomposition identities for actual projectors P and Q. -/
structure PrincipalAngleInput (ι : Type*) [Fintype ι] [DecidableEq ι] (r : ℕ) where
  cosines : RankProjector ι r → RankProjector ι r → Fin r → ℝ
  range : ∀ P Q i, 0 ≤ cosines P Q i ∧ cosines P Q i ≤ 1
  charpoly : ∀ (P Q : RankProjector ι r),
    Matrix.charpoly (P.matrix * Q.matrix * P.matrix) =
      Polynomial.X ^ (Fintype.card ι - r) *
        ∏ i : Fin r, (Polynomial.X - Polynomial.C ((cosines P Q i) ^ 2 : ℂ))
  residual_trace : ∀ P Q,
    subspaceTail P Q = (∑ i, (1 - cosines P Q i ^ 2)) / (r : ℝ)
  flat_fidelity : ∀ (P Q : RankProjector ι r) (hr : 0 < r),
    rootFidelity (P.flat hr) (Q.flat hr) = (∑ i, cosines P Q i) / (r : ℝ)

lemma buresDistance_nonneg (ρ σ : Density ι) : 0 ≤ buresDistance ρ σ := Real.sqrt_nonneg _

lemma buresDistance_sq (F : BuresMetricInput ι) (ρ σ : Density ι) :
    buresDistance ρ σ ^ 2 = 2 - 2 * rootFidelity ρ σ := by
  unfold buresDistance
  exact Real.sq_sqrt (by linarith [(F.fidelity_range ρ σ).2])

/-- A finite chi-squared guarantee gives the unmodified Bures-square guarantee. -/
lemma bures_sq_le_of_chiB (F : BuresMetricInput ι) (ρ σ : Density ι)
    {ε : ℝ} (hε : 0 ≤ ε) (hχ : chiB ρ σ ≤ ENNReal.ofReal ε) :
    buresDistance ρ σ ^ 2 ≤ ε :=
  (ENNReal.ofReal_le_ofReal_iff hε).mp ((F.distance_sq_le_chiB ρ σ).trans hχ)

/-- Scalar Cauchy--Schwarz is applied to the genuine compression eigenvalues. -/
theorem flat_fidelity_sq_le_trace {r : ℕ} (C : CompressionInput ι r)
    (σ : Density ι) (P : RankProjector ι r) (hr : 0 < r) :
    rootFidelity (P.flat hr) σ ^ 2 ≤ (Matrix.trace (P.matrix * σ.matrix)).re := by
  have hrR : (0 : ℝ) < r := Nat.cast_pos.mpr hr
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i : Fin r => Real.sqrt (C.values σ P i)) (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one] at hcs
  simp_rw [Real.sq_sqrt (C.nonneg σ P _)] at hcs
  rw [C.flat_fidelity σ P hr, div_pow, Real.sq_sqrt hrR.le, C.trace_eq σ P]
  exact (div_le_iff₀ hrR).mpr (by simpa [mul_comm] using hcs)

/-- Top-r compression interlacing implies the corresponding root-fidelity ordering. -/
theorem leading_fidelity_maximal {r : ℕ} (C : CompressionInput ι r)
    (σ : Density ι) (P Q : RankProjector ι r) (hr : 0 < r) (hQ : Leading σ Q) :
    rootFidelity (P.flat hr) σ ≤ rootFidelity (Q.flat hr) σ := by
  rw [C.flat_fidelity σ P hr, C.flat_fidelity σ Q hr]
  apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
  exact Finset.sum_le_sum fun i _ => Real.sqrt_le_sqrt (C.leading_interlacing σ P Q hQ i)

/-- The best-flat-state Bures property is derived from the raw eigenvalue interlacing. -/
theorem leading_bures_minimal {r : ℕ} (C : CompressionInput ι r)
    (σ : Density ι) (P Q : RankProjector ι r) (hr : 0 < r) (hQ : Leading σ Q) :
    buresDistance (Q.flat hr) σ ≤ buresDistance (P.flat hr) σ := by
  unfold buresDistance
  apply Real.sqrt_le_sqrt
  linarith [leading_fidelity_maximal C σ P Q hr hQ]

/-- The top-r trace inequality is also derived, without a target tail assumption. -/
theorem leading_trace_maximal {r : ℕ} (C : CompressionInput ι r)
    (σ : Density ι) (P Q : RankProjector ι r) (hQ : Leading σ Q) :
    (Matrix.trace (P.matrix * σ.matrix)).re ≤ (Matrix.trace (Q.matrix * σ.matrix)).re := by
  rw [C.trace_eq σ P, C.trace_eq σ Q]
  exact Finset.sum_le_sum fun i _ => C.leading_interlacing σ P Q hQ i

lemma tailMass_eq_one_sub {r : ℕ} (σ : Density ι) (Q : RankProjector ι r) :
    tailMass σ Q = 1 - (Matrix.trace (Q.matrix * σ.matrix)).re := by
  simp [tailMass, Matrix.sub_mul, Matrix.trace_sub, σ.trace_one]

/-- The principal-angle comparison in the original proof, derived term by term. -/
theorem subspaceTail_le_bures_sq {r : ℕ} (F : BuresMetricInput ι)
    (G : PrincipalAngleInput ι r) (P Q : RankProjector ι r) (hr : 0 < r) :
    subspaceTail P Q ≤ buresDistance (P.flat hr) (Q.flat hr) ^ 2 := by
  have hrR : (0 : ℝ) < r := Nat.cast_pos.mpr hr
  have hs : (∑ i, (1 - G.cosines P Q i ^ 2)) ≤
      ∑ i, 2 * (1 - G.cosines P Q i) := by
    apply Finset.sum_le_sum
    intro i _
    nlinarith [sq_nonneg (1 - G.cosines P Q i)]
  rw [buresDistance_sq F, G.flat_fidelity P Q hr, G.residual_trace P Q]
  calc
    (∑ i, (1 - G.cosines P Q i ^ 2)) / (r : ℝ) ≤
        (∑ i, 2 * (1 - G.cosines P Q i)) / (r : ℝ) :=
      div_le_div_of_nonneg_right hs hrR.le
    _ = 2 - 2 * ((∑ i, G.cosines P Q i) / (r : ℝ)) := by
      rw [← Finset.mul_sum, Finset.sum_sub_distrib]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
      field_simp [ne_of_gt hrR]
      <;> ring

/-- The original tail-mass argument, retaining actual density/projector traces. -/
theorem tailMass_le_epsilon {r : ℕ} (F : BuresMetricInput ι)
    (C : CompressionInput ι r) (σ : Density ι) (P Q : RankProjector ι r)
    (hr : 0 < r) (hQ : Leading σ Q) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 4)
    (hχ : chiB (P.flat hr) σ ≤ ENNReal.ofReal ε) : tailMass σ Q ≤ ε := by
  have hb := bures_sq_le_of_chiB F (P.flat hr) σ hε.le hχ
  rw [buresDistance_sq F] at hb
  have hf : 1 - ε / 2 ≤ rootFidelity (P.flat hr) σ := by linarith
  have hp := flat_fidelity_sq_le_trace C σ P hr
  have hm := leading_trace_maximal C σ P Q hQ
  have hprod : 0 ≤ (rootFidelity (P.flat hr) σ - (1 - ε / 2)) *
      (rootFidelity (P.flat hr) σ + (1 - ε / 2)) :=
    mul_nonneg (sub_nonneg.mpr hf) (by linarith [(F.fidelity_range (P.flat hr) σ).1])
  rw [tailMass_eq_one_sub]
  nlinarith [sq_nonneg (ε / 2)]

/-- The subspace bound uses only the proved best-flat property, metric triangle,
and the proved principal-angle scalar comparison. -/
theorem subspaceTail_le_four_epsilon {r : ℕ} (F : BuresMetricInput ι)
    (C : CompressionInput ι r) (G : PrincipalAngleInput ι r)
    (σ : Density ι) (P Q : RankProjector ι r) (hr : 0 < r) (hQ : Leading σ Q)
    {ε : ℝ} (hε : 0 ≤ ε) (hχ : chiB (P.flat hr) σ ≤ ENNReal.ofReal ε) :
    subspaceTail P Q ≤ 4 * ε := by
  have hb := bures_sq_le_of_chiB F (P.flat hr) σ hε hχ
  have hbest := leading_bures_minimal C σ P Q hr hQ
  have htriangle := F.distance_triangle (P.flat hr) σ (Q.flat hr)
  rw [F.distance_symm σ (Q.flat hr)] at htriangle
  have htwo : buresDistance (P.flat hr) (Q.flat hr) ≤ 2 * buresDistance (P.flat hr) σ :=
    by linarith
  have hpq := buresDistance_nonneg (P.flat hr) (Q.flat hr)
  have hps := buresDistance_nonneg (P.flat hr) σ
  have hsquare : 0 ≤ (2 * buresDistance (P.flat hr) σ -
      buresDistance (P.flat hr) (Q.flat hr)) *
      (2 * buresDistance (P.flat hr) σ + buresDistance (P.flat hr) (Q.flat hr)) :=
    mul_nonneg (sub_nonneg.mpr htwo) (by positivity)
  have ht := subspaceTail_le_bures_sq F G P Q hr
  nlinarith

/-- Lemma 2.2 under precisely the explicit standard external matrix facts above. -/
theorem lemma_2_2_bures {r : ℕ} (F : BuresMetricInput ι)
    (C : CompressionInput ι r) (G : PrincipalAngleInput ι r)
    (σ : Density ι) (P Q : RankProjector ι r) (hr : 0 < r) (hQ : Leading σ Q)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 4)
    (hχ : chiB (P.flat hr) σ ≤ ENNReal.ofReal ε) :
    tailMass σ Q ≤ ε ∧ subspaceTail P Q ≤ 4 * ε :=
  ⟨tailMass_le_epsilon F C σ P Q hr hQ hε hε1 hχ,
    subspaceTail_le_four_epsilon F C G σ P Q hr hQ hε.le hχ⟩

/-- The right-inverse assertion follows from the already-proved actual loss ordering. -/
theorem lemma_2_2_right {r : ℕ} (F : BuresMetricInput ι)
    (C : CompressionInput ι r) (G : PrincipalAngleInput ι r)
    (σ : Density ι) (P Q : RankProjector ι r) (hr : 0 < r) (hQ : Leading σ Q)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 4)
    (hχ : chiR (P.flat hr) σ ≤ ENNReal.ofReal ε) :
    tailMass σ Q ≤ ε ∧ subspaceTail P Q ≤ 4 * ε := by
  apply lemma_2_2_bures F C G σ P Q hr hQ hε hε1
  exact ((loss_comparison (P.flat hr) σ).1.trans (loss_comparison (P.flat hr) σ).2).trans hχ

end Paper26.TailMass
