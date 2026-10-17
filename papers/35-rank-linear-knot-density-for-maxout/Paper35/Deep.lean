import Paper35.Basic
import Paper35.Rank
import Mathlib.Probability.Moments.Variance
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Real.StarOrdered
import Mathlib.Data.Real.ENatENNReal
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Section 8: rigorously isolated algebra and counting steps

This file proves the finite union argument and the iteration of one-step
length/switch bounds.  These are auxiliary results: the conditional one-step
bounds for random Maxout networks are not asserted here.

It also proves the deterministic positive-semidefinite comparison for the
matrix on the right of (8.15).  No Gaussian regression or winner-selection
identity is assumed to be the conclusion of Proposition 8.2.
-/

open scoped BigOperators ENNReal
open MeasureTheory Matrix

namespace Paper35.Deep

/-- Product of incoming length multipliers, with layers indexed from zero. -/
noncomputable def lengthProduct (A : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∏ h ∈ Finset.range n, A h

/-- The coefficient in the right side of the switch propagation formula. -/
noncomputable def switchCoefficient (A D : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ h ∈ Finset.range n, D h * lengthProduct A h

/-- The deterministic induction used in (8.6), with explicit one-step premises. -/
theorem length_recursion (A L : ℕ → ℝ)
    (hA : ∀ n, 0 ≤ A n) (hstep : ∀ n, L (n + 1) ≤ A n * L n) :
    ∀ n, L n ≤ L 0 * lengthProduct A n := by
  intro n
  induction n with
  | zero => simp [lengthProduct]
  | succ n ih =>
    calc
      L (n + 1) ≤ A n * L n := hstep n
      _ ≤ A n * (L 0 * lengthProduct A n) := mul_le_mul_of_nonneg_left ih (hA n)
      _ = L 0 * lengthProduct A (n + 1) := by
        simp [lengthProduct, Finset.prod_range_succ]
        ring

/-- The deterministic sum-product iteration in (8.7)/(8.19).
The probabilistic and differential one-step estimates are explicit premises. -/
theorem switch_recursion (A D L S : ℕ → ℝ)
    (hA : ∀ n, 0 ≤ A n) (hD : ∀ n, 0 ≤ D n)
    (hL : ∀ n, L (n + 1) ≤ A n * L n)
    (hS0 : S 0 = 0) (hS : ∀ n, S (n + 1) ≤ S n + D n * L n) :
    ∀ n, S n ≤ L 0 * switchCoefficient A D n := by
  intro n
  induction n with
  | zero => simp [hS0, switchCoefficient]
  | succ n ih =>
    have hlen := length_recursion A L hA hL n
    calc
      S (n + 1) ≤ S n + D n * L n := hS n
      _ ≤ L 0 * switchCoefficient A D n + D n * (L 0 * lengthProduct A n) :=
        add_le_add ih (mul_le_mul_of_nonneg_left hlen (hD n))
      _ = L 0 * switchCoefficient A D (n + 1) := by
        simp [switchCoefficient, Finset.sum_range_succ]
        ring

/-- Union of actual parameter sets; unlike a finite-list representation, this
also preserves the possibility of infinitely many switches. -/
def allSwitchTimes {ι α : Type*} (S : ι → Set α) : Set α := ⋃ i, S i

/-- Number of distinct parameter values, in the extended nonnegative reals. -/
noncomputable def allSwitchCount {ι α : Type*} (S : ι → Set α) : ℝ≥0∞ :=
  (allSwitchTimes S).encard

/-- The distinct-time union bound, valid even if some counts are infinite. -/
theorem allSwitchCount_le {ι α : Type*} [Fintype ι] (S : ι → Set α) :
    allSwitchCount S ≤ ∑ i, ((S i).encard : ℝ≥0∞) := by
  have he := ENat.toENNReal_mono (Set.encard_iUnion_le_of_fintype S)
  calc
    allSwitchCount S ≤ ((∑ i, (S i).encard : ℕ∞) : ℝ≥0∞) := he
    _ = _ := map_sum ENat.toENNRealRingHom (fun i => (S i).encard) Finset.univ

/-- Extended expected distinct count is at most the sum of marginal expected
counts.  Same-layer units need not be independent. -/
theorem expected_allSwitchCount_le {Ω ι α : Type*}
    [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) (S : Ω → ι → Set α)
    (hi : ∀ i, Measurable (fun ω => ((S ω i).encard : ℝ≥0∞))) :
    (∫⁻ ω, allSwitchCount (S ω) ∂μ) ≤
      ∑ i, ∫⁻ ω, ((S ω i).encard : ℝ≥0∞) ∂μ := by
  calc
    _ ≤ ∫⁻ ω, ∑ i, ((S ω i).encard : ℝ≥0∞) ∂μ :=
      lintegral_mono (fun ω => allSwitchCount_le (S ω))
    _ = _ := lintegral_finset_sum _ (fun i _ => hi i)

/-- The union count of Definition (8.5), with all unit scores evaluated in
the original path parameter.  The finite index may encode layers and units. -/
noncomputable def jointSwitchCount {ι : Type*} (K : ι → ℕ)
    (f : (i : ι) → Fin (K i) → ℝ → ℝ) (L : ℝ) : ℝ≥0∞ :=
  allSwitchCount (fun i => Paper35.switchSet (f i) L)

/-- Source-semantic version of the distinct-time union bound.  Marginal
expected counts may be infinite and units may be dependent. -/
theorem expected_jointSwitchCount_le {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) (K : ι → ℕ)
    (f : Ω → (i : ι) → Fin (K i) → ℝ → ℝ) (L : ℝ)
    (hi : ∀ i, Measurable (fun ω => Paper35.switchCount (f ω i) L)) :
    (∫⁻ ω, jointSwitchCount K (f ω) L ∂μ) ≤
      ∑ i, Paper35.expectedSwitchCount μ (fun ω => f ω i) L := by
  exact expected_allSwitchCount_le μ (fun ω i => Paper35.switchSet (f ω i) L) hi

/-- All distinct times from a finite collection of units/layers. -/
def distinctSwitchTimes {ι α : Type*} [Fintype ι] [DecidableEq α]
    (S : ι → Finset α) : Finset α := Finset.univ.biUnion S

/-- Simultaneous switches count only once, as required by (8.5). -/
theorem distinctSwitchTimes_card_le {ι α : Type*} [Fintype ι] [DecidableEq α]
    (S : ι → Finset α) :
    (distinctSwitchTimes S).card ≤ ∑ i, (S i).card := by
  exact Finset.card_biUnion_le

/-- The union argument is valid without independence between units. -/
theorem integral_distinctSwitchTimes_le {Ω ι α : Type*}
    [MeasurableSpace Ω] [Fintype ι] [DecidableEq α]
    (μ : Measure Ω) (S : Ω → ι → Finset α)
    (hu : Integrable (fun ω => ((distinctSwitchTimes (S ω)).card : ℝ)) μ)
    (hi : ∀ i, Integrable (fun ω => ((S ω i).card : ℝ)) μ) :
    (∫ ω, ((distinctSwitchTimes (S ω)).card : ℝ) ∂μ) ≤
      ∑ i, ∫ ω, ((S ω i).card : ℝ) ∂μ := by
  calc
    _ ≤ ∫ ω, ∑ i, ((S ω i).card : ℝ) ∂μ := by
      apply integral_mono hu (integrable_finset_sum _ (fun i _ => hi i))
      intro ω
      change ((distinctSwitchTimes (S ω)).card : ℝ) ≤ ∑ i, ((S ω i).card : ℝ)
      have hnat := distinctSwitchTimes_card_le (S ω)
      have hreal : ((distinctSwitchTimes (S ω)).card : ℝ) ≤ ((∑ i, (S ω i).card : ℕ) : ℝ) :=
        Nat.cast_le.mpr hnat
      simpa only [Nat.cast_sum] using hreal
    _ = _ := integral_finset_sum _ (fun i _ => hi i)

/-- The elementary maximum-to-sum estimate used in (8.9). -/
theorem max_square_le_sum {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (a : ι → ℝ) : s.sup' hs (fun j => |a j| ^ 2) ≤ ∑ j ∈ s, |a j| ^ 2 := by
  apply Finset.sup'_le
  intro j hj
  exact Finset.single_le_sum (fun k _ => sq_nonneg (|a k|)) hj

/-- Quadratic form associated with a real covariance matrix. -/
def covarianceForm {ι : Type*} [Fintype ι]
    (C : Matrix ι ι ℝ) (v w : ι → ℝ) : ℝ := v ⬝ᵥ (C *ᵥ w)

/-- Cauchy--Schwarz for a positive semidefinite covariance matrix. -/
theorem covariance_cauchy_schwarz {ι : Type*} [Fintype ι]
    {C : Matrix ι ι ℝ} (hC : C.PosSemidef) (v z : ι → ℝ) :
    covarianceForm C v z ^ 2 ≤ covarianceForm C v v * covarianceForm C z z := by
  have hs : covarianceForm C z v = covarianceForm C v z := by
    have hm : Cᵀ = C := by simpa only [Matrix.conjTranspose, star_trivial] using hC.1
    dsimp [covarianceForm]
    rw [← hm, Matrix.mulVec_transpose, dotProduct_comm]
    rw [Matrix.dotProduct_mulVec, hm]
  have hp (t : ℝ) : 0 ≤ covarianceForm C z z * (t * t) +
      (2 * covarianceForm C v z) * t + covarianceForm C v v := by
    have hn := hC.2 (v + t • z)
    simp only [star_trivial] at hn
    simp only [covarianceForm, Matrix.mulVec_add, Matrix.mulVec_smul,
      dotProduct_add, add_dotProduct, dotProduct_smul, smul_dotProduct,
      smul_eq_mul] at *
    rw [hs] at hn
    nlinarith [hn]
  have hd := discrim_le_zero hp
  dsimp [discrim] at hd
  nlinarith

/-- Rank-one term P(z) in the proof of Proposition 8.2. -/
noncomputable def rankCorrection {ι : Type*} [Fintype ι]
    (C : Matrix ι ι ℝ) (z : ι → ℝ) (s : ℝ) : Matrix ι ι ℝ :=
  s⁻¹ • Matrix.vecMulVec (C *ᵥ z) (C *ᵥ z)

/-- The proposed active-weight covariance Q from (8.15), as a deterministic matrix. -/
noncomputable def activeSecondMomentMatrix {ι : Type*} [Fintype ι]
    (C : Matrix ι ι ℝ) (z : ι → ℝ) (s m₂ : ℝ) : Matrix ι ι ℝ :=
  C + (m₂ - 1) • rankCorrection C z s

/-- Quadratic form of the rank-one correction, without any probabilistic hypothesis. -/
theorem rankCorrection_form {ι : Type*} [Fintype ι]
    (C : Matrix ι ι ℝ) (z v : ι → ℝ) (s : ℝ) :
    covarianceForm (rankCorrection C z s) v v = covarianceForm C v z ^ 2 / s := by
  simp [covarianceForm, rankCorrection, Matrix.smul_mulVec, Matrix.vecMulVec_mulVec,
    dotProduct_smul, smul_eq_mul, dotProduct_comm, pow_two, div_eq_mul_inv]
  ring

/-- The directional form of the deterministic matrix expression in (8.15). -/
theorem activeSecondMomentMatrix_form {ι : Type*} [Fintype ι]
    (C : Matrix ι ι ℝ) (z v : ι → ℝ) (s m₂ : ℝ) :
    covarianceForm (activeSecondMomentMatrix C z s m₂) v v =
      covarianceForm C v v + (m₂ - 1) * (covarianceForm C v z ^ 2 / s) := by
  simp only [activeSecondMomentMatrix, covarianceForm, Matrix.add_mulVec,
    Matrix.smul_mulVec, dotProduct_add, dotProduct_smul, smul_eq_mul]
  change covarianceForm C v v + (m₂ - 1) * covarianceForm (rankCorrection C z s) v v = _
  rw [rankCorrection_form]
  rfl

/-- At z = 0 the deterministic correction vanishes, for every rank moment. -/
theorem activeSecondMomentMatrix_zero {ι : Type*} [Fintype ι]
    (C : Matrix ι ι ℝ) (s m₂ : ℝ) :
    activeSecondMomentMatrix C 0 s m₂ = C := by
  simp [activeSecondMomentMatrix, rankCorrection]

/-- The substantive deterministic comparison 0 ≤ vᵀP(z)v ≤ vᵀCv. -/
theorem rankCorrection_quadratic_bounds {ι : Type*} [Fintype ι]
    {C : Matrix ι ι ℝ} (hC : C.PosSemidef) (z v : ι → ℝ)
    {σ : ℝ} (hσ : 0 < σ) :
    0 ≤ covarianceForm (rankCorrection C z (σ ^ 2 + covarianceForm C z z)) v v ∧
      covarianceForm (rankCorrection C z (σ ^ 2 + covarianceForm C z z)) v v ≤
        covarianceForm C v v := by
  have hv : 0 ≤ covarianceForm C v v := by simpa [covarianceForm] using hC.2 v
  have hz : 0 ≤ covarianceForm C z z := by simpa [covarianceForm] using hC.2 z
  have hs : 0 < σ ^ 2 + covarianceForm C z z := by positivity
  rw [rankCorrection_form]
  constructor
  · positivity
  · apply (div_le_iff₀ hs).2
    have hcs := covariance_cauchy_schwarz hC v z
    nlinarith [mul_nonneg hv (sq_nonneg σ)]

/-- The Q ≤ max(1,m₂)C comparison in Proposition 8.2, in every direction.
It follows solely from C ⪰ 0 and σ > 0. -/
theorem activeSecondMomentMatrix_quadratic_le {ι : Type*} [Fintype ι]
    {C : Matrix ι ι ℝ} (hC : C.PosSemidef) (z v : ι → ℝ)
    {σ : ℝ} (hσ : 0 < σ) (m₂ : ℝ) :
    covarianceForm (activeSecondMomentMatrix C z
      (σ ^ 2 + covarianceForm C z z) m₂) v v ≤
        max 1 m₂ * covarianceForm C v v := by
  have hp := rankCorrection_quadratic_bounds hC z v hσ
  simp only [activeSecondMomentMatrix, covarianceForm, Matrix.add_mulVec,
    Matrix.smul_mulVec, dotProduct_add, dotProduct_smul, smul_eq_mul]
  change covarianceForm C v v + (m₂ - 1) *
    covarianceForm (rankCorrection C z (σ ^ 2 + covarianceForm C z z)) v v ≤
      max 1 m₂ * covarianceForm C v v
  by_cases hm : 1 ≤ m₂
  · rw [max_eq_right hm]
    nlinarith [mul_nonneg (sub_nonneg.mpr hm) (sub_nonneg.mpr hp.2)]
  · rw [max_eq_left (le_of_not_ge hm)]
    nlinarith [mul_nonpos_of_nonpos_of_nonneg (by linarith : m₂ - 1 ≤ 0) hp.1]

/-- The rank-one matrix itself is positive semidefinite. -/
theorem rankCorrection_posSemidef {ι : Type*} [Fintype ι]
    (C : Matrix ι ι ℝ) (z : ι → ℝ) {s : ℝ} (hs : 0 ≤ s) :
    (rankCorrection C z s).PosSemidef := by
  have ho := Matrix.posSemidef_vecMulVec_self_star (C *ᵥ z)
  simpa only [star_trivial] using ho.smul (inv_nonneg.mpr hs)

/-- The matrix inequality P(z) ⪯ C, in the standard PSD-difference meaning. -/
theorem rankCorrection_sub_posSemidef {ι : Type*} [Fintype ι]
    {C : Matrix ι ι ℝ} (hC : C.PosSemidef) (z : ι → ℝ)
    {σ : ℝ} (hσ : 0 < σ) :
    (C - rankCorrection C z (σ ^ 2 + covarianceForm C z z)).PosSemidef := by
  have hz : 0 ≤ covarianceForm C z z := by simpa [covarianceForm] using hC.2 z
  have hp := rankCorrection_posSemidef C z (by positivity :
    0 ≤ σ ^ 2 + covarianceForm C z z)
  refine ⟨hC.1.sub hp.1, ?_⟩
  intro v
  have hb := (rankCorrection_quadratic_bounds hC z v hσ).2
  simpa only [covarianceForm, star_trivial, Matrix.sub_mulVec, dotProduct_sub,
    sub_nonneg] using hb

/-- The proposed second moment matrix Q is positive semidefinite for m₂ ≥ 0. -/
theorem activeSecondMomentMatrix_posSemidef {ι : Type*} [Fintype ι]
    {C : Matrix ι ι ℝ} (hC : C.PosSemidef) (z : ι → ℝ)
    {σ m₂ : ℝ} (hσ : 0 < σ) (hm : 0 ≤ m₂) :
    (activeSecondMomentMatrix C z (σ ^ 2 + covarianceForm C z z) m₂).PosSemidef := by
  have hz : 0 ≤ covarianceForm C z z := by simpa [covarianceForm] using hC.2 z
  have hp := rankCorrection_posSemidef C z (by positivity :
    0 ≤ σ ^ 2 + covarianceForm C z z)
  have hs := rankCorrection_sub_posSemidef hC z hσ
  have he : activeSecondMomentMatrix C z (σ ^ 2 + covarianceForm C z z) m₂ =
      m₂ • rankCorrection C z (σ ^ 2 + covarianceForm C z z) +
        (C - rankCorrection C z (σ ^ 2 + covarianceForm C z z)) := by
    ext i j
    simp only [activeSecondMomentMatrix, Matrix.add_apply, Matrix.smul_apply,
      Matrix.sub_apply, smul_eq_mul]
    ring
  rw [he]
  exact (hp.smul hm).add hs

/-- Q(z) ⪯ max(1,m₂) C as a genuine standard matrix PSD statement. -/
theorem activeSecondMomentMatrix_domination {ι : Type*} [Fintype ι]
    {C : Matrix ι ι ℝ} (hC : C.PosSemidef) (z : ι → ℝ)
    {σ : ℝ} (hσ : 0 < σ) (m₂ : ℝ) :
    (max 1 m₂ • C -
      activeSecondMomentMatrix C z (σ ^ 2 + covarianceForm C z z) m₂).PosSemidef := by
  by_cases hm : 1 ≤ m₂
  · rw [max_eq_right hm]
    have he : m₂ • C - activeSecondMomentMatrix C z
        (σ ^ 2 + covarianceForm C z z) m₂ =
        (m₂ - 1) • (C - rankCorrection C z (σ ^ 2 + covarianceForm C z z)) := by
      ext i j
      simp only [activeSecondMomentMatrix, Matrix.add_apply, Matrix.smul_apply,
        Matrix.sub_apply, smul_eq_mul]
      ring
    rw [he]
    exact (rankCorrection_sub_posSemidef hC z hσ).smul (sub_nonneg.mpr hm)
  · rw [max_eq_left (le_of_not_ge hm)]
    have he : (1 : ℝ) • C - activeSecondMomentMatrix C z
        (σ ^ 2 + covarianceForm C z z) m₂ =
        (1 - m₂) • rankCorrection C z (σ ^ 2 + covarianceForm C z z) := by
      ext i j
      simp only [activeSecondMomentMatrix, Matrix.add_apply, Matrix.smul_apply,
        Matrix.sub_apply, smul_eq_mul]
      ring
    rw [he]
    have hz : 0 ≤ covarianceForm C z z := by simpa [covarianceForm] using hC.2 z
    exact (rankCorrection_posSemidef C z (by positivity)).smul (by linarith)

/-- The mean-square lower bound used in (8.16), for any square-integrable law. -/
theorem mean_square_le_second_moment {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ)
    (hX : MemLp X 2 μ) :
    (∫ ω, X ω ∂μ) ^ 2 ≤ ∫ ω, (X ω) ^ 2 ∂μ := by
  have hn := ProbabilityTheory.variance_nonneg X μ
  rw [ProbabilityTheory.variance_eq_sub hX] at hn
  simpa only [Pi.pow_apply, sub_nonneg] using hn

/-- Jensen's lower bound in the normalization c = E[M]/sqrt(pi), as in (8.16).
Instantiation at the Gaussian maximum still requires its square integrability. -/
theorem normalized_mean_square_lower {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ)
    (hX : MemLp X 2 μ) :
    Real.pi * ((∫ ω, X ω ∂μ) / Real.sqrt Real.pi) ^ 2 ≤
      ∫ ω, (X ω) ^ 2 ∂μ := by
  have hs : (Real.sqrt Real.pi) ^ 2 = Real.pi := Real.sq_sqrt Real.pi_pos.le
  have hne : Real.sqrt Real.pi ≠ 0 := ne_of_gt (Real.sqrt_pos.2 Real.pi_pos)
  have he : Real.pi * ((∫ ω, X ω ∂μ) / Real.sqrt Real.pi) ^ 2 =
      (∫ ω, X ω ∂μ) ^ 2 := by
    rw [div_pow, hs]
    exact mul_div_cancel₀ _ Real.pi_ne_zero
  rw [he]
  exact mean_square_le_second_moment μ X hX

/-- The actual second moment of the maximum of K iid standard normal variables. -/
noncomputable def gaussianMaxSecondMoment : ℕ → ℝ
  | 0 => 0
  | n + 1 => ∫ x, (Paper35.prefixMax n x) ^ 2 ∂Paper35.standardNormalSequence

/-- The Gaussian length correction q_K in (8.14). -/
noncomputable def gaussianLengthCorrection (K : ℕ) : ℝ :=
  max 1 (gaussianMaxSecondMoment K)

theorem gaussianMaxSecondMoment_nonneg (K : ℕ) :
    0 ≤ gaussianMaxSecondMoment K := by
  cases K with
  | zero => rfl
  | succ n => exact integral_nonneg (fun x => sq_nonneg _)

/-- The left half of (8.16), for the paper's actual iid Gaussian maximum. -/
theorem gaussian_rank_second_moment_lower (K : ℕ) :
    Real.pi * Paper35.gaussianRankCoefficient K ^ 2 ≤ gaussianMaxSecondMoment K := by
  cases K with
  | zero => simp [Paper35.gaussianRankCoefficient, Paper35.gaussianMaxMean,
      gaussianMaxSecondMoment]
  | succ n =>
    exact normalized_mean_square_lower Paper35.standardNormalSequence
      (Paper35.prefixMax n) (Paper35.memLp_prefixMax n 2)

theorem gaussianMaxSecondMoment_le_lengthCorrection (K : ℕ) :
    gaussianMaxSecondMoment K ≤ gaussianLengthCorrection K := le_max_right _ _

theorem gaussianLengthCorrection_ge_one (K : ℕ) :
    1 ≤ gaussianLengthCorrection K := le_max_left _ _

/-- The PSD comparison in Proposition 8.2, with its actual Gaussian rank moment.
The separate identification with the selected weight's moment is not asserted. -/
theorem gaussian_secondMomentMatrix_domination {ι : Type*} [Fintype ι]
    {C : Matrix ι ι ℝ} (hC : C.PosSemidef) (z : ι → ℝ)
    {σ : ℝ} (hσ : 0 < σ) (K : ℕ) :
    (gaussianLengthCorrection K • C -
      activeSecondMomentMatrix C z (σ ^ 2 + covarianceForm C z z)
        (gaussianMaxSecondMoment K)).PosSemidef :=
  activeSecondMomentMatrix_domination hC z hσ _

/-- Positive semidefiniteness of the Gaussian rank moment expression. -/
theorem gaussian_secondMomentMatrix_posSemidef {ι : Type*} [Fintype ι]
    {C : Matrix ι ι ℝ} (hC : C.PosSemidef) (z : ι → ℝ)
    {σ : ℝ} (hσ : 0 < σ) (K : ℕ) :
    (activeSecondMomentMatrix C z (σ ^ 2 + covarianceForm C z z)
      (gaussianMaxSecondMoment K)).PosSemidef :=
  activeSecondMomentMatrix_posSemidef hC z hσ (gaussianMaxSecondMoment_nonneg K)

end Paper35.Deep
