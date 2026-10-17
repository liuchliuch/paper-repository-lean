import Paper08.Integral
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.InformationTheory.Hamming
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Actual exponential partition functions and the zero-free prerequisites

`Q E B z` is the complex Bochner integral in equation (2.1), with local factors
pulled back along their labelled scopes. The theorems in this file establish
its normalization, its identification with the real partition function, and
the range, dependence, and Hamming-Lipschitz prerequisites for Lemma 2.1.

The elementary non-vanishing result at the end has an explicit dependence on
`B.card`. The common disk in Lemma 2.1 is established separately by the
actual partial-expectation induction in ZeroFreeInduction and CubeZeroFreeMain.
-/

set_option maxHeartbeats 800000

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Paper08
namespace ZeroFree

open Integral

lemma isCompact_cube (k : ℕ) : IsCompact (cube k) := by
  exact isCompact_univ_pi fun _ => isCompact_Icc

/-- The Euclidean Lipschitz promise implies continuity in the ordinary product
 topology. This proves continuity rather than adding it to the model. -/
theorem continuousOn_of_lip {k : ℕ} (f : LocalFunc k) {K : ℝ}
    (hf : f.LipLe K) : ContinuousOn f.toFun (cube k) := by
  have hEucl : LipschitzOnWith (Real.toNNReal K)
      (fun x : EuclideanSpace ℝ (Fin k) => f.toFun (fun i => x i))
      (euclCube k) := by
    apply LipschitzOnWith.of_dist_le'
    intro x hx y hy
    simpa only [Real.dist_eq, dist_eq_norm, Real.norm_eq_abs, euclDist, euclNorm] using
      hf (fun i => x i) (fun i => y i) hx hy
  exact hEucl.continuousOn.comp
    (PiLp.continuous_toLp 2 (fun _ : Fin k => ℝ)).continuousOn
    (fun x hx => mem_cube.mp hx)

lemma restrictTo_mem_cube {n : ℕ} (s : Finset (Fin n))
    {x : Fin n → ℝ} (hx : x ∈ cube n) : restrictTo s x ∈ cube s.card := by
  exact mem_cube.mpr fun i => mem_cube.mp hx (s.orderEmbOfFin rfl i)

lemma continuous_restrictTo {n : ℕ} (s : Finset (Fin n)) :
    Continuous (restrictTo s) := by
  exact continuous_pi fun i => continuous_apply _

/-- Ambient real log-factor. -/
def ell {n r : ℕ} (e : Factor n r) (x : Fin n → ℝ) : ℝ :=
  e.ell.toFun (restrictTo e.scope x)

lemma ell_range {n r : ℕ} (e : Factor n r) {q : ℝ}
    (he : e.RangeOk q) {x : Fin n → ℝ} (hx : x ∈ cube n) :
    0 ≤ ell e x ∧ ell e x ≤ q := by
  have hx' := mem_cube.mp (restrictTo_mem_cube e.scope hx)
  have hlow := he.2 (restrictTo e.scope x) hx'
  have hpos : 0 < e.psi.toFun (restrictTo e.scope x) := lt_of_lt_of_le zero_lt_one hlow
  have hupp : e.psi.toFun (restrictTo e.scope x) ≤ Real.exp q :=
    (le_abs_self _).trans (he.1 _ hx')
  refine ⟨Real.log_nonneg hlow, ?_⟩
  exact (Real.log_le_iff_le_exp hpos).mpr hupp

lemma logFactor_lip {n r : ℕ} (e : Factor n r) {q K : ℝ}
    (he : e.RangeOk q) (hLip : e.LipOk K) : e.ell.LipLe K := by
  intro x y hx hy
  exact (Paper08.log_abs_sub_le_abs_sub (he.2 x hx) (he.2 y hy)).trans
    (hLip x y hx hy)

lemma continuousOn_ell {n r : ℕ} (e : Factor n r) {q K : ℝ}
    (he : e.RangeOk q) (hLip : e.LipOk K) : ContinuousOn (ell e) (cube n) := by
  exact (continuousOn_of_lip e.ell (logFactor_lip e he hLip)).comp
    (continuous_restrictTo e.scope).continuousOn
    (fun _ hx => restrictTo_mem_cube e.scope hx)

/-- An ambient log-factor depends only on its declared scope. -/
lemma ell_dependsOn_scope {n r : ℕ} (e : Factor n r) {x y : Fin n → ℝ}
    (hxy : ∀ v ∈ e.scope, x v = y v) : ell e x = ell e y := by
  unfold ell
  congr 1
  funext i
  exact hxy _ (e.scope.orderEmbOfFin_mem rfl i)

/-- Normalization used in the application of Barvinok's theorem. -/
def normalizedEll {n r : ℕ} (e : Factor n r) (q : ℝ) (x : Fin n → ℝ) : ℝ :=
  ell e x / q

lemma normalizedEll_range {n r : ℕ} (e : Factor n r) {q : ℝ}
    (hq : 0 < q) (he : e.RangeOk q) {x : Fin n → ℝ} (hx : x ∈ cube n) :
    0 ≤ normalizedEll e q x ∧ normalizedEll e q x ≤ 1 := by
  rcases ell_range e he hx with ⟨h₀, h₁⟩
  exact ⟨div_nonneg h₀ hq.le, (div_le_one hq).mpr h₁⟩

/-- The range `[0,1]` gives the pointwise oscillation bound, independently of
 any metric regularity assumption. -/
lemma normalizedEll_oscillation {n r : ℕ} (e : Factor n r) {q : ℝ}
    (hq : 0 < q) (he : e.RangeOk q) {x y : Fin n → ℝ}
    (hx : x ∈ cube n) (hy : y ∈ cube n) :
    |normalizedEll e q x - normalizedEll e q y| ≤ 1 := by
  rcases normalizedEll_range e hq he hx with ⟨hx₀, hx₁⟩
  rcases normalizedEll_range e hq he hy with ⟨hy₀, hy₁⟩
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Hence the normalized real log-factor is 1-Lipschitz for Hamming distance
 on the cube, exactly as used in the paper. -/
lemma normalizedEll_hamming {n r : ℕ} (e : Factor n r) {q : ℝ}
    (hq : 0 < q) (he : e.RangeOk q) {x y : Fin n → ℝ}
    (hx : x ∈ cube n) (hy : y ∈ cube n) :
    |normalizedEll e q x - normalizedEll e q y| ≤ (hammingDist x y : ℝ) := by
  classical
  by_cases hxy : x = y
  · subst y
    simp
  · have hH : 1 ≤ hammingDist x y := (hammingDist_pos.mpr hxy)
    have hH' : (1 : ℝ) ≤ (hammingDist x y : ℝ) := by exact_mod_cast hH
    exact (normalizedEll_oscillation e hq he hx hy).trans hH'

/-- Sum of the real log-factors in a subcollection. -/
def sumEll {n r : ℕ} {ι : Type*} (E : ι → Factor n r) (B : Finset ι)
    (x : Fin n → ℝ) : ℝ := ∑ i ∈ B, ell (E i) x

lemma sumEll_range {n r : ℕ} {ι : Type*} (E : ι → Factor n r)
    (B : Finset ι) {q : ℝ} (hE : ∀ i ∈ B, (E i).RangeOk q)
    {x : Fin n → ℝ} (hx : x ∈ cube n) :
    0 ≤ sumEll E B x ∧ sumEll E B x ≤ B.card * q := by
  constructor
  · exact Finset.sum_nonneg fun i hi => (ell_range (E i) (hE i hi) hx).1
  · calc
      sumEll E B x ≤ ∑ _i ∈ B, q := Finset.sum_le_sum fun i hi =>
        (ell_range (E i) (hE i hi) hx).2
      _ = B.card * q := by simp

lemma continuousOn_sumEll {n r : ℕ} {ι : Type*} (E : ι → Factor n r)
    (B : Finset ι) {q K : ℝ} (hE : ∀ i ∈ B, (E i).RangeOk q)
    (hLip : ∀ i ∈ B, (E i).LipOk K) : ContinuousOn (sumEll E B) (cube n) := by
  exact continuousOn_finset_sum B fun i hi => continuousOn_ell (E i) (hE i hi) (hLip i hi)

/-- The complex partition function of equation (2.1), as an actual integral. -/
def Q {n r : ℕ} {ι : Type*} (E : ι → Factor n r) (B : Finset ι) (z : ℂ) : ℂ :=
  ∫ x in cube n, Complex.exp (z * (sumEll E B x : ℂ))

lemma continuousOn_integrand {n r : ℕ} {ι : Type*} (E : ι → Factor n r)
    (B : Finset ι) {q K : ℝ} (hE : ∀ i ∈ B, (E i).RangeOk q)
    (hLip : ∀ i ∈ B, (E i).LipOk K) (z : ℂ) :
    ContinuousOn (fun x => Complex.exp (z * (sumEll E B x : ℂ))) (cube n) := by
  exact Complex.continuous_exp.comp_continuousOn
    (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn
      (continuousOn_sumEll E B hE hLip)))

lemma integrableOn_integrand {n r : ℕ} {ι : Type*} (E : ι → Factor n r)
    (B : Finset ι) {q K : ℝ} (hE : ∀ i ∈ B, (E i).RangeOk q)
    (hLip : ∀ i ∈ B, (E i).LipOk K) (z : ℂ) :
    IntegrableOn (fun x => Complex.exp (z * (sumEll E B x : ℂ))) (cube n) := by
  exact (continuousOn_integrand E B hE hLip z).integrableOn_compact (isCompact_cube n)

@[simp] lemma Q_zero {n r : ℕ} {ι : Type*} (E : ι → Factor n r) (B : Finset ι) :
    Q E B 0 = 1 := by
  simp [Q, Measure.real, Integral.volume_cube]

@[simp] lemma Q_empty {n r : ℕ} {ι : Type*} (E : ι → Factor n r) (z : ℂ) :
    Q E ∅ z = 1 := by
  simp [Q, sumEll, Measure.real, Integral.volume_cube]

/-- At real arguments, the complex partition function is the corresponding
 real exponential integral embedded into `ℂ`. -/
lemma Q_real {n r : ℕ} {ι : Type*} (E : ι → Factor n r) (B : Finset ι) (t : ℝ) :
    Q E B (t : ℂ) = (cubeIntegral (fun x => Real.exp (t * sumEll E B x)) : ℂ) := by
  unfold Q cubeIntegral
  simp_rw [← Complex.ofReal_mul, ← Complex.ofReal_exp]
  exact integral_ofReal

lemma Q_real_pos {n r : ℕ} {ι : Type*} (E : ι → Factor n r)
    (B : Finset ι) {q K : ℝ} (hE : ∀ i ∈ B, (E i).RangeOk q)
    (hLip : ∀ i ∈ B, (E i).LipOk K) (t : ℝ) :
    0 < (Q E B (t : ℂ)).re := by
  rw [Q_real]
  simp only [Complex.ofReal_re]
  have hvol : NeZero ((volume : Measure (Fin n → ℝ)).restrict (cube n)) := by
    constructor
    intro hzero
    have h := congrArg (fun μ : Measure (Fin n → ℝ) => μ Set.univ) hzero
    simp [Integral.volume_cube] at h
  letI := hvol
  apply integral_exp_pos
  exact (Real.continuous_exp.comp_continuousOn
    (continuousOn_const.mul (continuousOn_sumEll E B hE hLip))).integrableOn_compact
    (isCompact_cube n)

lemma Q_real_ne_zero {n r : ℕ} {ι : Type*} (E : ι → Factor n r)
    (B : Finset ι) {q K : ℝ} (hE : ∀ i ∈ B, (E i).RangeOk q)
    (hLip : ∀ i ∈ B, (E i).LipOk K) (t : ℝ) : Q E B (t : ℂ) ≠ 0 := by
  intro hzero
  have hp := Q_real_pos E B hE hLip t
  rw [hzero] at hp
  exact (lt_irrefl 0) hp

/-- The identity `Q(1)=Z` refers to the original factors, not a new
 definition of their product. -/
lemma Q_one_eq_partitionFunction {n r : ℕ} {ι : Type*} [Fintype ι]
    (E : ι → Factor n r) {q : ℝ} (hE : ∀ i, (E i).RangeOk q) :
    Q E Finset.univ 1 = (partitionFunctionFactor E : ℂ) := by
  rw [show (1 : ℂ) = ((1 : ℝ) : ℂ) by norm_num, Q_real]
  apply congrArg Complex.ofReal
  unfold cubeIntegral partitionFunctionFactor partitionFunction
  apply setIntegral_congr_fun (measurableSet_cube n)
  intro x hx
  simp only [one_mul, sumEll]
  rw [Real.exp_sum]
  apply Finset.prod_congr rfl
  intro i hi
  unfold ell Factor.ell Integral.Factor.ambient pullback
  exact Real.exp_log (lt_of_lt_of_le zero_lt_one
    ((hE i).2 _ (mem_cube.mp (restrictTo_mem_cube (E i).scope hx))))

lemma integrand_norm_le {n r : ℕ} {ι : Type*} (E : ι → Factor n r)
    (B : Finset ι) {q : ℝ} (hE : ∀ i ∈ B, (E i).RangeOk q) (z : ℂ)
    {x : Fin n → ℝ} (hx : x ∈ cube n) :
    ‖Complex.exp (z * (sumEll E B x : ℂ))‖ ≤ Real.exp (‖z‖ * (B.card * q)) := by
  rcases sumEll_range E B hE hx with ⟨h₀, h₁⟩
  apply (Complex.norm_exp_le_exp_norm _).trans
  apply Real.exp_le_exp.mpr
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h₀]
  exact mul_le_mul_of_nonneg_left h₁ (norm_nonneg z)

lemma norm_Q_le {n r : ℕ} {ι : Type*} (E : ι → Factor n r)
    (B : Finset ι) {q : ℝ} (hE : ∀ i ∈ B, (E i).RangeOk q) (z : ℂ) :
    ‖Q E B z‖ ≤ Real.exp (‖z‖ * (B.card * q)) := by
  have h := norm_setIntegral_le_of_norm_le_const (volume_cube_lt_top n)
    (fun x hx => integrand_norm_le E B hE z hx)
  simpa [Q, Measure.real, volume_cube] using h

/-- Elementary estimate around the origin. The hypothesis is a numerical
 smallness condition; this result does not use or assert Barvinok zero-freeness. -/
lemma norm_Q_sub_one_le {n r : ℕ} {ι : Type*} (E : ι → Factor n r)
    (B : Finset ι) {q K : ℝ} (hE : ∀ i ∈ B, (E i).RangeOk q)
    (hLip : ∀ i ∈ B, (E i).LipOk K) {z : ℂ}
    (hz : ‖z‖ * (B.card * q) ≤ 1) :
    ‖Q E B z - 1‖ ≤ 2 * ‖z‖ * (B.card * q) := by
  have hInt := integrableOn_integrand E B hE hLip z
  have hconst : IntegrableOn (fun _ : Fin n → ℝ => (1 : ℂ)) (cube n) :=
    continuousOn_const.integrableOn_compact (isCompact_cube n)
  have heq : Q E B z - 1 =
      ∫ x in cube n, (Complex.exp (z * (sumEll E B x : ℂ)) - 1) := by
    rw [integral_sub hInt hconst]
    simp [Q, Measure.real, volume_cube]
  rw [heq]
  have hbound : ∀ x ∈ cube n,
      ‖Complex.exp (z * (sumEll E B x : ℂ)) - 1‖ ≤ 2 * ‖z‖ * (B.card * q) := by
    intro x hx
    rcases sumEll_range E B hE hx with ⟨h₀, h₁⟩
    have hzx : ‖z * (sumEll E B x : ℂ)‖ ≤ ‖z‖ * (B.card * q) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h₀]
      exact mul_le_mul_of_nonneg_left h₁ (norm_nonneg z)
    calc
      ‖Complex.exp (z * (sumEll E B x : ℂ)) - 1‖ ≤
          2 * ‖z * (sumEll E B x : ℂ)‖ := Complex.norm_exp_sub_one_le (hzx.trans hz)
      _ ≤ 2 * ‖z‖ * (B.card * q) := by nlinarith
  simpa [Measure.real, volume_cube] using
    norm_setIntegral_le_of_norm_le_const (volume_cube_lt_top n) hbound

/-- A genuine but collection-size-dependent zero-free neighbourhood. The
 stronger common disk of Lemma 2.1 remains a separate unproved obligation. -/
theorem Q_ne_zero_of_total_small {n r : ℕ} {ι : Type*} (E : ι → Factor n r)
    (B : Finset ι) {q K : ℝ} (hq : 0 ≤ q) (hE : ∀ i ∈ B, (E i).RangeOk q)
    (hLip : ∀ i ∈ B, (E i).LipOk K) {z : ℂ}
    (hz : 2 * ‖z‖ * (B.card * q) < 1) : Q E B z ≠ 0 := by
  have hnonneg : 0 ≤ ‖z‖ * (B.card * q) := by positivity
  have hsmall : ‖z‖ * (B.card * q) ≤ 1 := by nlinarith
  have hb := (norm_Q_sub_one_le E B hE hLip hsmall).trans_lt hz
  intro hzero
  simp [hzero] at hb

/-- Differentiation under the actual cube integral, justified by a bounded
 exponential derivative on a unit neighbourhood of the parameter. -/
lemma hasDerivAt_Q {n r : ℕ} {ι : Type*} (E : ι → Factor n r)
    (B : Finset ι) {q K : ℝ} (hq : 0 ≤ q) (hE : ∀ i ∈ B, (E i).RangeOk q)
    (hLip : ∀ i ∈ B, (E i).LipOk K) (z : ℂ) :
    HasDerivAt (Q E B)
      (∫ x in cube n, Complex.exp (z * (sumEll E B x : ℂ)) * (sumEll E B x : ℂ)) z := by
  let μ : Measure (Fin n → ℝ) := volume.restrict (cube n)
  let S : ℝ := B.card * q
  have hS : 0 ≤ S := mul_nonneg (Nat.cast_nonneg _) hq
  have hcont := continuousOn_sumEll E B hE hLip
  have hdcont : ContinuousOn
      (fun x => Complex.exp (z * (sumEll E B x : ℂ)) * (sumEll E B x : ℂ)) (cube n) :=
    (continuousOn_integrand E B hE hLip z).mul
      (Complex.continuous_ofReal.comp_continuousOn hcont)
  have hdmeas : AEStronglyMeasurable
      (fun x => Complex.exp (z * (sumEll E B x : ℂ)) * (sumEll E B x : ℂ)) μ :=
    (hdcont.integrableOn_compact (isCompact_cube n)).1
  have hboundint : Integrable (fun _ : Fin n → ℝ => Real.exp ((‖z‖ + 1) * S) * S) μ :=
    continuousOn_const.integrableOn_compact (isCompact_cube n)
  have hbound : ∀ᵐ x ∂μ, ∀ w ∈ Metric.ball z 1,
      ‖Complex.exp (w * (sumEll E B x : ℂ)) * (sumEll E B x : ℂ)‖ ≤
        Real.exp ((‖z‖ + 1) * S) * S := by
    filter_upwards [ae_restrict_mem (measurableSet_cube n)] with x hx
    intro w hw
    rcases sumEll_range E B hE hx with ⟨hx₀, hx₁⟩
    have hw' : ‖w‖ ≤ ‖z‖ + 1 := by
      have hdist : ‖w - z‖ < 1 := by simpa [Metric.mem_ball, dist_eq_norm] using hw
      calc
        ‖w‖ = ‖w - z + z‖ := by congr 1; ring
        _ ≤ ‖w - z‖ + ‖z‖ := norm_add_le _ _
        _ ≤ ‖z‖ + 1 := by linarith
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx₀]
    apply mul_le_mul _ hx₁ hx₀ (Real.exp_pos _).le
    exact (integrand_norm_le E B hE w hx).trans
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hw' hS))
  have hdiff : ∀ᵐ x ∂μ, ∀ w ∈ Metric.ball z 1,
      HasDerivAt (fun w : ℂ => Complex.exp (w * (sumEll E B x : ℂ)))
        (Complex.exp (w * (sumEll E B x : ℂ)) * (sumEll E B x : ℂ)) w := by
    exact Filter.Eventually.of_forall fun x w _ => by
      simpa only [Function.comp_def, id_eq, one_mul] using
        (Complex.hasDerivAt_exp (w * (sumEll E B x : ℂ))).comp w
          ((hasDerivAt_id w).mul_const (sumEll E B x : ℂ))
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) (bound := fun _ => Real.exp ((‖z‖ + 1) * S) * S)
    (by norm_num : (0 : ℝ) < 1)
    (Filter.Eventually.of_forall fun w => (integrableOn_integrand E B hE hLip w).1)
    (integrableOn_integrand E B hE hLip z) hdmeas hbound hboundint hdiff).2

/-- The entire-function assertion immediately preceding Lemma 2.1. -/
theorem differentiable_Q {n r : ℕ} {ι : Type*} (E : ι → Factor n r)
    (B : Finset ι) {q K : ℝ} (hq : 0 ≤ q) (hE : ∀ i ∈ B, (E i).RangeOk q)
    (hLip : ∀ i ∈ B, (E i).LipOk K) : Differentiable ℂ (Q E B) := by
  intro z
  exact (hasDerivAt_Q E B hq hE hLip z).differentiableAt

lemma analyticAt_Q {n r : ℕ} {ι : Type*} (E : ι → Factor n r)
    (B : Finset ι) {q K : ℝ} (hq : 0 ≤ q) (hE : ∀ i ∈ B, (E i).RangeOk q)
    (hLip : ∀ i ∈ B, (E i).LipOk K) (z : ℂ) : AnalyticAt ℂ (Q E B) z :=
  (differentiable_Q E B hq hE hLip).analyticAt z

end ZeroFree
end Paper08
