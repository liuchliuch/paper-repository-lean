import Paper02.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

noncomputable section

open MeasureTheory Real

namespace Paper02.LSym

lemma one_sub_cos_nonneg (t : ℝ) : 0 ≤ 1 - Real.cos t := sub_nonneg.mpr (Real.cos_le_one t)

lemma one_sub_cos_le_sq (t : ℝ) : 1 - Real.cos t ≤ t ^ 2 / 2 := by
  have hc := Real.cos_two_mul (t / 2)
  have hs := Real.sin_sq_le_sq (x := t / 2)
  have hi := Real.sin_sq_add_cos_sq (t / 2)
  have he : 2 * (t / 2) = t := by ring
  rw [he] at hc
  nlinarith

lemma levy_kernel_bound (x s : ℝ) :
    |1 - Real.cos (x * s)| ≤ (x ^ 2 + 2) * min (s ^ 2) 1 := by
  rw [abs_of_nonneg (one_sub_cos_nonneg _)]
  by_cases hs : s ^ 2 ≤ 1
  · rw [min_eq_left hs]
    have := one_sub_cos_le_sq (x * s)
    nlinarith [sq_nonneg x, sq_nonneg s, sq_nonneg (x * s)]
  · rw [min_eq_right (le_of_not_ge hs)]
    have := Real.neg_one_le_cos (x * s)
    nlinarith [sq_nonneg x]

lemma levyIntegrable_iff (ν : Measure ℝ) :
    LevyIntegrable ν ↔ Integrable (fun s : ℝ => min (s ^ 2) 1) ν := by
  unfold LevyIntegrable
  rw [lt_top_iff_ne_top]
  apply lintegral_ofReal_ne_top_iff_integrable
  · exact (by fun_prop : Continuous (fun s : ℝ => min (s ^ 2) 1)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun s => le_min (sq_nonneg s) zero_le_one)

lemma integrable_levy_kernel {ν : Measure ℝ} (hν : LevyIntegrable ν) (x : ℝ) :
    Integrable (fun s : ℝ => 1 - Real.cos (x * s)) ν := by
  have hi := ((levyIntegrable_iff ν).mp hν).const_mul (x ^ 2 + 2)
  apply hi.mono' (by fun_prop)
  exact Filter.Eventually.of_forall (fun s => by
    simpa only [Real.norm_eq_abs] using levy_kernel_bound x s)

lemma integrable_weight_cos {ν : Measure ℝ} (hν : LevyIntegrable ν) (x : ℝ) :
    Integrable (fun s : ℝ => (1 - Real.cos s) * Real.cos (x * s)) ν := by
  have hw : Integrable (fun s : ℝ => 1 - Real.cos s) ν := by
    simpa using integrable_levy_kernel hν 1
  apply hw.mono' (by fun_prop)
  filter_upwards [] with s
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (one_sub_cos_nonneg s)]
  exact mul_le_of_le_one_right (one_sub_cos_nonneg s) (Real.abs_cos_le_one _)

lemma secondDiff_integral {ν : Measure ℝ} (hν : LevyIntegrable ν) (k : ℤ) :
    secondDiff (fun z : ℤ => ∫ s in Set.Ioi (0 : ℝ),
      (1 - Real.cos ((z : ℝ) * s)) ∂ν) k =
      ∫ s in Set.Ioi (0 : ℝ), (1 - Real.cos s) * Real.cos ((k : ℝ) * s) ∂ν := by
  have h1 := (integrable_levy_kernel hν ((k + 1 : ℤ) : ℝ)).restrict (s := Set.Ioi (0 : ℝ))
  have h2 := (integrable_levy_kernel hν (k : ℝ)).restrict (s := Set.Ioi (0 : ℝ))
  have h3 := (integrable_levy_kernel hν ((k - 1 : ℤ) : ℝ)).restrict (s := Set.Ioi (0 : ℝ))
  have he : (fun s : ℝ => (1 - Real.cos s) * Real.cos ((k : ℝ) * s)) =
      (fun s : ℝ => ((1 - Real.cos (((k + 1 : ℤ) : ℝ) * s)) -
        2 * (1 - Real.cos ((k : ℝ) * s)) +
        (1 - Real.cos (((k - 1 : ℤ) : ℝ) * s))) / 2) := by
    funext s
    exact (Paper02.secondDiff_cos s k).symm
  have ha := integral_add (h1.sub (h2.const_mul 2)) h3
  have hs := integral_sub h1 (h2.const_mul 2)
  simp only [Pi.sub_apply] at ha hs
  rw [he, integral_div, ha, hs, integral_const_mul]
  rfl

lemma cert_secondDiff {g : ℝ → ℝ} (c : LSymCert g) (k : ℤ) :
    secondDiff (RestrictInt g) k = c.A +
      ∫ s in Set.Ioi (0 : ℝ), (1 - Real.cos s) * Real.cos ((k : ℝ) * s) ∂c.ν := by
  have he : RestrictInt g = fun k : ℤ => c.A * (k : ℝ) ^ 2 +
      ∫ s in Set.Ioi (0 : ℝ), (1 - Real.cos ((k : ℝ) * s)) ∂c.ν := by
    funext k
    exact c.apply_eq _
  rw [he, Paper02.secondDiff_add, Paper02.secondDiff_gaussian,
    secondDiff_integral c.ν_integrable]

lemma cert_one {g : ℝ → ℝ} (c : LSymCert g) :
    g 1 = c.A + ∫ s in Set.Ioi (0 : ℝ), (1 - Real.cos s) ∂c.ν := by
  simpa using c.apply_eq 1

lemma cert_nonneg {g : ℝ → ℝ} (c : LSymCert g) (x : ℝ) : 0 ≤ g x := by
  rw [c.apply_eq x]
  exact add_nonneg (mul_nonneg c.A_nonneg (sq_nonneg x))
    (integral_nonneg fun s => one_sub_cos_nonneg _)

lemma cert_zero {g : ℝ → ℝ} (c : LSymCert g) : g 0 = 0 := by
  simp [c.apply_eq 0]

lemma cert_even {g : ℝ → ℝ} (c : LSymCert g) (x : ℝ) : g (-x) = g x := by
  simp only [c.apply_eq, neg_sq, neg_mul, Real.cos_neg]

lemma dual_cert {ι : Type*} [Fintype ι] {g : ℝ → ℝ} (c : LSymCert g)
    (a : ι → ℝ) (k : ι → ℤ) (M : ℝ)
    (hM : ∀ t : ℝ, |∑ i, a i * Real.cos ((k i : ℝ) * t)| ≤ M) :
    |∑ i, a i * secondDiff (RestrictInt g) (k i)| ≤ g 1 * M := by
  classical
  let μ := c.ν.restrict (Set.Ioi (0 : ℝ))
  have hw : Integrable (fun s : ℝ => 1 - Real.cos s) μ := by
    simpa [μ] using (integrable_levy_kernel c.ν_integrable 1).restrict
  have hcos (i : ι) : Integrable (fun s : ℝ =>
      (1 - Real.cos s) * Real.cos ((k i : ℝ) * s)) μ :=
    (integrable_weight_cos c.ν_integrable _).restrict
  have he : (∑ i, a i * secondDiff (RestrictInt g) (k i)) =
      c.A * (∑ i, a i) + ∫ s, (1 - Real.cos s) *
        (∑ i, a i * Real.cos ((k i : ℝ) * s)) ∂μ := by
    simp_rw [cert_secondDiff c, mul_add]
    rw [Finset.sum_add_distrib]
    congr 1
    · rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
    · simp_rw [← integral_const_mul]
      rw [← integral_finset_sum Finset.univ (fun i _ => (hcos i).const_mul (a i))]
      apply integral_congr_ae
      filter_upwards [] with s
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => by ring)
  have hzero : |∑ i, a i| ≤ M := by simpa using hM 0
  have hgauss : |c.A * ∑ i, a i| ≤ c.A * M := by
    rw [abs_mul, abs_of_nonneg c.A_nonneg]
    exact mul_le_mul_of_nonneg_left hzero c.A_nonneg
  have hint : |∫ s, (1 - Real.cos s) *
      (∑ i, a i * Real.cos ((k i : ℝ) * s)) ∂μ| ≤
      (∫ s, (1 - Real.cos s) ∂μ) * M := by
    have hbound : ∀ᵐ s ∂μ, ‖(1 - Real.cos s) *
        (∑ i, a i * Real.cos ((k i : ℝ) * s))‖ ≤
        (1 - Real.cos s) * M := by
      filter_upwards [] with s
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (one_sub_cos_nonneg s)]
      exact mul_le_mul_of_nonneg_left (hM s) (one_sub_cos_nonneg s)
    have hi := norm_integral_le_of_norm_le (hw.mul_const M) hbound
    simpa [integral_mul_const, Real.norm_eq_abs] using hi
  rw [he, cert_one c, add_mul]
  exact (abs_add_le _ _).trans (add_le_add hgauss hint)

/-- Corollary 2.2 for arbitrary Lévy measures, including infinite and nonatomic measures. -/
lemma dual_general {ι : Type*} [Fintype ι] {gpos gneg : ℝ → ℝ}
    (hp : IsLSym gpos) (hn : IsLSym gneg) (a : ι → ℝ) (k : ι → ℤ) (M : ℝ)
    (hM : ∀ t : ℝ, |∑ i, a i * Real.cos ((k i : ℝ) * t)| ≤ M) :
    |∑ i, a i * secondDiff (RestrictInt (fun x => gpos x - gneg x)) (k i)| ≤
      (gpos 1 + gneg 1) * M := by
  rcases hp with ⟨cp⟩
  rcases hn with ⟨cn⟩
  have he : (∑ i, a i * secondDiff (RestrictInt (fun x => gpos x - gneg x)) (k i)) =
      (∑ i, a i * secondDiff (RestrictInt gpos) (k i)) -
      (∑ i, a i * secondDiff (RestrictInt gneg) (k i)) := by
    change (∑ i, a i * secondDiff (fun z => RestrictInt gpos z - RestrictInt gneg z) (k i)) = _
    simp_rw [Paper02.secondDiff_sub, mul_sub, Finset.sum_sub_distrib]
  rw [he, add_mul]
  exact (abs_sub _ _).trans (add_le_add (dual_cert cp a k M hM) (dual_cert cn a k M hM))

/-- The original Lévy cone is closed under addition. -/
lemma isLSym_add {g h : ℝ → ℝ} (hg : IsLSym g) (hh : IsLSym h) :
    IsLSym (fun x => g x + h x) := by
  rcases hg with ⟨c⟩
  rcases hh with ⟨d⟩
  refine ⟨{
    A := c.A + d.A
    A_nonneg := add_nonneg c.A_nonneg d.A_nonneg
    ν := c.ν + d.ν
    ν_pos := bot_le
    ν_support := ?_
    ν_integrable := ?_
    apply_eq := ?_ }⟩
  · simp [Measure.restrict_add, c.ν_support, d.ν_support]
  · rw [levyIntegrable_iff, integrable_add_measure]
    exact ⟨(levyIntegrable_iff _).mp c.ν_integrable,
      (levyIntegrable_iff _).mp d.ν_integrable⟩
  · intro x
    rw [c.apply_eq, d.apply_eq, Measure.restrict_add,
      integral_add_measure (integrable_levy_kernel c.ν_integrable x).restrict
        (integrable_levy_kernel d.ν_integrable x).restrict]
    ring

/-- The original Lévy cone is closed under multiplication by a nonnegative scalar. -/
lemma isLSym_smul {g : ℝ → ℝ} (hg : IsLSym g) {r : ℝ} (hr : 0 ≤ r) :
    IsLSym (fun x => r * g x) := by
  rcases hg with ⟨c⟩
  refine ⟨{
    A := r * c.A
    A_nonneg := mul_nonneg hr c.A_nonneg
    ν := ENNReal.ofReal r • c.ν
    ν_pos := bot_le
    ν_support := ?_
    ν_integrable := ?_
    apply_eq := ?_ }⟩
  · simp [Measure.restrict_smul, c.ν_support]
  · rw [levyIntegrable_iff]
    exact ((levyIntegrable_iff _).mp c.ν_integrable).smul_measure ENNReal.ofReal_ne_top
  · intro x
    rw [c.apply_eq, Measure.restrict_smul, integral_smul_measure,
      ENNReal.toReal_ofReal hr, smul_eq_mul]
    ring

lemma isLSym_zero : IsLSym (fun _ : ℝ => (0 : ℝ)) := by
  simpa using (Paper02.isLSym_gaussian (A := 0) (le_refl 0))

lemma isLSym_sum {J : Type*} (S : Finset J) (g : J → ℝ → ℝ)
    (hg : ∀ j ∈ S, IsLSym (g j)) : IsLSym (fun x => ∑ j ∈ S, g j x) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using isLSym_zero
  | @insert j S hj ih =>
    simpa [Finset.sum_insert hj] using
      isLSym_add (hg j (Finset.mem_insert_self _ _))
        (ih (fun i hi => hg i (Finset.mem_insert_of_mem hi)))

lemma isLSym_jump {s : ℝ} (hs : 0 ≤ s) :
    IsLSym (fun x : ℝ => 1 - Real.cos (x * s)) := by
  rcases eq_or_lt_of_le hs with he | hs
  · subst s
    simpa using isLSym_zero
  · refine ⟨{
      A := 0
      A_nonneg := le_refl 0
      ν := Measure.dirac s
      ν_pos := bot_le
      ν_support := ?_
      ν_integrable := ?_
      apply_eq := ?_ }⟩
    · simp [restrict_dirac, not_le.mpr hs]
    · rw [levyIntegrable_iff]
      exact integrable_dirac (by simp)
    · intro x
      simp [restrict_dirac, hs]

/-- Every finite atomic nonnegative jump sum is in the original measure cone.
Zero frequencies are allowed, since their summands vanish identically. -/
lemma isLSym_atomic_sum {J : Type*} [Fintype J] (s c : J → ℝ)
    (hs : ∀ j, 0 ≤ s j) (hc : ∀ j, 0 ≤ c j) :
    IsLSym (fun x : ℝ => ∑ j, c j * (1 - Real.cos (x * s j))) := by
  exact isLSym_sum Finset.univ _ (fun j _ => isLSym_smul (isLSym_jump (hs j)) (hc j))

/-- The positive finite second-difference measure on the real line.
Its reduction modulo `2π` is the measure of Lemma 2.1. -/
def certMeasure {g : ℝ → ℝ} (c : LSymCert g) : Measure ℝ :=
  ENNReal.ofReal c.A • Measure.dirac 0 +
    (c.ν.restrict (Set.Ioi (0 : ℝ))).withDensity
      (fun s => ENNReal.ofReal (1 - Real.cos s))

lemma certMeasure_mass {g : ℝ → ℝ} (c : LSymCert g) :
    certMeasure c Set.univ = ENNReal.ofReal (g 1) := by
  have hw : Integrable (fun s : ℝ => 1 - Real.cos s) (c.ν.restrict (Set.Ioi (0 : ℝ))) := by
    simpa using (integrable_levy_kernel c.ν_integrable 1).restrict
  rw [certMeasure, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_univ _),
    smul_eq_mul, mul_one, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ, ← ofReal_integral_eq_lintegral_ofReal hw
      (Filter.Eventually.of_forall one_sub_cos_nonneg),
    ← ENNReal.ofReal_add c.A_nonneg (integral_nonneg one_sub_cos_nonneg), cert_one c]

instance certMeasure_finite {g : ℝ → ℝ} (c : LSymCert g) : IsFiniteMeasure (certMeasure c) := by
  constructor
  rw [certMeasure_mass]
  exact ENNReal.ofReal_lt_top

lemma certMeasure_secondDiff {g : ℝ → ℝ} (c : LSymCert g) (k : ℤ) :
    secondDiff (RestrictInt g) k = ∫ t, Real.cos ((k : ℝ) * t) ∂certMeasure c := by
  have hw : Integrable (fun s : ℝ => 1 - Real.cos s) (c.ν.restrict (Set.Ioi (0 : ℝ))) := by
    simpa using (integrable_levy_kernel c.ν_integrable 1).restrict
  haveI := isFiniteMeasure_withDensity_ofReal hw.hasFiniteIntegral
  have hcos : Integrable (fun t : ℝ => Real.cos ((k : ℝ) * t))
      ((c.ν.restrict (Set.Ioi (0 : ℝ))).withDensity
        (fun s => ENNReal.ofReal (1 - Real.cos s))) := by
    apply (integrable_const (1 : ℝ)).mono' (by fun_prop)
    exact Filter.Eventually.of_forall (fun t => by simpa using Real.abs_cos_le_one ((k : ℝ) * t))
  rw [certMeasure, integral_add_measure
      ((integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top) hcos,
    integral_smul_measure, integral_dirac,
    integral_withDensity_eq_integral_toReal_smul (by fun_prop)
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [mul_zero, Real.cos_zero, ENNReal.toReal_ofReal c.A_nonneg, smul_eq_mul,
    mul_one, ENNReal.toReal_ofReal (one_sub_cos_nonneg _)]
  exact cert_secondDiff c k

/-- Uniform norm of a real cosine polynomial on the circle, written using
its periodic real representative. -/
def cosinePolynomialNorm {ι : Type*} [Fintype ι] (a : ι → ℝ) (k : ι → ℤ) : ℝ :=
  sSup (Set.range (fun t : ℝ => |∑ i, a i * Real.cos ((k i : ℝ) * t)|))

lemma cosinePolynomial_bddAbove {ι : Type*} [Fintype ι] (a : ι → ℝ) (k : ι → ℤ) :
    BddAbove (Set.range (fun t : ℝ => |∑ i, a i * Real.cos ((k i : ℝ) * t)|)) := by
  classical
  refine ⟨∑ i, |a i|, ?_⟩
  rintro y ⟨t, rfl⟩
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)

lemma cosinePolynomial_le_norm {ι : Type*} [Fintype ι] (a : ι → ℝ) (k : ι → ℤ) (t : ℝ) :
    |∑ i, a i * Real.cos ((k i : ℝ) * t)| ≤ cosinePolynomialNorm a k :=
  le_csSup (cosinePolynomial_bddAbove a k) ⟨t, rfl⟩

/-- Corollary 2.2 in its actual uniform-norm form, with no assumed bound. -/
theorem dual_general_norm {ι : Type*} [Fintype ι] {gpos gneg : ℝ → ℝ}
    (hp : IsLSym gpos) (hn : IsLSym gneg) (a : ι → ℝ) (k : ι → ℤ) :
    |∑ i, a i * secondDiff (RestrictInt (fun x => gpos x - gneg x)) (k i)| ≤
      (gpos 1 + gneg 1) * cosinePolynomialNorm a k :=
  dual_general hp hn a k _ (cosinePolynomial_le_norm a k)

end Paper02.LSym
