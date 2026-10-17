import PUT.DirichletTV
import Mathlib.Probability.Distributions.Gamma
import Mathlib.Probability.Distributions.Beta

/-!
# Continuous probability objects for the Dirichlet prior

`dirichletMeasure` is the law of independent gamma random variables after
division by their sum.  This is the continuous normalized-gamma construction
of the symmetric Dirichlet law.  The construction, its probability property,
and its support are proved here without an assumed moment formula.

This file deliberately does **not** identify the algebraic quantities
`dirMoment` with integrals: that identification needs a further analytic
proof.  In particular the construction alone does not prove paper Lemma 2.
-/

noncomputable section
namespace PUT

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

/-- The independent gamma variables used in the normalized-gamma definition. -/
def gammaProduct (d : ℕ) (a : ℝ) : Measure (Fin d → ℝ) :=
  Measure.pi (fun _ : Fin d => gammaMeasure a 1)

/-- Normalize all gamma coordinates by their sum.  Division by zero is
irrelevant almost everywhere when the shape is positive and `d > 0`. -/
def normalizeGamma {d : ℕ} (x : Fin d → ℝ) : Fin d → ℝ :=
  fun i => x i / ∑ j, x j

theorem measurable_normalizeGamma (d : ℕ) :
    Measurable (@normalizeGamma d) := by
  apply measurable_pi_lambda
  intro i
  exact (measurable_pi_apply i).div (by fun_prop)

/-- The actual continuous symmetric Dirichlet prior, constructed from
independent `Gamma(a,1)` variables, not a finite approximation. -/
def dirichletMeasure (d : ℕ) (a : ℝ) : Measure (Fin d → ℝ) :=
  (gammaProduct d a).map normalizeGamma

theorem isProbabilityMeasure_gammaProduct (d : ℕ) {a : ℝ} (ha : 0 < a) :
    IsProbabilityMeasure (gammaProduct d a) := by
  letI : IsProbabilityMeasure (gammaMeasure a 1) :=
    isProbabilityMeasure_gammaMeasure ha zero_lt_one
  unfold gammaProduct
  infer_instance

theorem isProbabilityMeasure_dirichletMeasure (d : ℕ) {a : ℝ} (ha : 0 < a) :
    IsProbabilityMeasure (dirichletMeasure d a) := by
  letI := isProbabilityMeasure_gammaProduct d ha
  exact Measure.isProbabilityMeasure_map (measurable_normalizeGamma d).aemeasurable

theorem gammaMeasure_ae_pos (a : ℝ) : ∀ᵐ x ∂gammaMeasure a 1, 0 < x := by
  unfold gammaMeasure
  rw [ae_withDensity_iff (by unfold gammaPDF; fun_prop)]
  have hne : ∀ᵐ x : ℝ ∂volume, x ≠ 0 := by
    rw [ae_iff]
    simpa using (measure_singleton (0 : ℝ) : (volume : Measure ℝ) {0} = 0)
  filter_upwards [hne] with x hx
  intro hpdf
  by_contra h
  have hxneg : x < 0 := lt_of_le_of_ne (le_of_not_gt h) hx
  exact hpdf (gammaPDF_of_neg hxneg)

theorem gammaProduct_ae_pos (d : ℕ) {a : ℝ} (ha : 0 < a) :
    ∀ᵐ x ∂gammaProduct d a, ∀ i, 0 < x i := by
  letI : IsProbabilityMeasure (gammaMeasure a 1) :=
    isProbabilityMeasure_gammaMeasure ha zero_lt_one
  unfold gammaProduct
  exact eventually_all.mpr (fun i =>
    (Measure.tendsto_eval_ae_ae (i := i)).eventually (gammaMeasure_ae_pos a))

/-- The open probability simplex; for one label the sole coordinate is one. -/
def positiveSimplex (d : ℕ) : Set (Fin d → ℝ) :=
  {p | (∀ i, 0 < p i) ∧ ∑ i, p i = 1}

theorem measurableSet_positiveSimplex (d : ℕ) :
    MeasurableSet (positiveSimplex d) := by
  unfold positiveSimplex
  have hpos : MeasurableSet {p : Fin d → ℝ | ∀ i, 0 < p i} := by
    rw [setOf_forall]
    exact MeasurableSet.iInter fun i =>
      measurableSet_lt measurable_const (measurable_pi_apply i)
  exact hpos.inter
    (measurableSet_eq_fun (by fun_prop) measurable_const)

theorem normalizeGamma_mem_positiveSimplex {d : ℕ} (hd : 0 < d)
    (x : Fin d → ℝ) (hx : ∀ i, 0 < x i) :
    normalizeGamma x ∈ positiveSimplex d := by
  have hsum : 0 < ∑ i, x i :=
    Finset.sum_pos (fun i _ => hx i) ⟨⟨0, hd⟩, Finset.mem_univ _⟩
  constructor
  · intro i
    exact div_pos (hx i) hsum
  · simp only [normalizeGamma, ← Finset.sum_div]
    exact div_self hsum.ne'

/-- The normalized-gamma prior is supported on actual positive probability
vectors. -/
theorem dirichletMeasure_ae_positiveSimplex {d : ℕ} (hd : 0 < d) {a : ℝ} (ha : 0 < a) :
    ∀ᵐ p ∂dirichletMeasure d a, p ∈ positiveSimplex d := by
  unfold dirichletMeasure
  apply (ae_map_iff (measurable_normalizeGamma d).aemeasurable
    (measurableSet_positiveSimplex d)).mpr
  filter_upwards [gammaProduct_ae_pos d ha] with x hx
  exact normalizeGamma_mem_positiveSimplex hd x hx

/-- The TV function on the continuous sample space is measurable. -/
theorem measurable_tvDist_uniform (d : ℕ) :
    Measurable (fun p : Fin d → ℝ => tvDist p (uniform d)) := by
  unfold tvDist
  fun_prop

theorem tvDist_uniform_le_one {d : ℕ} (hd : 0 < d)
    {p : Fin d → ℝ} (hp : p ∈ positiveSimplex d) :
    tvDist p (uniform d) ≤ 1 := by
  have hu : ∑ i : Fin d, uniform d i = 1 := by
    simp [uniform, hd.ne']
  have hsum : ∑ i, |p i - uniform d i| ≤ ∑ i, (p i + uniform d i) := by
    apply Finset.sum_le_sum
    intro i _
    have hpi := (hp.1 i).le
    have hui : 0 ≤ uniform d i := by unfold uniform; positivity
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  rw [Finset.sum_add_distrib, hp.2, hu] at hsum
  unfold tvDist
  linarith

/-- All finite moments of the TV distance exist under the continuous prior. -/
theorem dirichlet_tv_memLp {d : ℕ} (hd : 0 < d) {a : ℝ} (ha : 0 < a)
    (p : ℝ≥0∞) :
    MemLp (fun x => tvDist x (uniform d)) p (dirichletMeasure d a) := by
  letI := isProbabilityMeasure_dirichletMeasure d ha
  apply MemLp.of_bound (measurable_tvDist_uniform d).aestronglyMeasurable 1
  filter_upwards [dirichletMeasure_ae_positiveSimplex hd ha] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (tvDist_nonneg _ _)]
  exact tvDist_uniform_le_one hd hx

/-! ## Cauchy–Schwarz and Paley–Zygmund for genuine measures

These statements use Bochner integrals and event measures.  There is no
finite-support hypothesis and no assumed Hölder/Cauchy–Schwarz inequality.
-/

/-- Integral Cauchy–Schwarz in squared form, derived by integrating a
nonnegative quadratic and taking its discriminant. -/
theorem integral_cauchy_sq {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f g : Ω → ℝ) (hff : Integrable (fun x => f x ^ 2) μ)
    (hfg : Integrable (fun x => f x * g x) μ)
    (hgg : Integrable (fun x => g x ^ 2) μ) :
    (∫ x, f x * g x ∂μ) ^ 2 ≤
      (∫ x, f x ^ 2 ∂μ) * (∫ x, g x ^ 2 ∂μ) := by
  have hquad (t : ℝ) :
      0 ≤ (∫ x, f x ^ 2 ∂μ) * (t * t) +
        (2 * ∫ x, f x * g x ∂μ) * t + ∫ x, g x ^ 2 ∂μ := by
    have hn : 0 ≤ ∫ x, t ^ 2 * f x ^ 2 + (2 * t) * (f x * g x) + g x ^ 2 ∂μ := by
      apply integral_nonneg
      intro x
      change 0 ≤ t ^ 2 * f x ^ 2 + (2 * t) * (f x * g x) + g x ^ 2
      nlinarith only [sq_nonneg (t * f x + g x)]
    have he : (∫ x, t ^ 2 * f x ^ 2 + (2 * t) * (f x * g x) + g x ^ 2 ∂μ) =
        t ^ 2 * (∫ x, f x ^ 2 ∂μ) + (2 * t) * (∫ x, f x * g x ∂μ) +
          ∫ x, g x ^ 2 ∂μ := by
      calc
        _ = (∫ x, t ^ 2 * f x ^ 2 + (2 * t) * (f x * g x) ∂μ) +
            ∫ x, g x ^ 2 ∂μ :=
          integral_add ((hff.const_mul (t ^ 2)).add (hfg.const_mul (2 * t))) hgg
        _ = _ := by
          rw [integral_add (hff.const_mul (t ^ 2)) (hfg.const_mul (2 * t)),
            integral_const_mul, integral_const_mul]
    rw [he] at hn
    nlinarith only [hn]
  have hd := discrim_le_zero hquad
  unfold discrim at hd
  nlinarith

/-- The moment interpolation used after paper equation (25).  Its Hölder
inequality is proved, rather than supplied as a premise.  Only existence
of the four integrals is required. -/
theorem integral_holder_moments {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → ℝ) (h1 : Integrable (fun x => |X x|) μ)
    (h2 : Integrable (fun x => X x ^ 2) μ)
    (h3 : Integrable (fun x => |X x| ^ 3) μ)
    (h4 : Integrable (fun x => X x ^ 4) μ) :
    (∫ x, X x ^ 2 ∂μ) ^ 3 ≤
      (∫ x, |X x| ∂μ) ^ 2 * (∫ x, X x ^ 4 ∂μ) := by
  have hs (x : Ω) : Real.sqrt |X x| ^ 2 = |X x| := Real.sq_sqrt (abs_nonneg _)
  have ha (x : Ω) : |X x| ^ 2 = X x ^ 2 := sq_abs _
  have hp (x : Ω) : Real.sqrt |X x| * (|X x| * Real.sqrt |X x|) = X x ^ 2 := by
    calc Real.sqrt |X x| * (|X x| * Real.sqrt |X x|) =
        |X x| * Real.sqrt |X x| ^ 2 := by ring
      _ = X x ^ 2 := by rw [hs]; nlinarith only [ha x]
  have hq (x : Ω) : (|X x| * Real.sqrt |X x|) ^ 2 = |X x| ^ 3 := by
    rw [mul_pow, hs]
    ring
  have hfirst := integral_cauchy_sq μ (fun x => Real.sqrt |X x|)
    (fun x => |X x| * Real.sqrt |X x|)
    (by simpa only [hs] using h1)
    (by simpa only [hp] using h2)
    (by simpa only [hq] using h3)
  simp only [hp, hs, hq] at hfirst
  have hr (x : Ω) : |X x| * X x ^ 2 = |X x| ^ 3 := by rw [← ha]; ring
  have ht (x : Ω) : (X x ^ 2) ^ 2 = X x ^ 4 := by ring
  have hsecond := integral_cauchy_sq μ (fun x => |X x|) (fun x => X x ^ 2)
    (by simpa only [ha] using h2)
    (by simpa only [hr] using h3)
    (by simpa only [ht] using h4)
  simp only [hr, ha, ht] at hsecond
  have he1 : 0 ≤ ∫ x, |X x| ∂μ := integral_nonneg (fun x => abs_nonneg _)
  have he2 : 0 ≤ ∫ x, X x ^ 2 ∂μ := integral_nonneg (fun x => sq_nonneg _)
  have he3 : 0 ≤ ∫ x, |X x| ^ 3 ∂μ := integral_nonneg (fun x => by positivity)
  have he4 : 0 ≤ ∫ x, X x ^ 4 ∂μ := integral_nonneg (fun x => by positivity)
  have hf_sq := mul_self_le_mul_self (sq_nonneg (∫ x, X x ^ 2 ∂μ)) hfirst
  have hs_mul := mul_le_mul_of_nonneg_left hsecond (sq_nonneg (∫ x, |X x| ∂μ))
  rcases he2.eq_or_lt with hz | hp2
  · rw [← hz]
    simpa using mul_nonneg (sq_nonneg (∫ x, |X x| ∂μ)) he4
  · apply (mul_le_mul_right hp2).mp
    nlinarith only [hf_sq, hs_mul]

/-- Paley–Zygmund at half a lower bound for the expectation, on an arbitrary
probability space.  The first and second moments are actual integrals. -/
theorem paley_zygmund_measure {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : Ω → ℝ)
    (hZ : Measurable Z) (hZint : Integrable Z μ)
    (hZ2int : Integrable (fun x => Z x ^ 2) μ)
    {m v : ℝ} (hm : 0 < m) (hv : 0 < v)
    (hEZ : m ≤ ∫ x, Z x ∂μ) (hEZ2 : (∫ x, Z x ^ 2 ∂μ) ≤ v) :
    m ^ 2 / (4 * v) ≤ μ.real {x | m / 2 ≤ Z x} := by
  let s : Set Ω := {x | m / 2 ≤ Z x}
  have hs : MeasurableSet s := measurableSet_le measurable_const hZ
  have hcomp : (∫ x in sᶜ, Z x ∂μ) ≤ m / 2 := by
    rw [← integral_indicator hs.compl]
    have hi : (∫ x, sᶜ.indicator Z x ∂μ) ≤ ∫ _ : Ω, m / 2 ∂μ := by
      apply integral_mono (hZint.indicator hs.compl) (integrable_const _)
      intro x
      by_cases hx : x ∈ s
      · rw [Set.indicator_of_not_mem (show x ∉ sᶜ by simpa using hx)]
        positivity
      · have hxlt : Z x < m / 2 := lt_of_not_ge hx
        simpa [hx] using hxlt.le
    simpa using hi
  have hlarge : m / 2 ≤ ∫ x in s, Z x ∂μ := by
    have hsplit := integral_add_compl hs hZint
    linarith
  let g : Ω → ℝ := s.indicator (fun _ => 1)
  have hfg_eq : (fun x => Z x * g x) = s.indicator Z := by
    funext x
    by_cases hx : x ∈ s <;> simp [g, hx]
  have hgg_eq : (fun x => g x ^ 2) = s.indicator (fun _ => (1 : ℝ)) := by
    funext x
    by_cases hx : x ∈ s <;> simp [g, hx]
  have hfg : Integrable (fun x => Z x * g x) μ := by
    rw [hfg_eq]
    exact hZint.indicator hs
  have hgg : Integrable (fun x => g x ^ 2) μ := by
    rw [hgg_eq]
    exact (integrable_const (1 : ℝ)).indicator hs
  have hcs := integral_cauchy_sq μ Z g hZ2int hfg hgg
  rw [hfg_eq, integral_indicator hs, hgg_eq, integral_indicator_const 1 hs] at hcs
  simp only [smul_eq_mul, mul_one] at hcs
  have hmass : 0 ≤ μ.real s := ENNReal.toReal_nonneg
  have hlarge0 : 0 ≤ ∫ x in s, Z x ∂μ := le_trans (by positivity) hlarge
  have hsq : (m / 2) ^ 2 ≤ (∫ x in s, Z x ∂μ) ^ 2 := by
    nlinarith
  have hbound := mul_le_mul_of_nonneg_right hEZ2 hmass
  change m ^ 2 / (4 * v) ≤ μ.real s
  apply (div_le_iff₀ (by positivity : 0 < 4 * v)).mpr
  nlinarith

/-- The paper's Paley–Zygmund numerical instance, now for a continuous
measure.  This is the probability-inequality step only; the two integral
bounds must still be proved for the constructed Dirichlet prior. -/
theorem paley_zygmund_paper_constants {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : Ω → ℝ)
    (hZ : Measurable Z) (hZint : Integrable Z μ)
    (hZ2int : Integrable (fun x => Z x ^ 2) μ)
    (a : ℝ) (ha : 1 ≤ a)
    (hEZ : 1 / (12 * Real.sqrt a) ≤ ∫ x, Z x ∂μ)
    (hEZ2 : (∫ x, Z x ^ 2 ∂μ) ≤ 1 / (4 * a)) :
    (1 / 144 : ℝ) ≤ μ.real {x | 1 / (24 * Real.sqrt a) ≤ Z x} := by
  have ha0 : 0 < a := by linarith
  have h := paley_zygmund_measure μ Z hZ hZint hZ2int
    (m := 1 / (12 * Real.sqrt a)) (v := 1 / (4 * a))
    (by positivity) (by positivity) hEZ hEZ2
  rw [paley_constant a ha0] at h
  have ht : (1 / (12 * Real.sqrt a) : ℝ) / 2 = 1 / (24 * Real.sqrt a) := by
    calc (1 / (12 * Real.sqrt a) : ℝ) / 2 =
        (1 / 2) * (1 / (12 * Real.sqrt a)) := by ring
      _ = 1 / (24 * Real.sqrt a) := half_ez_eq_threshold a ha0
  simpa only [ht] using h

/-- The exact continuous-measure target of paper Lemma 2.  This is a
specification. `PUT.lemma2_from_joint_moments` proves it from the explicitly
disclosed standard normalized-Gamma Dirichlet moment identity. -/
def paperLemma2 : Prop :=
  ∀ (d : ℕ) (a : ℝ), 2 ≤ d → 1 ≤ a →
    (1 / 144 : ℝ) ≤
      (dirichletMeasure d a).real {p | lemma2Threshold a ≤ tvDist p (uniform d)}

end PUT
