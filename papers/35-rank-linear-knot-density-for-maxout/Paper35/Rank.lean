import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Gaussian maxima and their rank shape

The coefficient is defined using the actual expectation of the maximum of
independent standard normal coordinates.  `prefixMax n` uses coordinates
`0, ..., n`, so the paper's rank `K ≥ 1` corresponds to `prefixMax (K - 1)`.
This file proves strict increase and strict discrete concavity (Proposition
7.1), the exact rank-two value, both finite-rank inequalities (7.7), and the
sharp uniform coefficient of `K - 1`. The quantile inequalities (7.1), the
asymptotic expansion, and the polytope interpretation are separate claims and
are not asserted here.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Paper35

/-- An infinite sequence of independent standard normal samples. -/
def standardNormalSequence : Measure (ℕ → ℝ) :=
  Measure.infinitePi (fun _ : ℕ => gaussianReal 0 1)

instance : IsProbabilityMeasure standardNormalSequence := by
  unfold standardNormalSequence
  infer_instance

/-- Maximum of coordinates `0, ..., n`. In particular, it is never an empty maximum. -/
def prefixMax : ℕ → (ℕ → ℝ) → ℝ
  | 0, x => x 0
  | n + 1, x => max (prefixMax n x) (x (n + 1))

/-- The expected maximum of `K` iid standard normal samples; rank zero is set to zero. -/
def gaussianMaxMean : ℕ → ℝ
  | 0 => 0
  | n + 1 => ∫ x, prefixMax n x ∂standardNormalSequence

/-- The Gaussian rank coefficient `c_K = E[max_j G_j] / sqrt π`. -/
def gaussianRankCoefficient (K : ℕ) : ℝ := gaussianMaxMean K / Real.sqrt Real.pi

theorem continuous_prefixMax (n : ℕ) : Continuous (prefixMax n) := by
  induction n with
  | zero => exact continuous_apply 0
  | succ n ih => exact ih.max (continuous_apply (n + 1))

theorem integrable_normalCoordinate (n : ℕ) :
    Integrable (fun x : ℕ → ℝ => x n) standardNormalSequence := by
  have h : Integrable (fun y : ℝ => y) (gaussianReal 0 1) :=
    (memLp_id_gaussianReal (μ := 0) (v := 1) 1).integrable (by norm_num)
  change Integrable (id ∘ Function.eval n) (Measure.infinitePi (fun _ : ℕ => gaussianReal 0 1))
  exact (measurePreserving_eval_infinitePi (fun _ : ℕ => gaussianReal 0 1) n).integrable_comp_of_integrable h

theorem memLp_normalCoordinate (n : ℕ) (p : ℝ≥0) :
    MemLp (fun x : ℕ → ℝ => x n) p standardNormalSequence := by
  exact (memLp_id_gaussianReal (μ := 0) (v := 1) p).comp_measurePreserving
    (measurePreserving_eval_infinitePi (fun _ : ℕ => gaussianReal 0 1) n)

theorem memLp_prefixMax (n : ℕ) (p : ℝ≥0) :
    MemLp (prefixMax n) p standardNormalSequence := by
  induction n with
  | zero => exact memLp_normalCoordinate 0 p
  | succ n ih => exact ih.sup (memLp_normalCoordinate (n + 1) p)

theorem normalCoordinate_law (n : ℕ) :
    standardNormalSequence.map (fun x => x n) = gaussianReal 0 1 :=
  (measurePreserving_eval_infinitePi (fun _ : ℕ => gaussianReal 0 1) n).map_eq

theorem normalCoordinates_independent :
    iIndepFun (fun n (x : ℕ → ℝ) => x n) standardNormalSequence := by
  exact iIndepFun_infinitePi (fun _ : ℕ => measurable_id)

theorem integral_normalCoordinate (n : ℕ) :
    (∫ x, x n ∂standardNormalSequence) = 0 := by
  have h := integral_map (μ := standardNormalSequence) (φ := fun x : ℕ → ℝ => x n)
    (f := fun y : ℝ => y) (measurable_pi_apply n).aemeasurable
    measurable_id.aestronglyMeasurable
  rw [normalCoordinate_law] at h
  simpa using h.symm

theorem integrable_prefixMax (n : ℕ) :
    Integrable (prefixMax n) standardNormalSequence := by
  induction n with
  | zero => exact integrable_normalCoordinate 0
  | succ n ih => exact ih.sup (integrable_normalCoordinate (n + 1))

theorem prefixMax_mono_step (n : ℕ) (x : ℕ → ℝ) :
    prefixMax n x ≤ prefixMax (n + 1) x := le_max_left _ _

theorem prefixMax_mono (x : ℕ → ℝ) : Monotone (fun n => prefixMax n x) :=
  monotone_nat_of_le_succ (fun n => prefixMax_mono_step n x)

theorem prefixMax_congr {n : ℕ} {x y : ℕ → ℝ} (h : ∀ i ≤ n, x i = y i) :
    prefixMax n x = prefixMax n y := by
  induction n with
  | zero => exact h 0 (by omega)
  | succ n ih =>
    simp only [prefixMax]
    rw [ih (fun i hi => h i (by omega)), h (n + 1) le_rfl]

theorem prefixMax_const (n : ℕ) (a : ℝ) : prefixMax n (fun _ => a) = a := by
  induction n with
  | zero => rfl
  | succ n ih => simp [prefixMax, ih]

instance standardNormal_openPos : Measure.IsOpenPosMeasure (gaussianReal 0 1) :=
  (gaussianReal_absolutelyContinuous' 0 (by norm_num : (1 : ℝ≥0) ≠ 0)).isOpenPosMeasure

instance standardNormalSequence_openPos : Measure.IsOpenPosMeasure standardNormalSequence := by
  constructor
  rintro U hU ⟨x, hx⟩
  obtain ⟨s, t, ht, hsub⟩ := isOpen_pi_iff.mp hU x hx
  apply ne_of_gt
  apply lt_of_lt_of_le _ (measure_mono hsub)
  unfold standardNormalSequence
  rw [Measure.infinitePi_pi _ (fun i hi => (ht i hi).1.measurableSet)]
  apply bot_lt_iff_ne_bot.mpr
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  exact (ht i hi).1.measure_ne_zero (gaussianReal 0 1) ⟨x i, (ht i hi).2⟩

/-- Rank one has zero Gaussian maximum mean. -/
@[simp] theorem gaussianMaxMean_one : gaussianMaxMean 1 = 0 := by
  exact integral_normalCoordinate 0

theorem gaussianMaxMean_step_pos (n : ℕ) :
    0 < gaussianMaxMean (n + 2) - gaussianMaxMean (n + 1) := by
  change 0 < (∫ x, prefixMax (n + 1) x ∂standardNormalSequence) -
    ∫ x, prefixMax n x ∂standardNormalSequence
  rw [← integral_sub (integrable_prefixMax (n + 1)) (integrable_prefixMax n)]
  apply integral_pos_of_integrable_nonneg_nonzero
    ((continuous_prefixMax (n + 1)).sub (continuous_prefixMax n))
    ((integrable_prefixMax (n + 1)).sub (integrable_prefixMax n))
    (fun x => sub_nonneg.mpr (prefixMax_mono_step n x))
    (x := fun i => if i = n + 1 then 1 else 0)
  have h : prefixMax n (fun i => if i = n + 1 then (1 : ℝ) else 0) = 0 := by
    calc
      _ = prefixMax n (fun _ => 0) := by
        apply prefixMax_congr
        intro i hi
        simp [show i ≠ n + 1 by omega]
      _ = 0 := prefixMax_const n 0
  simp [prefixMax, h]

/-- The means of positive-rank Gaussian maxima are strictly increasing. -/
theorem gaussianMaxMean_strictMono : StrictMono (fun n => gaussianMaxMean (n + 1)) := by
  apply strictMono_nat_of_lt_succ
  intro n
  have h := gaussianMaxMean_step_pos n
  linarith

theorem gaussianMaxMean_nonneg (K : ℕ) : 0 ≤ gaussianMaxMean K := by
  cases K with
  | zero => rfl
  | succ n =>
    simpa using (gaussianMaxMean_strictMono.monotone (Nat.zero_le n))

private def swapCoordinates (a b : ℕ) : (ℕ → ℝ) ≃ᵐ (ℕ → ℝ) :=
  MeasurableEquiv.piCongrLeft (fun _ : ℕ => ℝ) (Equiv.swap a b)

private theorem swapCoordinates_apply (a b : ℕ) (x : ℕ → ℝ) (i : ℕ) :
    swapCoordinates a b x i = x (Equiv.swap a b i) := by
  simp [swapCoordinates, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_eq_cast]

private theorem swapCoordinates_preserving (a b : ℕ) :
    MeasurePreserving (swapCoordinates a b) standardNormalSequence standardNormalSequence := by
  constructor
  · exact (swapCoordinates a b).measurable
  · exact Measure.infinitePi_map_piCongrLeft (fun _ : ℕ => gaussianReal 0 1) (Equiv.swap a b)

private theorem prefixMax_swap_future (n : ℕ) (x : ℕ → ℝ) :
    prefixMax n (swapCoordinates (n + 1) (n + 2) x) = prefixMax n x := by
  apply prefixMax_congr
  intro i hi
  rw [swapCoordinates_apply, Equiv.swap_apply_of_ne_of_ne (by omega) (by omega)]

/-- A fresh coordinate may be chosen after the next coordinate, by exchangeability. -/
theorem gaussianMaxMean_fresh (n : ℕ) :
    (∫ x, max (prefixMax n x) (x (n + 2)) ∂standardNormalSequence) =
      gaussianMaxMean (n + 2) := by
  have h := (swapCoordinates_preserving (n + 1) (n + 2)).integral_comp'
    (prefixMax (n + 1))
  simpa only [prefixMax, prefixMax_swap_future, swapCoordinates_apply,
    Equiv.swap_apply_left, gaussianMaxMean] using h

/-- Coupled positive-part formula for the rank increment (Proposition 7.1). -/
theorem gaussianMaxMean_increment (n : ℕ) :
    gaussianMaxMean (n + 2) - gaussianMaxMean (n + 1) =
      ∫ x, max (x (n + 1) - prefixMax n x) 0 ∂standardNormalSequence := by
  change (∫ x, prefixMax (n + 1) x ∂standardNormalSequence) -
    (∫ x, prefixMax n x ∂standardNormalSequence) = _
  rw [← integral_sub (integrable_prefixMax (n + 1)) (integrable_prefixMax n)]
  congr 1
  funext x
  dsimp [prefixMax]
  rcases le_total (prefixMax n x) (x (n + 1)) with h | h
  · rw [max_eq_right h, max_eq_left (sub_nonneg.mpr h)]
  · rw [max_eq_left h, max_eq_right (sub_nonpos.mpr h), sub_self]

private theorem decreasing_increment_integrand (n : ℕ) (x : ℕ → ℝ) :
    0 ≤ (max (prefixMax n x) (x (n + 2)) - prefixMax n x) -
      (prefixMax (n + 2) x - prefixMax (n + 1) x) := by
  let a := prefixMax n x
  let b := x (n + 1)
  let c := x (n + 2)
  change 0 ≤ (max a c - a) - (max (max a b) c - max a b)
  rcases le_total a b with hab | hba
  · rw [max_eq_right hab]
    rcases le_total b c with hbc | hcb
    · rw [max_eq_right hbc, max_eq_right (hab.trans hbc)]
      linarith
    · rw [max_eq_left hcb]
      have h := le_max_left a c
      linarith
  · rw [max_eq_left hba]
    simp

/-- The successive increments strictly decrease, including the first increment.
This is the strict form of the paper's discrete concavity assertion. -/
theorem gaussianMaxMean_strict_concavity (n : ℕ) :
    gaussianMaxMean (n + 3) - gaussianMaxMean (n + 2) <
      gaussianMaxMean (n + 2) - gaussianMaxMean (n + 1) := by
  have hFreshInt : Integrable (fun x => max (prefixMax n x) (x (n + 2)))
      standardNormalSequence := (integrable_prefixMax n).sup (integrable_normalCoordinate (n + 2))
  have hPositive :
      0 < ∫ x, (max (prefixMax n x) (x (n + 2)) - prefixMax n x) -
        (prefixMax (n + 2) x - prefixMax (n + 1) x) ∂standardNormalSequence := by
    apply integral_pos_of_integrable_nonneg_nonzero
      ((((continuous_prefixMax n).max (continuous_apply (n + 2))).sub
        (continuous_prefixMax n)).sub
        ((continuous_prefixMax (n + 2)).sub (continuous_prefixMax (n + 1))))
      ((hFreshInt.sub (integrable_prefixMax n)).sub
        ((integrable_prefixMax (n + 2)).sub (integrable_prefixMax (n + 1))))
      (decreasing_increment_integrand n)
      (x := fun i => if i = n + 1 then 1 else if i = n + 2 then 2 else 0)
    have h : prefixMax n (fun i => if i = n + 1 then (1 : ℝ)
        else if i = n + 2 then 2 else 0) = 0 := by
      calc
        _ = prefixMax n (fun _ => 0) := by
          apply prefixMax_congr
          intro i hi
          simp [show i ≠ n + 1 by omega, show i ≠ n + 2 by omega]
        _ = 0 := prefixMax_const n 0
    norm_num [prefixMax, h, show n + 2 ≠ n + 1 by omega]
  have heq := integral_sub (hFreshInt.sub (integrable_prefixMax n))
    ((integrable_prefixMax (n + 2)).sub (integrable_prefixMax (n + 1)))
  simp only [Pi.sub_apply] at heq
  rw [heq] at hPositive
  have heq1 := integral_sub hFreshInt (integrable_prefixMax n)
  have heq2 := integral_sub (integrable_prefixMax (n + 2)) (integrable_prefixMax (n + 1))
  rw [heq1, heq2, gaussianMaxMean_fresh] at hPositive
  change 0 < (gaussianMaxMean (n + 2) - gaussianMaxMean (n + 1)) -
    (gaussianMaxMean (n + 3) - gaussianMaxMean (n + 2)) at hPositive
  linarith

theorem gaussianMaxMean_discrete_concavity (n : ℕ) :
    gaussianMaxMean (n + 3) + gaussianMaxMean (n + 1) ≤
      2 * gaussianMaxMean (n + 2) := by
  have h := gaussianMaxMean_strict_concavity n
  linarith

theorem gaussianRankCoefficient_strictMono :
    StrictMono (fun n => gaussianRankCoefficient (n + 1)) := by
  intro a b hab
  exact (div_lt_div_iff_of_pos_right (Real.sqrt_pos.2 Real.pi_pos)).2
    (gaussianMaxMean_strictMono hab)

theorem gaussianRankCoefficient_nonneg (K : ℕ) : 0 ≤ gaussianRankCoefficient K :=
  div_nonneg (gaussianMaxMean_nonneg K) (Real.sqrt_nonneg _)

theorem gaussianRankCoefficient_pos {K : ℕ} (hK : 2 ≤ K) :
    0 < gaussianRankCoefficient K := by
  have h := gaussianMaxMean_strictMono (show 0 < K - 1 by omega)
  have hmean : 0 < gaussianMaxMean K := by
    simpa [Nat.sub_add_cancel (show 1 ≤ K by omega)] using h
  exact div_pos hmean (Real.sqrt_pos.2 Real.pi_pos)

theorem gaussianMaxMean_increments_antitone :
    Antitone (fun n => gaussianMaxMean (n + 2) - gaussianMaxMean (n + 1)) := by
  apply antitone_nat_of_succ_le
  intro n
  exact (gaussianMaxMean_strict_concavity n).le

/-- Discrete concavity gives a uniform linear bound in terms of the rank-two mean. -/
theorem gaussianMaxMean_le_rank_two (n : ℕ) :
    gaussianMaxMean (n + 1) ≤ n * gaussianMaxMean 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := gaussianMaxMean_increments_antitone (Nat.zero_le n)
    simp only [Nat.zero_add, gaussianMaxMean_one, sub_zero] at h
    push_cast
    nlinarith

/-- The two-point mean equals one half the expected absolute difference. -/
theorem gaussianMaxMean_two_eq_abs_difference :
    gaussianMaxMean 2 = (∫ x, |x 0 - x 1| ∂standardNormalSequence) / 2 := by
  have hmax : prefixMax 1 = fun x : ℕ → ℝ => (x 0 + x 1 + |x 0 - x 1|) / 2 := by
    funext x
    change max (x 0) (x 1) = _
    rcases le_total (x 0) (x 1) with h | h
    · rw [max_eq_right h, abs_of_nonpos (sub_nonpos.mpr h)]
      ring
    · rw [max_eq_left h, abs_of_nonneg (sub_nonneg.mpr h)]
      ring
  change (∫ x, prefixMax 1 x ∂standardNormalSequence) = _
  rw [hmax, integral_div]
  have heq := integral_add
    ((integrable_normalCoordinate 0).add (integrable_normalCoordinate 1))
    (((integrable_normalCoordinate 0).sub (integrable_normalCoordinate 1)).abs)
  simp only [Pi.add_apply, Pi.sub_apply] at heq
  have heq1 := integral_add (integrable_normalCoordinate 0) (integrable_normalCoordinate 1)
  rw [heq, heq1, integral_normalCoordinate, integral_normalCoordinate]
  simp

theorem normalDifference_law :
    standardNormalSequence.map (fun x => x 0 - x 1) = gaussianReal 0 2 := by
  have hy : standardNormalSequence.map (fun x => -(x 1)) = gaussianReal 0 1 := by
    change standardNormalSequence.map ((fun y : ℝ => -y) ∘ (fun x : ℕ → ℝ => x 1)) = _
    rw [← Measure.map_map (μ := standardNormalSequence)
      (g := fun y : ℝ => -y) (f := fun x : ℕ → ℝ => x 1)
      measurable_neg (measurable_pi_apply 1),
      normalCoordinate_law, gaussianReal_map_neg]
    simp
  have h := gaussianReal_add_gaussianReal_of_indepFun
    (normalCoordinates_independent.indepFun (show (0 : ℕ) ≠ 1 by omega)).neg_right
    (normalCoordinate_law 0) hy
  change standardNormalSequence.map (fun x => x 0 + -(x 1)) =
    gaussianReal (0 + 0) (1 + 1) at h
  norm_num at h
  exact h

/-- The rank-two mean reduced to an ordinary variance-two Gaussian absolute moment. -/
theorem gaussianMaxMean_two_eq_gaussian_abs :
    gaussianMaxMean 2 = (∫ y, |y| ∂gaussianReal 0 2) / 2 := by
  rw [gaussianMaxMean_two_eq_abs_difference]
  congr 1
  have h := integral_map (μ := standardNormalSequence)
    (φ := fun x : ℕ → ℝ => x 0 - x 1) (f := fun y : ℝ => |y|)
    ((measurable_pi_apply 0).sub (measurable_pi_apply 1)).aemeasurable
    measurable_id.abs.aestronglyMeasurable
  rw [normalDifference_law] at h
  exact h.symm

private theorem gaussian_first_moment_Ioi :
    (∫ x : ℝ in Set.Ioi 0, x * Real.exp (-(1 / 4 : ℝ) * x ^ 2)) = 2 := by
  have h := integral_mul_cexp_neg_mul_sq (b := (1 / 4 : ℂ)) (by norm_num)
  have hf : (fun x : ℝ => (x : ℂ) * Complex.exp (-(1 / 4 : ℂ) * (x : ℂ) ^ 2)) =
      (fun x : ℝ => ((x * Real.exp (-(1 / 4 : ℝ) * x ^ 2) : ℝ) : ℂ)) := by
    funext x
    rw [Complex.ofReal_mul, Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  rw [hf] at h
  rw [integral_complex_ofReal] at h
  have hr := congrArg Complex.re h
  norm_num at hr
  simpa only [neg_mul] using hr

theorem integral_abs_normal_variance_two :
    (∫ y, |y| ∂gaussianReal 0 2) = 2 / Real.sqrt Real.pi := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (2 : ℝ≥0) ≠ 0)]
  have hf : (fun x : ℝ => gaussianPDFReal 0 2 x • |x|) =
      (fun x : ℝ => (Real.sqrt (4 * Real.pi))⁻¹ *
        (|x| * Real.exp (-(1 / 4 : ℝ) * |x| ^ 2))) := by
    funext x
    simp only [gaussianPDFReal, NNReal.coe_ofNat, sub_zero, smul_eq_mul, sq_abs]
    rw [show 2 * Real.pi * 2 = 4 * Real.pi by ring,
      show -(x ^ 2) / (2 * (2 : ℝ)) = -(1 / 4 : ℝ) * x ^ 2 by ring]
    ring
  rw [hf, integral_const_mul,
    integral_comp_abs (f := fun x : ℝ => x * Real.exp (-(1 / 4 : ℝ) * x ^ 2)),
    gaussian_first_moment_Ioi]
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
  norm_num
  field_simp
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 4), Real.sqrt_nonneg (4 : ℝ)]

/-- The exact rank-two constant from Section 7. -/
theorem gaussianMaxMean_two : gaussianMaxMean 2 = 1 / Real.sqrt Real.pi := by
  rw [gaussianMaxMean_two_eq_gaussian_abs, integral_abs_normal_variance_two]
  ring

theorem gaussianRankCoefficient_two : gaussianRankCoefficient 2 = 1 / Real.pi := by
  unfold gaussianRankCoefficient
  rw [gaussianMaxMean_two]
  have hsq := Real.sq_sqrt (le_of_lt Real.pi_pos)
  have hp : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
  field_simp
  nlinarith

/-- The universal Gaussian rank-linear estimate (the weaker inequality of (7.7)). -/
theorem gaussianRankCoefficient_le_rank_linear {K : ℕ} (hK : 1 ≤ K) :
    gaussianRankCoefficient K ≤ (K - 1 : ℕ) / Real.pi := by
  have h := gaussianMaxMean_le_rank_two (K - 1)
  rw [Nat.sub_add_cancel hK, gaussianMaxMean_two] at h
  unfold gaussianRankCoefficient
  apply (div_le_iff₀ (Real.sqrt_pos.mpr Real.pi_pos)).2
  have hs := Real.sq_sqrt (le_of_lt Real.pi_pos)
  have hp : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have heq : (↑(K - 1) : ℝ) / Real.pi * Real.sqrt Real.pi =
      (↑(K - 1) : ℝ) * (1 / Real.sqrt Real.pi) := by
    field_simp
    nlinarith
  rwa [heq]

private theorem negSequence_preserving :
    MeasurePreserving (fun x : ℕ → ℝ => fun i => -(x i))
      standardNormalSequence standardNormalSequence := by
  constructor
  · exact measurable_pi_lambda _ (fun i => (measurable_pi_apply i).neg)
  · unfold standardNormalSequence
    rw [Measure.infinitePi_map_pi _ (fun _ => measurable_neg)]
    congr 1
    funext i
    rw [gaussianReal_map_neg]
    simp

private theorem integral_prefixMax_neg (n : ℕ) :
    (∫ x, prefixMax n (fun i => -(x i)) ∂standardNormalSequence) = gaussianMaxMean (n + 1) := by
  have h := integral_map (μ := standardNormalSequence)
    (φ := fun x : ℕ → ℝ => fun i => -(x i)) (f := prefixMax n)
    negSequence_preserving.aemeasurable (continuous_prefixMax n).aestronglyMeasurable
  rw [negSequence_preserving.map_eq] at h
  exact h.symm

private theorem triple_range_identity (a b c : ℝ) :
    max (max a b) c + max (max (-a) (-b)) (-c) =
      (|a - b| + |a - c| + |b - c|) / 2 := by
  rcases le_total a b with hab | hba
  · rcases le_total b c with hbc | hcb
    · rw [max_eq_right hab, max_eq_right hbc,
        max_eq_left (neg_le_neg hab), max_eq_left (neg_le_neg (hab.trans hbc)),
        abs_of_nonpos (sub_nonpos.mpr hab), abs_of_nonpos (sub_nonpos.mpr (hab.trans hbc)),
        abs_of_nonpos (sub_nonpos.mpr hbc)]
      ring
    · rcases le_total a c with hac | hca
      · rw [max_eq_right hab, max_eq_left hcb, max_eq_left (neg_le_neg hab),
          max_eq_left (neg_le_neg hac), abs_of_nonpos (sub_nonpos.mpr hab),
          abs_of_nonpos (sub_nonpos.mpr hac), abs_of_nonneg (sub_nonneg.mpr hcb)]
        ring
      · rw [max_eq_right hab, max_eq_left hcb, max_eq_left (neg_le_neg hab),
          max_eq_right (neg_le_neg hca), abs_of_nonpos (sub_nonpos.mpr hab),
          abs_of_nonneg (sub_nonneg.mpr hca), abs_of_nonneg (sub_nonneg.mpr hcb)]
        ring
  · rcases le_total a c with hac | hca
    · rw [max_eq_left hba, max_eq_right hac, max_eq_right (neg_le_neg hba),
        max_eq_left (neg_le_neg (hba.trans hac)), abs_of_nonneg (sub_nonneg.mpr hba),
        abs_of_nonpos (sub_nonpos.mpr hac), abs_of_nonpos (sub_nonpos.mpr (hba.trans hac))]
      ring
    · rcases le_total b c with hbc | hcb
      · rw [max_eq_left hba, max_eq_left hca, max_eq_right (neg_le_neg hba),
          max_eq_left (neg_le_neg hbc), abs_of_nonneg (sub_nonneg.mpr hba),
          abs_of_nonneg (sub_nonneg.mpr hca), abs_of_nonpos (sub_nonpos.mpr hbc)]
        ring
      · rw [max_eq_left hba, max_eq_left hca, max_eq_right (neg_le_neg hba),
          max_eq_right (neg_le_neg hcb), abs_of_nonneg (sub_nonneg.mpr hba),
          abs_of_nonneg (sub_nonneg.mpr hca), abs_of_nonneg (sub_nonneg.mpr hcb)]
        ring

private theorem integral_abs_diff_02 :
    (∫ x, |x 0 - x 2| ∂standardNormalSequence) =
      ∫ x, |x 0 - x 1| ∂standardNormalSequence := by
  have h := (swapCoordinates_preserving 1 2).integral_comp' (fun x => |x 0 - x 1|)
  simpa only [swapCoordinates_apply, Equiv.swap_apply_left,
    Equiv.swap_apply_of_ne_of_ne (by omega : (0 : ℕ) ≠ 1) (by omega : (0 : ℕ) ≠ 2)] using h

private theorem integral_abs_diff_12 :
    (∫ x, |x 1 - x 2| ∂standardNormalSequence) =
      ∫ x, |x 0 - x 1| ∂standardNormalSequence := by
  have h := (swapCoordinates_preserving 0 1).integral_comp' (fun x => |x 0 - x 2|)
  have h' : (∫ x, |x 1 - x 2| ∂standardNormalSequence) =
      ∫ x, |x 0 - x 2| ∂standardNormalSequence := by
    simpa only [swapCoordinates_apply, Equiv.swap_apply_left,
      Equiv.swap_apply_of_ne_of_ne (by omega : (2 : ℕ) ≠ 0) (by omega : (2 : ℕ) ≠ 1)] using h
  exact h'.trans integral_abs_diff_02

theorem gaussianMaxMean_three : gaussianMaxMean 3 = (3 / 2 : ℝ) * gaussianMaxMean 2 := by
  have hpoint : (fun x : ℕ → ℝ => prefixMax 2 x + prefixMax 2 (fun i => -(x i))) =
      (fun x => (|x 0 - x 1| + |x 0 - x 2| + |x 1 - x 2|) / 2) := by
    funext x
    exact triple_range_identity (x 0) (x 1) (x 2)
  have hIntNeg : Integrable (fun x => prefixMax 2 (fun i => -(x i))) standardNormalSequence :=
    (((integrable_normalCoordinate 0).neg.sup
      (integrable_normalCoordinate 1).neg).sup (integrable_normalCoordinate 2).neg)
  have heq := congrArg (fun f : (ℕ → ℝ) → ℝ => ∫ x, f x ∂standardNormalSequence) hpoint
  dsimp only at heq
  rw [integral_add (integrable_prefixMax 2) hIntNeg, integral_prefixMax_neg,
    integral_div] at heq
  have hsum := integral_add
    ((((integrable_normalCoordinate 0).sub (integrable_normalCoordinate 1)).abs).add
      (((integrable_normalCoordinate 0).sub (integrable_normalCoordinate 2)).abs))
    (((integrable_normalCoordinate 1).sub (integrable_normalCoordinate 2)).abs)
  simp only [Pi.add_apply, Pi.sub_apply] at hsum
  have hsum1 := integral_add
    (((integrable_normalCoordinate 0).sub (integrable_normalCoordinate 1)).abs)
    (((integrable_normalCoordinate 0).sub (integrable_normalCoordinate 2)).abs)
  simp only [Pi.sub_apply] at hsum1
  rw [hsum, hsum1, integral_abs_diff_02, integral_abs_diff_12] at heq
  change gaussianMaxMean 3 + gaussianMaxMean 3 = _ at heq
  have htwo := gaussianMaxMean_two_eq_abs_difference
  linarith

theorem gaussianMaxMean_le_half_rank (n : ℕ) :
    gaussianMaxMean (n + 2) ≤ (n + 2 : ℝ) / 2 * gaussianMaxMean 2 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    have h := gaussianMaxMean_increments_antitone (show 1 ≤ n + 1 by omega)
    simp only [Nat.reduceAdd, gaussianMaxMean_three] at h
    push_cast
    nlinarith

/-- The sharper finite-rank inequality in (7.7), proved without random-polytope theory. -/
theorem gaussianRankCoefficient_le_half_rank {K : ℕ} (hK : 2 ≤ K) :
    gaussianRankCoefficient K ≤ K / (2 * Real.pi) := by
  have h := gaussianMaxMean_le_half_rank (K - 2)
  rw [Nat.sub_add_cancel hK, gaussianMaxMean_two] at h
  have hcast : (↑(K - 2) : ℝ) + 2 = K := by
    exact_mod_cast Nat.sub_add_cancel hK
  rw [hcast] at h
  unfold gaussianRankCoefficient
  apply (div_le_iff₀ (Real.sqrt_pos.mpr Real.pi_pos)).2
  have hs := Real.sq_sqrt (le_of_lt Real.pi_pos)
  have hp : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have heq : (K : ℝ) / (2 * Real.pi) * Real.sqrt Real.pi =
      (K : ℝ) / 2 * (1 / Real.sqrt Real.pi) := by
    field_simp
    nlinarith
  rwa [heq]

/-- The constant `1/π` is exactly the smallest uniform coefficient of `K - 1`. -/
theorem gaussianRankCoefficient_uniform_bound_iff (C : ℝ) :
    (∀ K : ℕ, 2 ≤ K → gaussianRankCoefficient K ≤ C * ((K : ℝ) - 1)) ↔
      1 / Real.pi ≤ C := by
  constructor
  · intro h
    have htwo := h 2 (by omega)
    norm_num [gaussianRankCoefficient_two] at htwo
    simpa only [one_div] using htwo
  · intro hC K hK
    have hbase : gaussianRankCoefficient K ≤ (1 / Real.pi) * ((K : ℝ) - 1) := by
      simpa [Nat.cast_sub (show 1 ≤ K by omega), div_eq_mul_inv, mul_comm]
        using gaussianRankCoefficient_le_rank_linear (show 1 ≤ K by omega)
    have hnonneg : (0 : ℝ) ≤ (K : ℝ) - 1 := by
      apply sub_nonneg.mpr
      exact_mod_cast (show 1 ≤ K by omega)
    exact hbase.trans (mul_le_mul_of_nonneg_right hC hnonneg)

theorem prefixMax_le_iff (n : ℕ) (x : ℕ → ℝ) (t : ℝ) :
    prefixMax n x ≤ t ↔ ∀ i ≤ n, x i ≤ t := by
  induction n with
  | zero => simp [prefixMax]
  | succ n ih =>
    rw [prefixMax, max_le_iff, ih]
    constructor
    · rintro ⟨h, hn⟩ i hi
      rcases Nat.eq_or_lt_of_le hi with heq | hlt
      · simpa [heq] using hn
      · exact h i (by omega)
    · intro h
      exact ⟨fun i hi => h i (by omega), h (n + 1) le_rfl⟩

/-- Exact distribution function of the maximum of `n + 1` standard normals. -/
theorem prefixMax_distribution (n : ℕ) (t : ℝ) :
    standardNormalSequence {x | prefixMax n x ≤ t} =
      (gaussianReal 0 1 (Set.Iic t)) ^ (n + 1) := by
  have hevent : {x : ℕ → ℝ | prefixMax n x ≤ t} =
      Set.pi (Finset.range (n + 1)) (fun _ : ℕ => Set.Iic t) := by
    ext x
    simp only [Set.mem_setOf_eq, prefixMax_le_iff, Set.mem_pi,
      Finset.mem_coe, Finset.mem_range, Set.mem_Iic]
    constructor
    · exact fun h i hi => h i (by omega)
    · exact fun h i hi => h i (by omega)
  rw [hevent, standardNormalSequence,
    Measure.infinitePi_pi _ (fun _ _ => measurableSet_Iic)]
  simp

end Paper35
