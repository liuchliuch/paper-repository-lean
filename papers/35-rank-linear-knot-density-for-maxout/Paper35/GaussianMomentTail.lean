import Paper35.Deep
import Paper35.RankAsymptotics
import Mathlib.Analysis.Asymptotics.Theta
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! The logarithmic upper bound in (8.16), including the standard-normal
Chernoff tail, is proved here without external inputs. The Θ(log K) result uses
only the explicitly registered classical GaussianExtremeMeanLaw from
RankAsymptotics; the finite upper bound and lower Jensen step are proved here. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal
namespace Paper35.GaussianMomentTail
open Paper35.Deep

/-- Classical two-sided standard-normal Chernoff bound, in squared form.
Reference: Boucheron--Lugosi--Massart, Concentration Inequalities (2013),
Section 2.3 (Gaussian Chernoff bound); no rank or Gaussian maximum occurs here. -/
def StandardGaussianSquaredTailInput : Prop :=
  ∀ t : ℝ, 0 ≤ t → (gaussianReal 0 1).real {x : ℝ | t < x^2} ≤ 2 * Real.exp (-t/2)

/-- The squared Gaussian tail input is itself discharged using mathlib's
Gaussian moment generating function and the proved Chernoff bound. -/
theorem standardGaussianSquaredTail : StandardGaussianSquaredTailInput := by
  have hsub : HasSubgaussianMGF (fun x : ℝ => x) 1 (gaussianReal 0 1) := by
    constructor
    · intro t
      exact integrable_exp_mul_gaussianReal t
    · intro t
      rw [mgf_fun_id_gaussianReal]
      simp
  intro t ht
  have hs : 0 ≤ Real.sqrt t := Real.sqrt_nonneg t
  have hs2 := Real.sq_sqrt ht
  have hr := hsub.measure_ge_le hs
  have hl := hsub.neg.measure_ge_le hs
  have hset : {x : ℝ | t < x^2} ⊆
      {x : ℝ | Real.sqrt t ≤ x} ∪ {x : ℝ | Real.sqrt t ≤ -x} := by
    intro x hx
    dsimp only [mem_setOf_eq] at hx
    by_cases hx0 : 0 ≤ x
    · left
      dsimp only [mem_setOf_eq]
      nlinarith
    · right
      dsimp only [mem_setOf_eq]
      nlinarith
  calc
    _ ≤ (gaussianReal 0 1).real ({x : ℝ | Real.sqrt t ≤ x} ∪ {x : ℝ | Real.sqrt t ≤ -x}) :=
      measureReal_mono hset
    _ ≤ (gaussianReal 0 1).real {x : ℝ | Real.sqrt t ≤ x} +
        (gaussianReal 0 1).real {x : ℝ | Real.sqrt t ≤ -x} := measureReal_union_le _ _
    _ ≤ Real.exp (-t/2)+Real.exp (-t/2) := by
      apply add_le_add
      · simpa only [hs2, NNReal.coe_one, mul_one, mul_comm (2 : ℝ) 1, one_mul] using hr
      · simpa only [hs2, NNReal.coe_one, mul_one, Pi.neg_apply, mul_comm (2 : ℝ) 1, one_mul] using hl
    _ = _ := by ring

lemma excess_integrable (a : ℝ) :
    Integrable (fun x : ℝ => max 0 (x^2-a)) (gaussianReal 0 1) :=
  (integrable_const _).sup ((memLp_id_gaussianReal (μ := 0) (v := 1) 2).integrable_sq.sub (integrable_const _))

/-- Integrate the one-dimensional Gaussian tail. The constant four is obtained
by the explicit exponential integral, rather than supplied as a moment input. -/
theorem gaussian_excess_square_bound (htail : StandardGaussianSquaredTailInput)
    (a : ℝ) (ha : 0 ≤ a) :
    (∫ x : ℝ, max 0 (x^2-a) ∂gaussianReal 0 1) ≤ 4 * Real.exp (-a/2) := by
  let μ := gaussianReal 0 1
  have hF := excess_integrable a
  rw [hF.integral_eq_integral_meas_lt (Filter.Eventually.of_forall (fun x => le_max_left _ _))]
  have hg : IntegrableOn (fun t : ℝ => (2*Real.exp (-a/2))*Real.exp ((-1/2)*t)) (Ioi 0) :=
    (integrableOn_exp_mul_Ioi (by norm_num : (-1/2 : ℝ)<0) 0).const_mul _
  calc
    _ ≤ ∫ t in Ioi 0, (2*Real.exp (-a/2))*Real.exp ((-1/2)*t) := by
      apply integral_mono_of_nonneg (Filter.Eventually.of_forall (fun t => ENNReal.toReal_nonneg)) hg
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have hset : {x : ℝ | t < max 0 (x^2-a)} = {x : ℝ | a+t < x^2} := by
        ext x
        simp only [mem_setOf_eq, lt_max_iff]
        constructor
        · rintro (h|h)
          · exact False.elim ((not_lt_of_ge ht.le) h)
          · linarith
        · intro h
          right
          linarith
      rw [hset]
      have htpos : 0 < t := ht
      have H := htail (a+t) (by linarith)
      convert H using 1
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring
    _ = 4*Real.exp (-a/2) := by
      rw [integral_const_mul, integral_exp_mul_Ioi (by norm_num : (-1/2 : ℝ)<0)]
      norm_num
      ring

lemma prefixMax_eq_coordinate (n : ℕ) (x : ℕ → ℝ) :
    ∃ i ≤ n, Paper35.prefixMax n x = x i := by
  induction n with
  | zero => exact ⟨0,le_rfl,rfl⟩
  | succ n ih =>
    obtain ⟨i,hi,he⟩ := ih
    by_cases h : Paper35.prefixMax n x ≤ x (n+1)
    · exact ⟨n+1,le_rfl,max_eq_right h⟩
    · exact ⟨i,by omega,by rw [Paper35.prefixMax, max_eq_left (le_of_not_ge h),he]⟩

/-- The elementary truncation bound for the actual finite maximum. -/
lemma prefixMax_square_le_excess_sum (n : ℕ) (x : ℕ → ℝ) (a : ℝ) :
    (Paper35.prefixMax n x)^2 ≤ a + ∑ i ∈ Finset.range (n+1), max 0 (x i^2-a) := by
  obtain ⟨i,hi,he⟩ := prefixMax_eq_coordinate n x
  rw [he]
  have hs := Finset.single_le_sum (s := Finset.range (n+1))
    (f := fun j => max 0 (x j^2-a)) (fun j _ => le_max_left 0 _)
    (show i ∈ Finset.range (n+1) from Finset.mem_range.mpr (by omega))
  have hp := le_max_right 0 (x i^2-a)
  linarith

lemma excess_coordinate_integrable (i : ℕ) (a : ℝ) :
    Integrable (fun x : ℕ → ℝ => max 0 (x i^2-a)) Paper35.standardNormalSequence := by
  exact (integrable_const _).sup
    ((Paper35.memLp_normalCoordinate i 2).integrable_sq.sub (integrable_const _))

lemma integral_excess_coordinate (i : ℕ) (a : ℝ) :
    (∫ x : ℕ → ℝ, max 0 (x i^2-a) ∂Paper35.standardNormalSequence) =
      ∫ x : ℝ, max 0 (x^2-a) ∂gaussianReal 0 1 := by
  have H := integral_map (μ := Paper35.standardNormalSequence) (φ := fun x : ℕ → ℝ => x i)
    (f := fun y : ℝ => max 0 (y^2-a)) (measurable_pi_apply i).aemeasurable (by fun_prop)
  rw [Paper35.normalCoordinate_law] at H
  exact H.symm

/-- The logarithmic second-moment upper bound of Proposition 8.2. -/
theorem gaussianMaxSecondMoment_upper (htail : StandardGaussianSquaredTailInput) (n : ℕ) :
    gaussianMaxSecondMoment (n+1) ≤ 2*Real.log (2*(n+1 : ℝ))+2 := by
  let a := 2*Real.log (2*(n+1 : ℝ))
  have hk : 0 < 2*(n+1 : ℝ) := by positivity
  have ha : 0 ≤ a := by
    apply mul_nonneg (by norm_num)
    exact Real.log_nonneg (by nlinarith [Nat.cast_nonneg (α := ℝ) n])
  have hI : Integrable (fun x : ℕ → ℝ => a + ∑ i ∈ Finset.range (n+1), max 0 (x i^2-a))
      Paper35.standardNormalSequence :=
    (integrable_const a).add (integrable_finset_sum _ (fun i _ => excess_coordinate_integrable i a))
  change (∫ x, (Paper35.prefixMax n x)^2 ∂Paper35.standardNormalSequence) ≤ _
  calc
    _ ≤ ∫ x : ℕ → ℝ, a + ∑ i ∈ Finset.range (n+1), max 0 (x i^2-a) ∂Paper35.standardNormalSequence :=
      integral_mono (Paper35.memLp_prefixMax n 2).integrable_sq hI
        (fun x => prefixMax_square_le_excess_sum n x a)
    _ = a + ∑ i ∈ Finset.range (n+1), ∫ x : ℝ, max 0 (x^2-a) ∂gaussianReal 0 1 := by
      rw [integral_add (integrable_const a) (integrable_finset_sum _ (fun i _ => excess_coordinate_integrable i a)),
        integral_finset_sum _ (fun i _ => excess_coordinate_integrable i a)]
      simp_rw [integral_excess_coordinate]
      simp
    _ ≤ a + ∑ _i ∈ Finset.range (n+1), 4*Real.exp (-a/2) := by
      apply add_le_add_left
      exact Finset.sum_le_sum (fun i _ => gaussian_excess_square_bound htail a ha)
    _ = 2*Real.log (2*(n+1 : ℝ))+2 := by
      have he : Real.exp (-a/2) = (2*(n+1 : ℝ))⁻¹ := by
        have heq : -a/2 = -Real.log (2*(n+1 : ℝ)) := by dsimp [a]; ring
        rw [heq,Real.exp_neg,Real.exp_log hk]
      rw [he]
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
      dsimp only [a]
      field_simp
      <;> ring

/-- The complete finite upper chain in (8.16), with actual Gaussian moments. -/
theorem gaussianLengthCorrection_upper (htail : StandardGaussianSquaredTailInput) (n : ℕ) :
    gaussianLengthCorrection (n+1) ≤ 2*Real.log (2*(n+1 : ℝ))+2 := by
  apply max_le
  · have H := Real.log_nonneg (show 1 ≤ 2*(n+1 : ℝ) by nlinarith [Nat.cast_nonneg (α := ℝ) n])
    linarith
  · exact gaussianMaxSecondMoment_upper htail n

/-- Unconditional upper bound in (8.16), on actual Gaussian rank moments. -/
theorem gaussianLengthCorrection_upper_unconditional (n : ℕ) :
    gaussianLengthCorrection (n+1) ≤ 2*Real.log (2*(n+1 : ℝ))+2 :=
  gaussianLengthCorrection_upper standardGaussianSquaredTail n

lemma gaussianMaxMean_square_le_secondMoment (K : ℕ) :
    Paper35.gaussianMaxMean K^2 ≤ gaussianMaxSecondMoment K := by
  cases K with
  | zero => simp [Paper35.gaussianMaxMean, gaussianMaxSecondMoment]
  | succ n =>
    exact Paper35.Deep.mean_square_le_second_moment Paper35.standardNormalSequence
      (Paper35.prefixMax n) (Paper35.memLp_prefixMax n 2)

/-- The source logarithmic order, now proved from the actual first-moment
extreme-value law and the unconditional finite second-moment upper bound. -/
theorem gaussianLengthCorrection_eventual_bounds
    (hext : Paper35.RankAsymptotics.GaussianExtremeMeanLaw) :
    ∀ᶠ K : ℕ in Filter.atTop,
      (1/2 : ℝ)*Real.log K ≤ gaussianLengthCorrection K ∧
      gaussianLengthCorrection K ≤ 6*Real.log K := by
  have hhalf : ∀ᶠ K : ℕ in Filter.atTop,
      (1/2 : ℝ) ≤ Paper35.gaussianMaxMean K / Real.sqrt (2*Real.log K) := by
    filter_upwards [(tendsto_order.mp hext.1).1 (1/2) (by norm_num)] with K hK
    exact hK.le
  have hlog : ∀ᶠ K : ℕ in Filter.atTop, (1 : ℝ) ≤ Real.log K :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (Filter.eventually_ge_atTop 1)
  filter_upwards [hhalf,hlog] with K hhalf hlog
  have hsqpos : 0 < Real.sqrt (2*Real.log K) := Real.sqrt_pos.2 (by linarith)
  have hm : (1/2 : ℝ)*Real.sqrt (2*Real.log K) ≤ Paper35.gaussianMaxMean K := by
    exact (le_div_iff₀ hsqpos).1 hhalf
  have hs := Real.sq_sqrt (show 0 ≤ 2*Real.log K by linarith)
  have hmq := (gaussianMaxMean_square_le_secondMoment K).trans
    (gaussianMaxSecondMoment_le_lengthCorrection K)
  constructor
  · have hmsq := (sq_le_sq₀ (by positivity : 0 ≤ (1/2 : ℝ)*Real.sqrt (2*Real.log K))
      (Paper35.gaussianMaxMean_nonneg K)).2 hm
    nlinarith
  · cases K with
    | zero => simp at hlog; linarith
    | succ n =>
      have hu := gaussianLengthCorrection_upper_unconditional n
      have hp : (0 : ℝ) < (n : ℝ)+1 := by positivity
      rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hp.ne'] at hu
      have hl2 : Real.log 2 ≤ 1 := by
        have H := Real.log_le_sub_one_of_pos (show (0 : ℝ)<2 by norm_num)
        norm_num at H
        exact H
      norm_num only [Nat.cast_add, Nat.cast_one] at hlog ⊢
      nlinarith

/-- Proposition 8.2's q_K = Theta(log K), in mathlib's asymptotic relation. -/
theorem gaussianLengthCorrection_theta_log
    (hext : Paper35.RankAsymptotics.GaussianExtremeMeanLaw) :
    Asymptotics.IsTheta Filter.atTop gaussianLengthCorrection (fun K : ℕ => Real.log K) := by
  constructor
  · apply Asymptotics.isBigO_iff.2
    refine ⟨6, ?_⟩
    filter_upwards [gaussianLengthCorrection_eventual_bounds hext] with K hK
    simpa only [Real.norm_eq_abs, abs_of_nonneg (le_trans (by norm_num : (0 : ℝ)≤1)
      (gaussianLengthCorrection_ge_one K)), abs_of_nonneg (Real.log_natCast_nonneg K)] using hK.2
  · apply Asymptotics.isBigO_iff.2
    refine ⟨2, ?_⟩
    filter_upwards [gaussianLengthCorrection_eventual_bounds hext] with K hK
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (Real.log_natCast_nonneg K), abs_of_nonneg (le_trans (by norm_num : (0 : ℝ)≤1)
        (gaussianLengthCorrection_ge_one K))]
    linarith [hK.1]

end Paper35.GaussianMomentTail
