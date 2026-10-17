import Paper37.BayesLowerBound
import Paper37.AnytimePrediction

/-! Same-prior cumulative Bayes assembly. The observable good-event premise is
kept explicit here so the independently proved cycle/event estimate can be
connected without replacing an actual minimax risk by an abstract quantity. -/
namespace Paper37.CumulativeLower

open Finset Renewal Prediction BayesLowerBound SupportPrior LowerBound
open scoped ENNReal

noncomputable def cumulativeRisk (N : ℕ) (q : RandomizedPredictor) (μ : Law) : ℝ≥0∞ :=
  ∑ t ∈ range N, risk t q μ

noncomputable def minimaxCumulativeRisk (N : ℕ) : ℝ≥0∞ :=
  ⨅ q : RandomizedPredictor, ⨆ μ : Law, cumulativeRisk N q μ

lemma prior_total_ofReal (b : ℕ) : ∑ z, ENNReal.ofReal ((prior b).mass z) = 1 := by
  rw [← ENNReal.ofReal_sum_of_nonneg (fun z _ => (prior b).nonneg z), (prior b).total]
  simp

/-- The same fixed prior is used at every time, allowing the two finite sums to commute. -/
lemma sum_bayesRisk_eq (N b : ℕ) (q : RandomizedPredictor) :
    (∑ t ∈ range N, bayesRisk t b q) =
      ∑ z, ENNReal.ofReal ((prior b).mass z) * cumulativeRisk N q (law z) := by
  unfold bayesRisk cumulativeRisk
  simp_rw [Finset.mul_sum]
  rw [sum_comm]

lemma bayesCumulative_le_worst (N b : ℕ) (q : RandomizedPredictor) :
    (∑ t ∈ range N, bayesRisk t b q) ≤ ⨆ μ : Law, cumulativeRisk N q μ := by
  rw [sum_bayesRisk_eq]
  calc
    _ ≤ ∑ z, ENNReal.ofReal ((prior b).mass z) *
        (⨆ μ : Law, cumulativeRisk N q μ) := by
      apply sum_le_sum
      intro z _
      exact mul_le_mul_left' (le_iSup (fun μ : Law => cumulativeRisk N q μ) (law z)) _
    _ = _ := by rw [← Finset.sum_mul, prior_total_ofReal, one_mul]

lemma bayesRisk_lower_of_goodMass {b : ℕ} (hb : 0 < b) (t : ℕ)
    (hgood : 1/8 ≤ goodPredictiveMass t b) (q : RandomizedPredictor) :
    ENNReal.ofReal ((1/8)*radiusConstant b) ≤ bayesRisk t b q := by
  rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1/8)]
  exact (mul_le_mul_right' (ENNReal.ofReal_le_ofReal hgood) _).trans
    (goodMass_mul_radius_le_bayesRisk hb t q)

/-- A per-time observable event bound transfers to one cumulative minimax bound
without changing the prior with time. -/
theorem cumulative_lower_of_goodMass {b N : ℕ} (hb : 0 < b)
    (hgood : ∀ t ∈ Ico (24*b) N, 1/8 ≤ goodPredictiveMass t b)
    (q : RandomizedPredictor) :
    ENNReal.ofReal (((N-24*b : ℕ) : ℝ)*((1/8)*radiusConstant b)) ≤
      ⨆ μ : Law, cumulativeRisk N q μ := by
  have hconst : ENNReal.ofReal (((N-24*b : ℕ) : ℝ)*((1/8)*radiusConstant b)) =
      ∑ t ∈ Ico (24*b) N, ENNReal.ofReal ((1/8)*radiusConstant b) := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ =>
      mul_nonneg (by norm_num : (0 : ℝ) ≤ 1/8) (radiusConstant_nonneg b))]
    congr 1
    simp
  rw [hconst]
  calc
    _ ≤ ∑ t ∈ Ico (24*b) N, bayesRisk t b q :=
      sum_le_sum (fun t ht => bayesRisk_lower_of_goodMass hb t (hgood t ht) q)
    _ ≤ ∑ t ∈ range N, bayesRisk t b q := by
      apply sum_le_sum_of_subset
      intro t ht
      exact mem_range.mpr (mem_Ico.mp ht).2
    _ ≤ _ := bayesCumulative_le_worst N b q

/-- The count of admissible late times occupies at least half the horizon. -/
lemma late_count_lower {N : ℕ} (hN : 2500 ≤ N) :
    (N : ℝ)/2 ≤ ((N-24*ceilingRoot N : ℕ) : ℝ) := by
  have hN600 : 600 ≤ N := by omega
  obtain ⟨hb, h24, h25⟩ := ceilingRoot_scale_bounds hN600
  have hs0 := Real.sqrt_nonneg (N : ℝ)
  have hs2 := Real.mul_self_sqrt (Nat.cast_nonneg N)
  have hNR : (2500 : ℝ) ≤ N := by exact_mod_cast hN
  have hs50 : (50 : ℝ) ≤ Real.sqrt N := by nlinarith
  rw [Nat.cast_sub h24]
  nlinarith

/-- A ceiling square root supports the same hard prior at all earlier times. -/
lemma ceilingRoot_square_ge (N : ℕ) : N ≤ ceilingRoot N * ceilingRoot N := by
  have hs0 := Real.sqrt_nonneg (N : ℝ)
  have hs2 := Real.mul_self_sqrt (Nat.cast_nonneg N)
  have hb : Real.sqrt (N : ℝ) ≤ (ceilingRoot N : ℝ) := Nat.le_ceil _
  have hsq : (N : ℝ) ≤ (ceilingRoot N : ℝ) * ceilingRoot N := by nlinarith
  exact_mod_cast hsq

noncomputable def cumulativeConstant : ℝ := 11*(Real.log 2-1/2)/81200

lemma cumulativeConstant_pos : 0 < cumulativeConstant := by
  have h := radius_coefficient_pos
  unfold cumulativeConstant
  positivity

lemma late_radius_lower {N : ℕ} (hN : 2500 ≤ N) :
    cumulativeConstant * Real.sqrt N ≤
      ((N-24*ceilingRoot N : ℕ) : ℝ)*((1/8)*radiusConstant (ceilingRoot N)) := by
  obtain ⟨hb, _, h25⟩ := ceilingRoot_scale_bounds (show 600 ≤ N by omega)
  have ha : (0 : ℝ) < ((24*ceilingRoot N : ℕ) : ℝ) := by positivity
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hs : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hNp
  have hr := lower_bound_constant_assembly ha hNp h25 radius_coefficient_nonneg
    (risk := (1/8)*radiusConstant (ceilingRoot N)) le_rfl
  have hcount := late_count_lower hN
  have hcoef : 0 ≤ 11*(Real.log 2-1/2)/(40600*Real.sqrt N) := by
    exact div_nonneg (mul_nonneg (by norm_num) radius_coefficient_nonneg) (by positivity)
  have hm := mul_le_mul hcount hr hcoef (Nat.cast_nonneg (N-24*ceilingRoot N))
  calc
    cumulativeConstant * Real.sqrt N = (N : ℝ)/2 * (11*(Real.log 2-1/2)/(40600*Real.sqrt N)) := by
      unfold cumulativeConstant
      field_simp
      rw [Real.sq_sqrt (Nat.cast_nonneg N)]
      ring
    _ ≤ _ := hm

/-- Explicit square-root cumulative lower bound once the observable source good
event has been proved for all times in the common prior's valid range. -/
theorem cumulative_sqrt_lower_of_goodMass (N : ℕ) (hN : 2500 ≤ N)
    (hgood : ∀ t ∈ Ico (24*ceilingRoot N) N,
      1/8 ≤ goodPredictiveMass t (ceilingRoot N)) (q : RandomizedPredictor) :
    ENNReal.ofReal (cumulativeConstant * Real.sqrt N) ≤
      ⨆ μ : Law, cumulativeRisk N q μ := by
  have hb := (ceilingRoot_scale_bounds (show 600 ≤ N by omega)).1
  exact (ENNReal.ofReal_le_ofReal (late_radius_lower hN)).trans
    (cumulative_lower_of_goodMass hb hgood q)

theorem minimax_cumulative_sqrt_lower_of_goodMass (N : ℕ) (hN : 2500 ≤ N)
    (hgood : ∀ t ∈ Ico (24*ceilingRoot N) N,
      1/8 ≤ goodPredictiveMass t (ceilingRoot N)) :
    ENNReal.ofReal (cumulativeConstant * Real.sqrt N) ≤ minimaxCumulativeRisk N :=
  le_iInf (fun q => cumulative_sqrt_lower_of_goodMass N hN hgood q)

/-- The horizon-free algorithm supplies the corresponding actual minimax upper bound. -/
theorem minimax_cumulative_upper (N : ℕ) (hN : 1 ≤ N) :
    minimaxCumulativeRisk N ≤ ENNReal.ofReal
      (AnalyticBounds.partitionConstant * (2+Real.sqrt 2) * Real.sqrt N +
        (3*Real.log 2/2) * ((Nat.log2 N : ℝ)+1) * ((Nat.log2 N : ℝ)+2)) := by
  apply iInf_le_of_le AnytimePrediction.predictor
  apply iSup_le
  intro μ
  exact AnytimePrediction.cumulativeRisk_upper μ N hN


noncomputable def cumulativeUpperConstant : ℝ :=
  AnalyticBounds.partitionConstant*(2+Real.sqrt 2) +
    (3*Real.log 2/2)*(4/Real.log 2+2)^2

lemma cumulativeUpperConstant_pos : 0 < cumulativeUpperConstant := by
  have hc := AnalyticBounds.partitionConstant_pos
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold cumulativeUpperConstant
  positivity

/-- The logarithmic correction in G.2 is uniformly absorbed by a square-root
term, with an explicit horizon-independent constant. -/
lemma log2_polynomial_le_sqrt (N : ℕ) (hN : 1 ≤ N) :
    ((Nat.log2 N : ℝ)+1)*((Nat.log2 N : ℝ)+2) ≤
      (4/Real.log 2+2)^2 * Real.sqrt N := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let u := (N : ℝ)^(1/4 : ℝ)
  have hu1 : 1 ≤ u := Real.one_le_rpow hN1 (by norm_num)
  have hu0 : 0 ≤ u := by positivity
  have hu2 : u*u = Real.sqrt N := by
    dsimp [u]
    rw [← Real.rpow_add hNp, Real.sqrt_eq_rpow]
    norm_num
  have hp : (2 : ℝ)^(Nat.log2 N) ≤ N := by
    exact_mod_cast (show 2^(Nat.log2 N) ≤ N by
      rw [Nat.log2_eq_log_two]
      exact Nat.pow_log_le_self 2 (by omega : N ≠ 0))
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) < 2^(Nat.log2 N)) hp
  rw [Real.log_pow] at hlog
  have hJ : (Nat.log2 N : ℝ) ≤ Real.log (N : ℝ)/Real.log 2 :=
    (le_div_iff₀ hl).mpr hlog
  have hlogpow : Real.log (N : ℝ) ≤ 4*u := by
    have h := Real.log_le_rpow_div hNp.le (by norm_num : (0 : ℝ) < 1/4)
    dsimp [u]
    convert h using 1 <;> ring
  have hJ' : (Nat.log2 N : ℝ)+2 ≤ (4/Real.log 2+2)*u := by
    have hd := div_le_div_of_nonneg_right hlogpow hl.le
    have he : 4*u/Real.log 2 = (4/Real.log 2)*u := by ring
    rw [he] at hd
    linarith
  have hc : 0 ≤ 4/Real.log 2+2 := by positivity
  have hprod : ((Nat.log2 N : ℝ)+1)*((Nat.log2 N : ℝ)+2) ≤
      ((Nat.log2 N : ℝ)+2)*((Nat.log2 N : ℝ)+2) := by
    apply mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have hsquare := mul_self_le_mul_self (by positivity : (0 : ℝ) ≤ (Nat.log2 N : ℝ)+2) hJ'
  calc
    _ ≤ ((4/Real.log 2+2)*u)*((4/Real.log 2+2)*u) := hprod.trans hsquare
    _ = (4/Real.log 2+2)^2 * (u*u) := by ring
    _ = _ := by rw [hu2]

/-- A pure square-root upper rate for the one horizon-free source algorithm. -/
theorem anytime_cumulative_sqrt_upper (μ : Law) (N : ℕ) (hN : 1 ≤ N) :
    AnytimePrediction.cumulativeRisk μ N ≤ ENNReal.ofReal (cumulativeUpperConstant*Real.sqrt N) := by
  apply (AnytimePrediction.cumulativeRisk_upper μ N hN).trans
  apply ENNReal.ofReal_le_ofReal
  have hl : 0 ≤ 3*Real.log 2/2 := by positivity
  have h := mul_le_mul_of_nonneg_left (log2_polynomial_le_sqrt N hN) hl
  unfold cumulativeUpperConstant
  nlinarith

/-- The full pure-rate cumulative minimax upper bound, allowing all private kernels. -/
theorem minimax_cumulative_sqrt_upper (N : ℕ) (hN : 1 ≤ N) :
    minimaxCumulativeRisk N ≤ ENNReal.ofReal (cumulativeUpperConstant*Real.sqrt N) := by
  apply iInf_le_of_le AnytimePrediction.predictor
  apply iSup_le
  intro μ
  exact anytime_cumulative_sqrt_upper μ N hN

end Paper37.CumulativeLower
