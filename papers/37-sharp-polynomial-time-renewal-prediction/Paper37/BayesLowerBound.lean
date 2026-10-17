import Paper37.FiniteSupportLowerBound
import Paper37.PredictorSpec

namespace Paper37.BayesLowerBound
open scoped BigOperators ENNReal
open Paper37.LowerBound Paper37.SupportPrior Paper37.FiniteSupportLowerBound
open MeasureTheory

noncomputable section

/-- Exact finite Bayes reweighting identity, valid also for infinite KL loss. -/
lemma reweighted_kl_identity {α : Type*} [Fintype α] (P : FiniteLaw α)
    (ℓ : α → ℝ) (hℓ : ∀ z, 0 ≤ ℓ z) (hZ : 0 < P.expectation ℓ)
    (θ : α → ℝ) (q : ℝ) :
    ENNReal.ofReal (P.expectation ℓ) * (P.reweight ℓ hℓ hZ).expectedKL θ q =
      ∑ z, ENNReal.ofReal (P.mass z * ℓ z) * Paper37.Boundary.kl (θ z) q := by
  unfold FiniteLaw.expectedKL
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  rw [← mul_assoc, ← ENNReal.ofReal_mul hZ.le]
  congr 1
  congr 1
  change P.expectation ℓ * (P.mass z * ℓ z / P.expectation ℓ) = P.mass z * ℓ z
  field_simp

lemma reweighted_integrated_kl_identity {α Ω : Type*} [Fintype α] [MeasurableSpace Ω]
    (ρ : Measure Ω) (P : FiniteLaw α)
    (ℓ : α → ℝ) (hℓ : ∀ z, 0 ≤ ℓ z) (hZ : 0 < P.expectation ℓ)
    (θ : α → ℝ) (q : Ω → ℝ) (hq : Measurable q) :
    ENNReal.ofReal (P.expectation ℓ) *
        (∫⁻ ω, (P.reweight ℓ hℓ hZ).expectedKL θ (q ω) ∂ρ) =
      ∑ z, ENNReal.ofReal (P.mass z * ℓ z) *
        ∫⁻ ω, Paper37.Boundary.kl (θ z) (q ω) ∂ρ := by
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  simp_rw [reweighted_kl_identity P ℓ hℓ hZ θ]
  rw [lintegral_finset_sum _ (by
    intro z _
    exact measurable_const.mul ((Paper37.Boundary.measurable_kl_right (θ z)).comp hq))]
  apply Finset.sum_congr rfl
  intro z _
  exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- The observable source good event, using its first visible renewal and
completed-gap parser. All ages/gaps use the zero-based convention. -/
def GoodBlock (b : ℕ) (w : List Bool) : Prop :=
  ∃ j x, w = List.replicate j false ++ true :: x ∧
    Paper37.Renewal.ageFrom 0 x < 24 * b ∧
    Paper37.Renewal.ageFrom 0 x ∉ (Paper37.Renewal.gapsFrom 0 x).toFinset ∧
    (Paper37.Renewal.gapsFrom 0 x).length ≤ b

instance goodBlock_decidable (b : ℕ) (w : List Bool) : Decidable (GoodBlock b w) :=
  Classical.propDecidable _

def predictiveMass (b : ℕ) (w : List Bool) : ℝ :=
  (prior b).expectation (fun z => Paper37.Renewal.blockMass (law z) w)

lemma predictiveMass_nonneg (b : ℕ) (w : List Bool) : 0 ≤ predictiveMass b w :=
  (prior b).expectation_nonneg (fun z => Paper37.Renewal.blockMass_nonneg (law z) w)

def conditionalJointLoss (b : ℕ) (q : Paper37.Prediction.RandomizedPredictor) (w : List Bool) : ℝ≥0∞ :=
  ∑ z, ENNReal.ofReal ((prior b).mass z * Paper37.Renewal.blockMass (law z) w) *
    ∫⁻ r : Set.Icc (0 : ℝ) 1, Paper37.Boundary.kl (Paper37.Renewal.conditional (law z) w) r.val ∂(q w).toMeasure

def bayesRisk (n b : ℕ) (q : Paper37.Prediction.RandomizedPredictor) : ℝ≥0∞ :=
  ∑ z, ENNReal.ofReal ((prior b).mass z) * Paper37.Prediction.risk n q (law z)

def radiusConstant (b : ℕ) : ℝ :=
  (11 / 203) * (Real.log 2 - 1 / 2) / ((24 * b : ℕ) : ℝ)

lemma radiusConstant_nonneg (b : ℕ) : 0 ≤ radiusConstant b :=
  div_nonneg (mul_nonneg (by norm_num) radius_coefficient_nonneg) (Nat.cast_nonneg _)

/-- The actual source posterior lower bound multiplied by its actual
prior-predictive block probability. Null blocks are handled without dividing. -/
lemma goodBlock_conditionalJointLoss_lower {b : ℕ} (hb : 0 < b)
    (q : Paper37.Prediction.RandomizedPredictor) (w : List Bool) (hw : GoodBlock b w) :
    ENNReal.ofReal (predictiveMass b w) * ENNReal.ofReal (radiusConstant b) ≤
      conditionalJointLoss b q w := by
  by_cases hZ : 0 < predictiveMass b w
  · obtain ⟨j, x, rfl, hg, hunseen, hr⟩ := hw
    have hpost := actual_randomized_posterior_radius
      (q (List.replicate j false ++ true :: x)).toMeasure hb j x hZ hg hunseen hr
      (fun r : Set.Icc (0 : ℝ) 1 => r.val) (fun r => r.property)
    have hid := reweighted_integrated_kl_identity
      (q (List.replicate j false ++ true :: x)).toMeasure (prior b) (observationLikelihood j x)
      (fun z => Paper37.Renewal.blockMass_nonneg (law z) _) hZ
      (fun z => Paper37.Renewal.conditional (law z) (List.replicate j false ++ true :: x))
      (fun r : Set.Icc (0 : ℝ) 1 => r.val) measurable_subtype_coe
    exact (mul_le_mul_left' hpost (ENNReal.ofReal (predictiveMass b _))).trans_eq hid
  · have heq : predictiveMass b w = 0 :=
      le_antisymm (not_lt.mp hZ) (predictiveMass_nonneg b w)
    simp [heq]

lemma bayesRisk_eq_sum_jointLoss (n b : ℕ) (q : Paper37.Prediction.RandomizedPredictor) :
    bayesRisk n b q = ∑ w ∈ (Paper37.Renewal.words n).toFinset, conditionalJointLoss b q w := by
  unfold bayesRisk Paper37.Prediction.risk conditionalJointLoss
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w _
  apply Finset.sum_congr rfl
  intro z _
  rw [ENNReal.ofReal_mul ((prior b).nonneg z), mul_assoc]

def goodPredictiveMass (n b : ℕ) : ℝ :=
  ∑ w ∈ (Paper37.Renewal.words n).toFinset, if GoodBlock b w then predictiveMass b w else 0

lemma goodPredictiveMass_nonneg (n b : ℕ) : 0 ≤ goodPredictiveMass n b := by
  apply Finset.sum_nonneg
  intro w _
  by_cases hw : GoodBlock b w <;> simp [hw, predictiveMass_nonneg]

lemma goodMass_mul_radius_le_bayesRisk {b : ℕ} (hb : 0 < b) (n : ℕ)
    (q : Paper37.Prediction.RandomizedPredictor) :
    ENNReal.ofReal (goodPredictiveMass n b) * ENNReal.ofReal (radiusConstant b) ≤ bayesRisk n b q := by
  rw [bayesRisk_eq_sum_jointLoss]
  unfold goodPredictiveMass
  rw [ENNReal.ofReal_sum_of_nonneg (by
    intro w _
    by_cases hw : GoodBlock b w <;> simp [hw, predictiveMass_nonneg]), Finset.sum_mul]
  apply Finset.sum_le_sum
  intro w _
  by_cases hw : GoodBlock b w
  · simp only [if_pos hw]
    exact goodBlock_conditionalJointLoss_lower hb q w hw
  · simp [hw]

/-- A normalized finite prior's average risk is dominated by the worst-case
risk over actual finite-mean renewal laws. -/
lemma bayesRisk_le_worstRisk (n b : ℕ) (q : Paper37.Prediction.RandomizedPredictor) :
    bayesRisk n b q ≤ ⨆ μ : Paper37.Renewal.Law, Paper37.Prediction.risk n q μ := by
  have htotal : ∑ z, ENNReal.ofReal ((prior b).mass z) = 1 := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun z _ => (prior b).nonneg z), (prior b).total]
    simp
  calc
    _ ≤ ∑ z, ENNReal.ofReal ((prior b).mass z) *
        (⨆ μ : Paper37.Renewal.Law, Paper37.Prediction.risk n q μ) := by
      apply Finset.sum_le_sum
      intro z _
      exact mul_le_mul_left' (le_iSup (fun μ => Paper37.Prediction.risk n q μ) (law z)) _
    _ = _ := by rw [← Finset.sum_mul, htotal, one_mul]

/-- Final Bayes/minimax assembly; the remaining F.3 obligation is precisely
the observable good-event mass, rather than a risk lower bound premise. -/
lemma worstRisk_lower_of_goodMass {b : ℕ} (hb : 0 < b) (n : ℕ)
    (hgood : 1 / 8 ≤ goodPredictiveMass n b) (q : Paper37.Prediction.RandomizedPredictor) :
    ENNReal.ofReal ((1 / 8) * radiusConstant b) ≤
      ⨆ μ : Paper37.Renewal.Law, Paper37.Prediction.risk n q μ := by
  have hmass : ENNReal.ofReal (1 / 8 : ℝ) ≤ ENNReal.ofReal (goodPredictiveMass n b) :=
    ENNReal.ofReal_le_ofReal hgood
  rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 1 / 8)]
  exact (mul_le_mul_right' hmass _).trans
    ((goodMass_mul_radius_le_bayesRisk hb n q).trans (bayesRisk_le_worstRisk n b q))

def ceilingRoot (n : ℕ) : ℕ := Nat.ceil (Real.sqrt (n : ℝ))

/-- The source numerical scale conditions, at the stated cutoff n=600. -/
lemma ceilingRoot_scale_bounds {n : ℕ} (hn : 600 ≤ n) :
    0 < ceilingRoot n ∧ 24 * ceilingRoot n ≤ n ∧
      ((24 * ceilingRoot n : ℕ) : ℝ) ≤ 25 * Real.sqrt (n : ℝ) := by
  let s := Real.sqrt (n : ℝ)
  let b := ceilingRoot n
  have hnR : (600 : ℝ) ≤ n := by exact_mod_cast hn
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s * s = (n : ℝ) := Real.mul_self_sqrt (Nat.cast_nonneg _)
  have hspos : 0 < s := by nlinarith
  have hs24 : (24 : ℝ) ≤ s := by nlinarith
  have hbceil : (b : ℝ) < s + 1 := Nat.ceil_lt_add_one hs0
  have hle : s ≤ (b : ℝ) := Nat.le_ceil s
  have hbR : (0 : ℝ) < b := lt_of_lt_of_le hspos hle
  have hb : 0 < b := by exact_mod_cast hbR
  have hcast : ((24 * b : ℕ) : ℝ) = 24 * (b : ℝ) := by norm_num
  have h25 : ((24 * b : ℕ) : ℝ) ≤ 25 * s := by rw [hcast]; nlinarith
  have hAn : 24 * b ≤ n := by
    by_cases hn625 : 625 ≤ n
    · have hn625R : (625 : ℝ) ≤ n := by exact_mod_cast hn625
      have hs25 : (25 : ℝ) ≤ s := by nlinarith
      have hprod := mul_nonneg (sub_nonneg.mpr hs25) (show 0 ≤ s + 1 by linarith)
      have hR : ((24 * b : ℕ) : ℝ) ≤ (n : ℝ) := by rw [hcast]; nlinarith
      exact_mod_cast hR
    · have hn625R : (n : ℝ) < 625 := by exact_mod_cast (not_le.mp hn625)
      have hs25 : s ≤ (25 : ℝ) := by nlinarith
      have hb25 : b ≤ 25 := Nat.ceil_le.mpr hs25
      omega
  exact ⟨hb, hAn, h25⟩

/-- F.1's explicit constant after the actual good-event mass has been proved. -/
lemma worstRisk_f1_of_goodMass {n : ℕ} (hn : 600 ≤ n)
    (hgood : 1 / 8 ≤ goodPredictiveMass n (ceilingRoot n))
    (q : Paper37.Prediction.RandomizedPredictor) :
    ENNReal.ofReal (11 * (Real.log 2 - 1 / 2) / (40600 * Real.sqrt (n : ℝ))) ≤
      ⨆ μ : Paper37.Renewal.Law, Paper37.Prediction.risk n q μ := by
  obtain ⟨hb, _, ha25⟩ := ceilingRoot_scale_bounds hn
  have ha : (0 : ℝ) < ((24 * ceilingRoot n : ℕ) : ℝ) := by positivity
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have harith := lower_bound_constant_assembly ha hnR ha25 radius_coefficient_nonneg
    (risk := (1 / 8) * radiusConstant (ceilingRoot n)) (le_refl _)
  exact (ENNReal.ofReal_le_ofReal harith).trans (worstRisk_lower_of_goodMass hb n hgood q)

end
end Paper37.BayesLowerBound

