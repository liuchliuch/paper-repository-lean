import MEJF.MainExact
import MEJF.ExtendedRule
import MEJF.Asymptotic

/-! Corollary 3.4 and its phase consequences for the actual statistical rule,
including finite early samples with rank zero. -/
namespace MEJF.ActualAsymptotic
open MEJF.Setup Filter Topology
noncomputable section

/-- The paper's Γ with the actual rounded levels and infinite-endpoint convention. -/
def Gamma (m n : ℕ) (alpha a b : ℝ) : ℝ :=
  ExtendedRule.gamma m n alpha (innerRank a n) (outerRank b m)

lemma shifted_rank_le (v : ℕ) {a : ℝ} (ha : 0 ≤ a) (ha1 : a < 1) :
    ⌊a*(v+1:ℕ)⌋₊ ≤ v := by
  have hs : (0:ℝ) < (v+1:ℕ) := by positivity
  have hu : ⌊a*(v+1:ℕ)⌋₊ < v+1 :=
    (Nat.floor_lt (mul_nonneg ha hs.le)).mpr (by nlinarith)
  omega

/-- The complete statistical law, including both literal rank-zero axes. -/
theorem gamma_full_rank_law (m n : ℕ) (alpha : ℝ) (ha : 0 ≤ alpha) (ha1 : alpha < 1)
    (t ell : ℕ) (ht : t ≤ n) (he : ell ≤ m) :
    ExtendedRule.gamma m n alpha t ell =
      if t=0 ∨ ell=0 then 0 else RankFrontier.failureRate m (failureRank alpha n) t ell := by
  by_cases hz : t=0 ∨ ell=0
  · rw [if_pos hz]
    exact ExtendedRule.gamma_zero m n alpha t ell he hz
  · rw [if_neg hz]
    have ht' : 1 ≤ t ∧ t ≤ n := by omega
    have he' : 1 ≤ ell ∧ ell ≤ m := by omega
    rw [ExtendedRule.gamma_finite m n alpha t ell ht' he',
      MainExact.finiteRankGamma_eq m n alpha ha ha1 t ell ht' he']

/-- The source's all-level law on its fixed universal experiment. -/
theorem Gamma_law (m n : ℕ) (alpha a b : ℝ) (halpha : 0 ≤ alpha) (halpha1 : alpha < 1)
    (ha : 0 ≤ a) (ha1 : a < 1) (hb : 0 ≤ b) (hb1 : b < 1) :
    Gamma m n alpha a b = if innerRank a n=0 ∨ outerRank b m=0 then 0 else
      RankFrontier.failureRate m (failureRank alpha n) (innerRank a n) (outerRank b m) := by
  apply gamma_full_rank_law m n alpha halpha halpha1
  · simpa only [innerRank,Nat.cast_add,Nat.cast_one] using shifted_rank_le n ha ha1
  · simpa only [outerRank,Nat.cast_add,Nat.cast_one] using shifted_rank_le m hb hb1

@[simp] theorem Gamma_zero_b (m n : ℕ) (alpha a : ℝ) : Gamma m n alpha a 0 = 0 := by
  unfold Gamma
  have he : outerRank 0 m = 0 := by simp [outerRank]
  rw [he]
  exact ExtendedRule.gamma_zero m n alpha _ 0 (by omega) (Or.inr rfl)

@[simp] theorem Gamma_zero_a (m n : ℕ) (alpha b : ℝ) (hb : 0 ≤ b) (hb1 : b < 1) :
    Gamma m n alpha 0 b = 0 := by
  unfold Gamma
  have ht : innerRank 0 n = 0 := by simp [innerRank]
  rw [ht]
  apply ExtendedRule.gamma_zero m n alpha 0 _ _ (Or.inl rfl)
  simpa only [outerRank,Nat.cast_add,Nat.cast_one] using shifted_rank_le m hb hb1

lemma eventually_finite_shifted_rank {v : ℕ → ℕ} {a : ℝ}
    (hv : Tendsto v atTop atTop) (ha : 0 < a) (ha1 : a < 1) :
    ∀ᶠ k in atTop, 1 ≤ ⌊a*(v k+1:ℕ)⌋₊ ∧ ⌊a*(v k+1:ℕ)⌋₊ ≤ v k := by
  have hr := RankFrontier.tendsto_shifted_floor_ratio hv ha.le
  have hp : ∀ᶠ k in atTop, (0:ℝ) < (⌊a*(v k+1:ℕ)⌋₊:ℝ) / v k :=
    (tendsto_order.1 hr).1 0 ha
  filter_upwards [hp, hv.eventually_gt_atTop 0] with k hk hvk
  have hvR : (0:ℝ) < v k := by exact_mod_cast hvk
  have hpR : (0:ℝ) < (⌊a*(v k+1:ℕ)⌋₊:ℝ) :=
    (div_pos_iff_of_pos_right hvR).mp hk
  have hnat : 0 < ⌊a*(v k+1:ℕ)⌋₊ := by exact_mod_cast hpR
  have hs : (0:ℝ) < (v k+1:ℕ) := by positivity
  have hu : ⌊a*(v k+1:ℕ)⌋₊ < v k+1 :=
    (Nat.floor_lt (mul_nonneg ha.le hs.le)).mpr (by nlinarith)
  omega

/-- Actual Γ equals the proved scalar law eventually; no rank convention is
changed on the finite initial segment. -/
lemma eventually_Gamma_eq_formula {m n : ℕ → ℕ} {a b alpha : ℝ}
    (hm : Tendsto m atTop atTop) (hn : Tendsto n atTop atTop)
    (ha : 0 < a) (ha1 : a < 1) (hb : 0 < b) (hb1 : b < 1)
    (halpha : 0 ≤ alpha) (halpha1 : alpha < 1) :
    ∀ᶠ k in atTop, Gamma (m k) (n k) alpha a b =
      RankFrontier.failureRate (m k) (failureRank alpha (n k))
        (innerRank a (n k)) (outerRank b (m k)) := by
  filter_upwards [eventually_finite_shifted_rank hn ha ha1,
    eventually_finite_shifted_rank hm hb hb1] with k ht he
  have ht' : 1 ≤ innerRank a (n k) ∧ innerRank a (n k) ≤ n k := by
    simpa only [innerRank,Nat.cast_add,Nat.cast_one] using ht
  have he' : 1 ≤ outerRank b (m k) ∧ outerRank b (m k) ≤ m k := by
    simpa only [outerRank,Nat.cast_add,Nat.cast_one] using he
  rw [Gamma, ExtendedRule.gamma_finite (m k) (n k) alpha
    (innerRank a (n k)) (outerRank b (m k)) ht' he',
    MainExact.finiteRankGamma_eq _ _ _ halpha halpha1 _ _ ht' he']

/-- Corollary 3.4, equation (3.15), for the independently defined statistical
supremum over the actual learner/law experiment. -/
theorem gamma_asymptotic {m n : ℕ → ℕ} {a b alpha : ℝ}
    (hm : Tendsto m atTop atTop) (hn : Tendsto n atTop atTop)
    (ha : 0 < a) (ha1 : a < 1) (hb : 0 < b) (hb1 : b < 1)
    (halpha : 0 < alpha) (halpha1 : alpha < 1) :
    Tendsto (fun k => Gamma (m k) (n k) alpha a b)
      atTop (𝓝 (RankFrontier.limitingRate a b alpha)) := by
  apply (RankFrontier.arithmetic_asymptotic hm hn ha hb halpha halpha1).congr'
  filter_upwards [eventually_Gamma_eq_formula hm hn ha ha1 hb hb1 halpha.le halpha1]
    with k hk
  simpa only [failureRank, innerRank, outerRank,Nat.cast_add,Nat.cast_one] using hk.symm

/-- The paper states divergence through `min {m,n}`; it implies both component
limits without requiring a relation between their rates of growth. -/
theorem gamma_asymptotic_min {m n : ℕ → ℕ} {a b alpha : ℝ}
    (hmin : Tendsto (fun k => min (m k) (n k)) atTop atTop)
    (ha : 0 < a) (ha1 : a < 1) (hb : 0 < b) (hb1 : b < 1)
    (halpha : 0 < alpha) (halpha1 : alpha < 1) :
    Tendsto (fun k => Gamma (m k) (n k) alpha a b)
      atTop (𝓝 (RankFrontier.limitingRate a b alpha)) :=
  gamma_asymptotic (tendsto_atTop_mono (fun k => min_le_left (m k) (n k)) hmin)
    (tendsto_atTop_mono (fun k => min_le_right (m k) (n k)) hmin)
    ha ha1 hb hb1 halpha halpha1

/-- The validity side (3.16) is the exact side of the actual limiting failure law. -/
theorem limiting_validity_iff {a b alpha delta : ℝ}
    (ha : 0 < a) (hb : 0 < b) (halpha : 0 < alpha)
    (hd : 0 < delta) (hd1 : delta < 1) :
    RankFrontier.limitingRate a b alpha ≤ delta ↔ a/alpha+2*b/delta ≤ 1 :=
  RankFrontier.limiting_budget_iff ha hb halpha hd hd1

/-- The complete-failure limit phase (3.18). -/
theorem limiting_complete_failure_iff {a b alpha : ℝ} (halpha : 0 < alpha) :
    RankFrontier.limitingRate a b alpha = 1 ↔
      alpha ≤ a ∨ (a < alpha ∧ 1 ≤ a/alpha+2*b) :=
  RankFrontier.limiting_complete_failure_iff halpha

end
end MEJF.ActualAsymptotic
