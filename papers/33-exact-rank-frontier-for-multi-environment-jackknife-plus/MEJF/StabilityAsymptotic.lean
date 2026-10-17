import MEJF.StabilityExtended
import MEJF.ActualAsymptotic

/-! The limiting rectangle (6.32) for the actual stable-class supremum,
including the equality a=alpha and the two literal zero-rank axes. -/
namespace MEJF.StabilityAsymptotic
open Setup StabilityExtended Filter Topology
noncomputable section

def Gamma (m n : ℕ) (alpha a b ε : ℝ) : ℝ :=
  StabilityExtended.gamma m n (failureRank alpha n) (innerRank a n) (outerRank b m) ε

def limitingFailure (alpha a b : ℝ) : ℝ :=
  if a = 0 ∨ b = 0 then 0 else if a ≤ alpha then b else 1

lemma shifted_rank_le (v : ℕ) (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) :
    ⌊a*(v+1 : ℕ)⌋₊ ≤ v := by
  have hv : (0 : ℝ) < (v+1 : ℕ) := by positivity
  have hh := (Nat.floor_lt (mul_nonneg ha hv.le)).mpr
    (show a*(v+1 : ℕ) < (v+1 : ℕ) by nlinarith)
  omega

/-- At and below a=alpha, the source's shifted inner floor never exceeds F. -/
lemma innerRank_le_failureRank (n : ℕ) (alpha a : ℝ)
    (ha : 0 ≤ a) (haα : a ≤ alpha) (hα1 : alpha < 1) :
    innerRank a n ≤ failureRank alpha n := by
  have hfloor := Nat.lt_floor_add_one (alpha*(n : ℝ))
  have hamul : a*(n : ℝ) ≤ alpha*n := mul_le_mul_of_nonneg_right haα (by positivity)
  have hraw : a*(n+1 : ℕ) < ((⌊alpha*(n : ℝ)⌋₊+2 : ℕ) : ℝ) := by
    push_cast
    nlinarith
  have hh := (Nat.floor_lt (mul_nonneg ha (by positivity))).mpr hraw
  have hnat : ⌊a*(n+1 : ℕ)⌋₊ ≤ ⌊alpha*(n : ℝ)⌋₊+1 := by omega
  simpa only [innerRank, failureRank, Nat.cast_add, Nat.cast_one] using hnat

lemma failureRank_le_n (n : ℕ) (hn : 0 < n) (alpha : ℝ)
    (hα : 0 ≤ alpha) (hα1 : alpha < 1) : failureRank alpha n ≤ n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hh := (Nat.floor_lt (mul_nonneg hα hnR.le)).mpr
    (show alpha*(n : ℝ) < n by nlinarith)
  unfold failureRank
  omega

lemma Gamma_zero_axis (m n : ℕ) (alpha a b ε : ℝ) (hε : 0 ≤ ε)
    (hb : 0 ≤ b) (hb1 : b < 1) (hz : a = 0 ∨ b = 0) :
    Gamma m n alpha a b ε = 0 := by
  unfold Gamma
  apply gamma_zero_rank m n (failureRank alpha n) (innerRank a n) (outerRank b m) ε hε
    (by unfold failureRank; omega)
    (by simpa only [outerRank, Nat.cast_add, Nat.cast_one] using shifted_rank_le m b hb hb1)
  rcases hz with rfl | rfl <;> simp [innerRank, outerRank]

/-- Actual stable-class Gamma converges to b for fixed positive levels a≤alpha,
and to one for a>alpha. Literal zero axes have limit zero. -/
theorem gamma_asymptotic {m n : ℕ → ℕ} {alpha a b ε : ℝ}
    (hm : Tendsto m atTop atTop) (hn : Tendsto n atTop atTop)
    (hα : 0 < alpha) (hα1 : alpha < 1) (ha : 0 ≤ a) (ha1 : a < 1)
    (hb : 0 ≤ b) (hb1 : b < 1) (hε : 0 ≤ ε) :
    Tendsto (fun k => Gamma (m k) (n k) alpha a b ε)
      atTop (𝓝 (limitingFailure alpha a b)) := by
  by_cases hz : a = 0 ∨ b = 0
  · rw [limitingFailure, if_pos hz]
    have heq : (fun k => Gamma (m k) (n k) alpha a b ε) = fun _ : ℕ => (0 : ℝ) := by
      funext k
      exact Gamma_zero_axis _ _ alpha a b ε hε hb hb1 hz
    rw [heq]
    exact tendsto_const_nhds
  have ha0 : 0 < a := by rcases not_or.mp hz with ⟨h, _⟩; exact lt_of_le_of_ne ha (Ne.symm h)
  have hb0 : 0 < b := by rcases not_or.mp hz with ⟨_, h⟩; exact lt_of_le_of_ne hb (Ne.symm h)
  have hfinite := (ActualAsymptotic.eventually_finite_shifted_rank hn ha0 ha1).and
    (ActualAsymptotic.eventually_finite_shifted_rank hm hb0 hb1)
  rw [limitingFailure, if_neg hz]
  by_cases hlow : a ≤ alpha
  · rw [if_pos hlow]
    have hm1 : Tendsto (fun k => m k+1) atTop atTop := (tendsto_add_atTop_nat 1).comp hm
    have hN : Tendsto (fun k => ((m k+1 : ℕ) : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp hm1
    have hlim := (tendsto_nat_floor_mul_div_atTop hb).comp hN
    apply hlim.congr'
    filter_upwards [hfinite, hn.eventually_gt_atTop 0] with k hk hnk
    have hk' : (1 ≤ innerRank a (n k) ∧ innerRank a (n k) ≤ n k) ∧
        1 ≤ outerRank b (m k) ∧ outerRank b (m k) ≤ m k := by
      simpa only [innerRank, outerRank, Nat.cast_add, Nat.cast_one] using hk
    have hFn := failureRank_le_n (n k) hnk alpha hα.le hα1
    have htF := innerRank_le_failureRank (n k) alpha a ha hlow hα1
    dsimp [Gamma]
    rw [StabilityExtended.gamma_eq (m k) (n k) (failureRank alpha (n k))
      (innerRank a (n k)) (outerRank b (m k)) ε hε (by unfold failureRank; omega)
      hFn hk'.1.2 hk'.2.2,
      if_neg (by omega), if_neg (not_lt.mpr htF)]
    simp only [outerRank, Nat.cast_add, Nat.cast_one]
  · rw [if_neg hlow]
    have hF := RankFrontier.tendsto_failureThreshold_ratio hn hα.le
    have hT := RankFrontier.tendsto_shifted_floor_ratio hn ha
    have hnR : Tendsto (fun k => (n k : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hn
    apply tendsto_const_nhds.congr'
    filter_upwards [hfinite, hn.eventually_gt_atTop 0,
      hF.eventually_lt hT (lt_of_not_ge hlow), hnR.eventually_gt_atTop 0] with k hk hnk hlt hnRk
    have hk' : (1 ≤ innerRank a (n k) ∧ innerRank a (n k) ≤ n k) ∧
        1 ≤ outerRank b (m k) ∧ outerRank b (m k) ≤ m k := by
      simpa only [innerRank, outerRank, Nat.cast_add, Nat.cast_one] using hk
    have hFt : failureRank alpha (n k) < innerRank a (n k) := by
      have hh := (div_lt_div_iff_of_pos_right hnRk).mp hlt
      have hh' : ⌊alpha*(n k : ℝ)⌋₊+1 < ⌊a*(n k+1 : ℕ)⌋₊ := by exact_mod_cast hh
      simpa only [failureRank, innerRank, Nat.cast_add, Nat.cast_one] using hh' 
    have hFn := failureRank_le_n (n k) hnk alpha hα.le hα1
    dsimp [Gamma]
    rw [StabilityExtended.gamma_eq (m k) (n k) (failureRank alpha (n k))
      (innerRank a (n k)) (outerRank b (m k)) ε hε (by unfold failureRank; omega)
      hFn hk'.1.2 hk'.2.2, if_neg (by omega), if_pos hFt]

/-- Exact limiting region on [0,1)^2: the positive rectangle plus zero axes. -/
theorem limiting_validity_iff (alpha a b δ : ℝ) (hδ : 0 ≤ δ) (hδ1 : δ < 1) :
    limitingFailure alpha a b ≤ δ ↔ a = 0 ∨ b = 0 ∨ (a ≤ alpha ∧ b ≤ δ) := by
  by_cases hz : a = 0 ∨ b = 0
  · simp only [limitingFailure, if_pos hz]
    constructor
    · intro _; rcases hz with h | h; exact Or.inl h; exact Or.inr (Or.inl h)
    · intro _; exact hδ
  · have ha : a ≠ 0 := (not_or.mp hz).1
    have hb : b ≠ 0 := (not_or.mp hz).2
    by_cases hlow : a ≤ alpha
    · simp [limitingFailure, hz, hlow, ha, hb]
    · simp [limitingFailure, hz, hlow, ha, hb, not_le.mpr hδ1]

/-- Among fixed positive levels the limiting validity set is precisely (6.32). -/
theorem positive_limiting_rectangle (alpha a b δ : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hδ : 0 ≤ δ) (hδ1 : δ < 1) :
    limitingFailure alpha a b ≤ δ ↔ a ≤ alpha ∧ b ≤ δ := by
  rw [limiting_validity_iff alpha a b δ hδ hδ1]
  simp [ne_of_gt ha, ne_of_gt hb]

/-- The source's single assumption min(m,n)→∞ implies both divergences. -/
theorem gamma_asymptotic_of_min {m n : ℕ → ℕ} {alpha a b ε : ℝ}
    (hmin : Tendsto (fun k => min (m k) (n k)) atTop atTop)
    (hα : 0 < alpha) (hα1 : alpha < 1) (ha : 0 ≤ a) (ha1 : a < 1)
    (hb : 0 ≤ b) (hb1 : b < 1) (hε : 0 ≤ ε) :
    Tendsto (fun k => Gamma (m k) (n k) alpha a b ε)
      atTop (𝓝 (limitingFailure alpha a b)) :=
  gamma_asymptotic (tendsto_atTop_mono (fun k => min_le_left (m k) (n k)) hmin)
    (tendsto_atTop_mono (fun k => min_le_right (m k) (n k)) hmin)
    hα hα1 ha ha1 hb hb1 hε

/-- The limit of the actual experiment has exactly the positive-level rectangle. -/
theorem actual_limiting_rectangle {m n : ℕ → ℕ} {alpha a b ε δ : ℝ}
    (hmin : Tendsto (fun k => min (m k) (n k)) atTop atTop)
    (hα : 0 < alpha) (hα1 : alpha < 1) (ha : 0 < a) (ha1 : a < 1)
    (hb : 0 < b) (hb1 : b < 1) (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (hδ1 : δ < 1) :
    ∃ L : ℝ, Tendsto (fun k => Gamma (m k) (n k) alpha a b ε) atTop (𝓝 L) ∧
      (L ≤ δ ↔ a ≤ alpha ∧ b ≤ δ) :=
  ⟨limitingFailure alpha a b,
    gamma_asymptotic_of_min hmin hα hα1 ha.le ha1 hb.le hb1 hε,
    positive_limiting_rectangle alpha a b δ ha hb hδ hδ1⟩

end
end MEJF.StabilityAsymptotic
