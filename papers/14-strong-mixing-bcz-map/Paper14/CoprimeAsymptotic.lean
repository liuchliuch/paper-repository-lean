import Paper14.CoprimeRectangle
import Paper14.DivisorRatios
import Paper14.MoebiusSeries
import Paper14.SieveVariance
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Real.Pi.Bounds

open Finset Filter Topology
namespace Paper14
noncomputable section

def appendixMobiusTerm (n d : ℕ) : ℝ :=
  ((ArithmeticFunction.moebius d : ℤ) : ℝ)*
    ((((Finset.Ioc (n/6) (n/3)).filter (fun p => d ∣ p)).card : ℝ)/(n : ℝ))*
    ((((Finset.Ioc ((n-1)/2) n).filter (fun q => d ∣ q)).card : ℝ)/(n : ℝ))

lemma appendixMobiusTerm_tendsto (d : ℕ) :
    Tendsto (fun n => appendixMobiusTerm n d) atTop
      (𝓝 (((ArithmeticFunction.moebius d : ℤ) : ℝ)/(12*(d : ℝ)^2))) := by
  have h := ((appendix_p_multiples_ratio d).const_mul ((ArithmeticFunction.moebius d : ℤ) : ℝ)).mul
    (appendix_q_multiples_ratio d)
  change Tendsto (fun n => appendixMobiusTerm n d) atTop _ at h
  convert h using 1
  by_cases hd : d = 0
  · simp [hd]
  · have hdr : (d : ℝ) ≠ 0 := by exact_mod_cast hd
    field_simp
    ring

lemma appendixMobiusTerm_bound (n d : ℕ) :
    ‖appendixMobiusTerm n d‖ ≤ ((d : ℝ)^2)⁻¹ := by
  by_cases hn : n = 0
  · simp [appendixMobiusTerm,hn]
  by_cases hd : d = 0
  · simp [appendixMobiusTerm,hd,Ioc_filter_dvd_card]
  have hnr : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hdr : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero hd
  let P := ((Finset.Ioc (n/6) (n/3)).filter (fun p => d ∣ p)).card
  let Q := ((Finset.Ioc ((n-1)/2) n).filter (fun q => d ∣ q)).card
  have hP : P*d ≤ n := by
    dsimp [P]
    rw [Ioc_filter_dvd_card]
    exact (Nat.mul_le_mul_right d (Nat.sub_le _ _)).trans
      ((Nat.div_mul_le_self _ _).trans (Nat.div_le_self n 3))
  have hQ : Q*d ≤ n := by
    dsimp [Q]
    rw [Ioc_filter_dvd_card]
    exact (Nat.mul_le_mul_right d (Nat.sub_le _ _)).trans (Nat.div_mul_le_self n d)
  have hPr : (P : ℝ)/(n : ℝ) ≤ (d : ℝ)⁻¹ := by
    apply (div_le_iff₀ hnr).mpr
    rw [inv_mul_eq_div]
    apply (le_div_iff₀ hdr).mpr
    exact_mod_cast hP
  have hQr : (Q : ℝ)/(n : ℝ) ≤ (d : ℝ)⁻¹ := by
    apply (div_le_iff₀ hnr).mpr
    rw [inv_mul_eq_div]
    apply (le_div_iff₀ hdr).mpr
    exact_mod_cast hQ
  have hmu : ‖((ArithmeticFunction.moebius d : ℤ) : ℝ)‖ ≤ 1 := by
    rw [Real.norm_eq_abs]
    exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := d))
  have hp0 : (0 : ℝ) ≤ (P : ℝ)/(n : ℝ) := by positivity
  have hq0 : (0 : ℝ) ≤ (Q : ℝ)/(n : ℝ) := by positivity
  change ‖((ArithmeticFunction.moebius d : ℤ) : ℝ)*((P : ℝ)/(n : ℝ))*((Q : ℝ)/(n : ℝ))‖ ≤ _
  rw [norm_mul,norm_mul,Real.norm_of_nonneg hp0,Real.norm_of_nonneg hq0]
  calc _ ≤ (1*(d : ℝ)⁻¹)*(d : ℝ)⁻¹ :=
      mul_le_mul (mul_le_mul hmu hPr hp0 (by norm_num)) hQr hq0 (by positivity)
       _ = _ := by simp [pow_two,mul_inv]

lemma appendixMobiusTerm_eq_zero_of_lt {n d : ℕ} (hnd : n < d) : appendixMobiusTerm n d = 0 := by
  have hp : n/3 < d := (Nat.div_le_self n 3).trans_lt hnd
  have hl : n/6 < d := (Nat.div_le_self n 6).trans_lt hnd
  simp [appendixMobiusTerm,Ioc_filter_dvd_card,Nat.div_eq_of_lt hp,Nat.div_eq_of_lt hl]

lemma coprimePairCount_eq_tsum (n : ℕ) :
    (coprimePairCount n : ℝ)/(n : ℝ)^2 = ∑' d : ℕ, appendixMobiusTerm n d := by
  rw [tsum_eq_sum (s := Finset.range (n+1)) (fun d hd => appendixMobiusTerm_eq_zero_of_lt (by
    have hdn : ¬ d < n+1 := by simpa only [Finset.mem_range] using hd
    omega))]
  have hA : ∀ p ∈ Finset.Ioc (n/6) (n/3), 0 < p := by
    intro p hp
    simp only [Finset.mem_Ioc] at hp
    omega
  have hB : ∀ q ∈ Finset.Ioc ((n-1)/2) n, 0 < q := by
    intro q hq
    simp only [Finset.mem_Ioc] at hq
    omega
  have hN : ∀ p ∈ Finset.Ioc (n/6) (n/3), p ≤ n := by
    intro p hp
    exact (Finset.mem_Ioc.mp hp).2.trans (Nat.div_le_self n 3)
  have h := coprime_rectangle_moebius _ _ n hA hB hN
  rw [coprimePairCount_eq_Ioc]
  rw [h,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro d hd
  dsimp [appendixMobiusTerm]
  ring

/-- The actual asymptotic in Appendix A (23), for the original restricted
coprime rectangle. The proof passes the exact divisor expansion through a
summable reciprocal-square bound. -/
theorem coprimePairCount_asymptotic :
    Tendsto (fun n : ℕ => (coprimePairCount n : ℝ)/(n : ℝ)^2) atTop
      (𝓝 (1/(2*Real.pi^2))) := by
  simp_rw [coprimePairCount_eq_tsum]
  have ht := tendsto_tsum_of_dominated_convergence summable_invSq appendixMobiusTerm_tendsto
    (Eventually.of_forall appendixMobiusTerm_bound)
  have heq : (fun d : ℕ => ((ArithmeticFunction.moebius d : ℤ) : ℝ)/(12*(d : ℝ)^2)) =
      (fun d => (1/12 : ℝ)*(((ArithmeticFunction.moebius d : ℤ) : ℝ)/(d : ℝ)^2)) := by
    funext d
    ring
  rw [heq,tsum_mul_left,tsum_moebius_invSq] at ht
  convert ht using 1
  ring

/-- The original explicit n^2/20 lower bound used by Appendix A. -/
theorem coprimeCountLower : CoprimeCountLowerStatement := by
  have hpi : Real.pi^2 < 10 := by nlinarith [Real.pi_lt_d2,Real.pi_pos]
  have hconst : (1 : ℝ)/20 < 1/(2*Real.pi^2) := by
    apply (div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 20) (by positivity : (0 : ℝ) < 2*Real.pi^2)).mpr
    nlinarith
  obtain ⟨N,hN⟩ := Filter.eventually_atTop.mp (coprimePairCount_asymptotic.eventually (Ioi_mem_nhds hconst))
  refine ⟨max N 1,fun n hn => ?_⟩
  have hnr : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hh := (le_div_iff₀ (sq_pos_of_pos hnr)).mp ((hN n (by omega)).le)
  nlinarith

end
end Paper14
