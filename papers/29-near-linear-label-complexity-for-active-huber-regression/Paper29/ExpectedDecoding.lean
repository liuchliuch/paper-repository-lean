import Paper29.DecodingLoss
import Paper29.Transcript

noncomputable section
open scoped BigOperators Classical
namespace Paper29.HardDistribution
open Transcript

theorem expected_bad_blocks {r N : ℕ} (hN : 0 < N) (β : ℝ)
    (hβ : 0 ≤ β) (hβhi : β ≤ 1/2) (hscale : 10 ≤ (N:ℝ)*β^2) :
    (∑ s : Signs r, ∑ y : Bits r N, hardMass β s y*badBlockCount β s y) ≤ Real.exp (-5)*r := by
  have he (s : Signs r) :
      (∑ y : Bits r N, conditionalMass β s y*badBlockCount β s y) ≤ Real.exp (-5)*r := by
    unfold badBlockCount
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    have hs : (∑ j : Fin r, ∑ y : Bits r N, conditionalMass β s y*(if GoodBlock β s y j then 0 else 1)) ≤
        ∑ _j : Fin r, Real.exp (-5) := by
      apply Finset.sum_le_sum
      intro j _
      have hh := conditional_bad_block_bound hN β hβ hβhi hscale s j
      simpa only [Sampling.eventMass,Finset.sum_filter,mul_ite,mul_zero,mul_one,ite_not] using hh
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_comm] using hs
  have hs : (∑ s : Signs r, ∑ y : Bits r N, hardMass β s y*badBlockCount β s y) ≤
      ∑ s : Signs r, signMass r s*(Real.exp (-5)*r) := by
    apply Finset.sum_le_sum
    intro s _
    unfold hardMass
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (he s) (by unfold signMass; positivity)
  apply hs.trans_eq
  rw [← Finset.sum_mul,signMass_total,one_mul]

theorem hamming_le_rank {r : ℕ} (s t : Signs r) : RateDistortion.hamming s t ≤ r := by
  unfold RateDistortion.hamming
  have hh : (∑ j : Fin r, if s j=t j then (0:ℝ) else 1) ≤ ∑ _j : Fin r, (1:ℝ) := by
    apply Finset.sum_le_sum
    intro j _
    split_ifs <;> norm_num
  simpa using hh

theorem finite_event_complement {Ω : Type*} [Fintype Ω] (P : Law Ω) (E : Ω → Prop)
    [DecidablePred E] :
    Sampling.eventMass P.weight (Finset.univ.filter E) +
      Sampling.eventMass P.weight (Finset.univ.filter (fun ω => ¬E ω)) = 1 := by
  simp only [Sampling.eventMass,Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  convert P.total using 1
  apply Finset.sum_congr rfl
  intro ω _
  by_cases he : E ω <;> simp [he]

/-- The paper's full decoding-error aggregation (4.8) for any finite joint
law with the actual hard response marginal and the true regression success
event. No expected-decoding certificate is assumed. -/
theorem finite_expected_hamming_lt {Ω : Type*} [Fintype Ω] {r N : ℕ}
    (P : Law Ω) (source : Ω → Signs r) (responses : Ω → Bits r N) (x : Ω → Fin r → ℝ)
    (E : Ω → Prop) [DecidablePred E] (hr : 1 ≤ r) (hN : 0 < N) (β ε : ℝ)
    (hβ : 0 < β) (hβhi : β ≤ 1/2) (hscale : 10 ≤ (N:ℝ)*β^2)
    (hε : 0 ≤ ε) (hεhi : ε ≤ 1) (hβε : 200*ε ≤ β)
    (hmarginal : ∀ s y, P.mass (fun ω => (source ω,responses ω)) (s,y) = hardMass β s y)
    (hsuccess : (99/100:ℝ) ≤ Sampling.eventMass P.weight (Finset.univ.filter E))
    (hgood : ∀ ω, E ω → Real.sqrt (productLoss (responses ω) (x ω)) ≤
      (1+ε)*Real.sqrt (productLoss (responses ω) (productOpt (responses ω)))) :
    (∑ ω, P.weight ω*RateDistortion.hamming (source ω) (fun j => decode (x ω j))) < (1/25:ℝ)*r := by
  have hbad : (∑ ω, P.weight ω*badBlockCount β (source ω) (responses ω)) ≤ Real.exp (-5)*r := by
    have he := P.sum_mass_mul (fun ω => (source ω,responses ω))
      (fun a : Signs r × Bits r N => badBlockCount β a.1 a.2)
    rw [Fintype.sum_prod_type] at he
    simp_rw [hmarginal] at he
    rw [← he]
    exact expected_bad_blocks hN β hβ.le hβhi hscale
  have hfail : Sampling.eventMass P.weight (Finset.univ.filter (fun ω => ¬E ω)) ≤ (1/100:ℝ) := by
    have hc := finite_event_complement P E
    linarith
  have hpoint (ω : Ω) : RateDistortion.hamming (source ω) (fun j => decode (x ω j)) ≤
      badBlockCount β (source ω) (responses ω) + (9/400:ℝ)*r +
        if E ω then 0 else (r:ℝ) := by
    by_cases he : E ω
    · rw [if_pos he,add_zero]
      exact (hamming_le_bad_add_wrong β (source ω) (responses ω) (x ω)).trans (add_le_add_left
        (successful_wrong_good_count hN β ε hβ hε hεhi hβε (source ω) (responses ω) (x ω) (hgood ω he)) _)
    · rw [if_neg he]
      have hb : 0 ≤ badBlockCount β (source ω) (responses ω) := by
        apply Finset.sum_nonneg
        intro j _
        split_ifs <;> norm_num
      have hr0 : (0:ℝ) ≤ r := Nat.cast_nonneg r
      have hh := hamming_le_rank (source ω) (fun j => decode (x ω j))
      linarith
  have hs := Finset.sum_le_sum (s:=Finset.univ) (fun ω _ => mul_le_mul_of_nonneg_left (hpoint ω) (P.nonneg ω))
  have hfailure : (∑ ω, P.weight ω*(if E ω then 0 else (r:ℝ))) =
      Sampling.eventMass P.weight (Finset.univ.filter (fun ω => ¬E ω))*r := by
    simp only [Sampling.eventMass,Finset.sum_filter,mul_ite,mul_zero,ite_not,Finset.sum_mul,ite_mul,zero_mul]
  simp_rw [mul_add] at hs
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib,← Finset.sum_mul,P.total,one_mul,hfailure] at hs
  have hf := mul_le_mul_of_nonneg_right hfail (Nat.cast_nonneg r)
  have hdec := mul_lt_mul_of_pos_right decoding_coefficient_lt (show (0:ℝ)<r by exact_mod_cast hr)
  nlinarith only [hs,hbad,hf,hdec]

end Paper29.HardDistribution
