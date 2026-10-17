import Paper29.ExpectedDecoding

noncomputable section
open scoped BigOperators Classical
namespace Paper29.HardDistribution
open Transcript

theorem finite_expected_hamming_of_good_bound {Ω : Type*} [Fintype Ω] {r N : ℕ}
    (P : Law Ω) (source : Ω → Signs r) (responses : Ω → Bits r N) (estimate : Ω → Signs r)
    (E : Ω → Prop) [DecidablePred E] (hr : 1 ≤ r) (hN : 0 < N) (β : ℝ)
    (hβ : 0 < β) (hβhi : β ≤ 1/2) (hscale : 10 ≤ (N:ℝ)*β^2)
    (hmarginal : ∀ s y, P.mass (fun ω => (source ω,responses ω)) (s,y) = hardMass β s y)
    (hsuccess : (99/100:ℝ) ≤ Sampling.eventMass P.weight (Finset.univ.filter E))
    (hgood : ∀ ω, E ω → RateDistortion.hamming (source ω) (estimate ω) ≤
      badBlockCount β (source ω) (responses ω) + (9/400:ℝ)*r) :
    (∑ ω, P.weight ω*RateDistortion.hamming (source ω) (estimate ω)) < (1/25:ℝ)*r := by
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
  have hpoint (ω : Ω) : RateDistortion.hamming (source ω) (estimate ω) ≤
      badBlockCount β (source ω) (responses ω) + (9/400:ℝ)*r +
        if E ω then 0 else (r:ℝ) := by
    by_cases he : E ω
    · rw [if_pos he,add_zero]
      exact hgood ω he
    · rw [if_neg he]
      have hb : 0 ≤ badBlockCount β (source ω) (responses ω) := by
        apply Finset.sum_nonneg
        intro j _
        split_ifs <;> norm_num
      have hr0 : (0:ℝ) ≤ r := Nat.cast_nonneg r
      have hh := hamming_le_rank (source ω) (estimate ω)
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
