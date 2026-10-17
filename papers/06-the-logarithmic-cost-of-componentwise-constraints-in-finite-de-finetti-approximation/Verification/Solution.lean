import Verification.Statements

noncomputable section
open Paper06
namespace Paper06.Challenge

theorem lemma_2_1_posterior : Specification.Lemma21_Posterior := by
  intro κ α _ _ _ t Γ η P hP c hCP i I hi z hz
  exact Posterior.lemma_2_1_posterior_preservation Γ η P hP c hCP i I hi z hz

theorem prop_2_2_conditioning : Specification.Prop22_Conditioning := by
  intro α _ t Γ η n k P hP c hCP hk hn
  exact proposition_2_2 Γ η P hP c hCP hk hn

theorem thm_3_1_logarithmic : Specification.Thm31_Logarithmic := by
  intro θ hθ hθhalf n hn hEven r hr hparam
  exact theorem_3_1_prime θ hθ hθhalf n hn hEven r hr hparam

theorem prop_3_2_matching : Specification.Prop32_Matching := by
  intro F _ _ n hEven
  exact ⟨(matchingAdmissible F n hEven).exchangeable, (matchingAdmissible F n hEven).cp⟩

theorem lemma_3_3_incidence : Specification.Lemma33_Incidence := by
  intro F _ _ q q' hq hq'
  exact lemma_3_3_full q q' hq hq'

theorem prop_3_4_matching_witness : Specification.Prop34_MatchingWitness := by
  intro F _ _ n k hEven hn hk2 hkk β hω hβ μ
  exact proposition_3_4 n k hEven hn hk2 hkk β hω hβ μ

theorem cor_3_5_no_sublogarithmic : Specification.Cor35_NoSublogarithmic :=
  corollary_3_5

theorem prop_4_1_response_tables : Specification.Prop41_ResponseTables := by
  intro X _ A _ _ piLaw n P hP c hCP hn
  exact proposition_4_1_dependent A piLaw n P hP c hCP hn

theorem eq10_two_point_law : Specification.Eq10_TwoPointLaw := by
  intro F _ _ n hEven hn2 i j hij
  exact ⟨Matching.matchingLawFin_pair_eq n hEven hn2 i j hij,
    fun a b => Matching.matchingLawFin_pair_mass n hEven hn2 i j hij a b⟩

theorem noniid_matching_witness : Specification.NonIID_MatchingWitness := by
  intro F _ _ n k hEven hn hk2 hkk β hω hβ μ
  exact proposition_3_4_noniid n k hEven hn hk2 hkk β hω hβ μ

theorem noniid_logarithmic : Specification.NonIID_Logarithmic := by
  intro F _ _ n k hEven hn hk2 hkk θ hθ hθhalf hparam μ
  exact matching_noniid_logarithmic_lower_bound n k hEven hn hk2 hkk θ hθ hθhalf hparam μ

theorem actual_optimal_error_zero : Specification.ActualOptimalErrorZero := by
  intro θ hθ hθhalf
  exact paperOptimalError_tendsto_zero_atTop hθ hθhalf

end Paper06.Challenge
