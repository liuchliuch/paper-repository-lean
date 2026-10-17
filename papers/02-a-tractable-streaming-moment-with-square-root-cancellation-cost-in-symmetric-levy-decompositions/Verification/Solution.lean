import Verification.Statements
import Paper02
import Paper02.Basic
import Paper02.RudinShapiro
import Paper02.LSym
import Paper02.Bounds
import Paper02.Main
import Paper02.Bernstein

/-!
# Solution side of the official Comparator

Imports the real `Paper02` proofs. No placeholders.
-/

namespace Verification.Certificate

open Paper02 Paper02.RS Paper02.LSym Paper02.Bounds Paper02.Main Paper02.Bernstein

theorem thm11_f_props : Verification.Specification.Theorem11_f_props :=
  Paper02.Main.f_is_even_bounded

theorem lem24_transitions : Verification.Specification.Lemma24_transitions :=
  fun m => Paper02.RS.T_add_U m

theorem lem21_gaussian : Verification.Specification.Lemma21_gaussian :=
  fun A k => Paper02.secondDiff_gaussian A k

theorem lem21_cos : Verification.Specification.Lemma21_cos :=
  fun s k => Paper02.secondDiff_cos s k

theorem cor22_gaussian : Verification.Specification.Cor22_gaussian := by
  intro ι _ a k A hA M hM
  exact Paper02.LSym.dual_gaussian a k A hA M hM

theorem cor22_atomic : Verification.Specification.Cor22_atomic := by
  intro ι J _ _ a k c s hc M hM
  exact Paper02.LSym.dual_atomic a k c hc s M hM

theorem prop31_algebra : Verification.Specification.Prop31_algebra :=
  fun N η ρ s1 hN hη hpair hs1 =>
    Paper02.Bounds.prop_3_1_algebra N η ρ s1 hN hη hpair hs1

theorem prop33_bound : Verification.Specification.Prop33_bound :=
  fun p c hp h => Paper02.Bounds.prop_3_3_bound p c hp h

theorem propB2_ratio : Verification.Specification.PropB2_ratio :=
  fun α k hk hα => Paper02.Bernstein.prop_B2_ratio α k hk hα

theorem propB2_envelope : Verification.Specification.PropB2_envelope :=
  fun α k hk hα => Paper02.Bernstein.prop_B2_envelope α k hk hα

theorem secondDiff_error : Verification.Specification.SecondDiff_error :=
  fun e k η h1 h2 h3 => Paper02.Bounds.secondDiff_error_le e k η h1 h2 h3

theorem lem21_full : Verification.Specification.Lemma21_full :=
  fun _ hg => Paper02.LSym.positive_second_difference_measure hg

theorem cor22_full : Verification.Specification.Cor22_full := by
  intro ι _ gp gn hp hn a k
  exact Paper02.LSym.dual_general_norm hp hn a k

theorem remark23_full : Verification.Specification.Remark23_full :=
  ⟨Paper02.LSym.normalizedGenerator_continuous,
    fun _ c k => Paper02.LSym.normalizedGenerator_representation c k,
    fun _ hg h => Paper02.LSym.normalized_probability_mixture hg h,
    fun _ c h => Paper02.LSym.cert_zero_mass_concentration c h,
    fun _ hg h k => Paper02.LSym.integer_zero_of_one_zero hg h k⟩

theorem lem24_full : Verification.Specification.Lemma24_full := by
  intro m t
  exact ⟨Paper02.RS.classical_energy_exp m t,
    Paper02.RS.classical_bound m _ (Complex.norm_exp_ofReal_mul_I t),
    Paper02.RS.T_add_U m, Paper02.RS.T_closed m⟩

theorem lem25_full : Verification.Specification.Lemma25_full :=
  Paper02.RS.exact_pairing

theorem prop31_full : Verification.Specification.Prop31_full :=
  Paper02.LowerBound.prop_3_1

theorem cor32_full : Verification.Specification.Cor32_full :=
  Paper02.Cutoff.cor_3_2

theorem prop33_full : Verification.Specification.Prop33_full :=
  Paper02.Fourier.prop_3_3

theorem thm11_bounds : Verification.Specification.Theorem11_bounds :=
  Paper02.Main.theorem_1_1_bounds

theorem thm11_theta : Verification.Specification.Theorem11_theta :=
  Paper02.Main.theorem_1_1_theta

theorem no_polynomial_control : Verification.Specification.No_polynomial_control :=
  Paper02.Cutoff.controlled_decomposition_conjecture_false_bivariate

theorem lemB1_full : Verification.Specification.LemmaB1_full :=
  fun _ _ _ ha ha' hb hb' hc habc => Paper02.Bernstein.lemma_B1 ha ha' hb hb' hc habc

theorem B5_full : Verification.Specification.B5_full :=
  fun y hy => ⟨Paper02.Bernstein.eq_B5_lower y hy, Paper02.Bernstein.eq_B5_upper y hy⟩

theorem propB2_estimates : Verification.Specification.PropB2_estimates := by
  intro n hn ε hε _
  exact Paper02.Bernstein.prop_B2_admissibleSplit hn hε

theorem propB3_estimates : Verification.Specification.PropB3_estimates := by
  intro p β hp _ hβ hβ' m hm n hn ε hε hε'
  exact ⟨Paper02.Bernstein.prop_B3_admissibleSplit hp hβ hm hn hε hε',
    Paper02.Bernstein.prop_B3_cost_bound hp hβ hβ' hm hn hε hε'⟩

theorem witness_evaluator : Verification.Specification.Witness_evaluator :=
  Paper02.WeightEval.weight_cast

theorem thm11_ennreal_bounds : Verification.Specification.Theorem11_ennreal_bounds :=
  Paper02.Cutoff.theorem_1_1_ennreal_bounds

theorem gaussian_mixture : Verification.Specification.Gaussian_mixture :=
  Paper02.Bernstein.isLSym_gaussian_mixture

theorem bernstein_representation_subordination :
    Verification.Specification.Bernstein_representation_subordination :=
  fun _ h => Paper02.Bernstein.isLSym_comp_square_of_representation h

theorem lemA1_correctness : Verification.Specification.LemmaA1_correctness := by
  intro d q U K _ hdq hUq v hv
  constructor
  · intro z hs
    rw [Paper02.SparseRecovery.decodeHankelSummary_eq_decodeSummary hdq hUq]
    exact Paper02.SparseRecovery.decodeSummary_sparse hdq hUq v hv hs z
  · intro hdense
    simp_rw [Paper02.SparseRecovery.decodeHankelSummary_eq_decodeSummary hdq hUq]
    exact Paper02.SparseRecovery.decodeSummary_dense_probability_le hUq v hv hdense

theorem lemA1_summary_bits : Verification.Specification.LemmaA1_summary_bits :=
  Paper02.StreamingSpace.summary_fits

theorem witness_stream_probability : Verification.Specification.Witness_stream_probability :=
  Paper02.Streaming.witness_stream_estimate

theorem lemA1_operational : Verification.Specification.LemmaA1_operational := by
  intro d q U K _ hK hdq hUq
  refine ⟨Paper02.SparseRecoverySpace.summary_and_decoder_quadratic hK hdq hUq, ?_⟩
  intro z summary
  obtain ⟨out, hr, he, _⟩ := Paper02.RecoveryMachine.machine_correct hdq hUq z summary
  refine ⟨out, hr, ?_⟩
  rw [Paper02.SparseRecovery.decodeHankelSummary_eq_decodeSummary hdq hUq]
  exact he

theorem prop34_full : Verification.Specification.Prop34_full :=
  Paper02.StreamingTractability.proposition_3_4

theorem lemA2_full : Verification.Specification.LemmaA2_full :=
  Paper02.GenericTractability.lemma_A2

theorem thm11_full : Verification.Specification.Theorem11_full :=
  Paper02.Main.theorem_1_1

end Verification.Certificate
