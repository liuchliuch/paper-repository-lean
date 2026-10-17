import Paper02.StreamingProgram
import Paper02.StreamingComplexity
import Paper02.ParameterGrowth

/-! # Proposition 3.4 in the actual bit-space turnstile model

The witness uses the concrete Rudin–Shapiro evaluator. Both online updates
and final decoding are executed by the bounded-register microprograms;
no decoder function is assigned a free workspace bound.
-/
noncomputable section
namespace Paper02.StreamingTractability

open BitSpaceModel StreamingSpace StreamingParameters ParameterGrowth WeightEval

/-- The witness in the source belongs to the real-even tractability class.
The only frequency restriction applies to the final integer vector. -/
theorem proposition_3_4 : IsTEvenPlus f := by
  refine ⟨f_nonneg, f_even, f_zero, (4096 * 65560 ^ 4 : ℝ), 8, by positivity, ?_⟩
  intro d U hd hU ε δ hε hε1 hδ hδthird
  have hδ1 : δ ≤ 1 := by linarith
  obtain ⟨q, hprime, hdq, hUq, _, hbudget, hQ⟩ := exists_parameters_prime d U hd hU
  letI : Fact q.Prime := ⟨hprime⟩
  let b := medianHalf δ
  let J := levelCount d
  let ℓ := binaryColumns d
  let K := accuracyThreshold ε
  let p := StreamingProgram.program d U b J ℓ K q
  refine ⟨q, AmplifiedDecoderMachine.V J K,
    StreamingProgram.programBits d U b J ℓ K q, inferInstance, p,
    StreamingProgram.update_refines, StreamingProgram.decode_total hdq hUq,
    StreamingProgram.fits, ?_, ?_⟩
  · have hnat := StreamingComplexity.programBits_polynomial d U b J ℓ K q
      (logarithmic_dimensions d).1 (logarithmic_dimensions d).2 hQ
    have hreal : (StreamingProgram.programBits d U b J ℓ K q : ℝ) ≤
        4096 * (parameterBudget d U ε δ : ℝ) ^ 4 := by
      exact_mod_cast hnat
    exact hreal.trans (fourth_power_bound_4096 hd hU hε hε1 hδ hδ1)
  · intro stream hv
    exact StreamingProgram.success (coordinate_fits_columns d)
      (Nat.le_pow_clog (by norm_num) d) hdq hUq
      (accuracyThreshold_ge_two hε hε1) hε hε1 hδ (accuracyThreshold_lower ε)
      hbudget.le (median_repetitions_lower δ) stream hv

end Paper02.StreamingTractability
