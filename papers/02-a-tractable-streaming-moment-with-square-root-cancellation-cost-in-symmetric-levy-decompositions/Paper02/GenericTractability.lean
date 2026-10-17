import Paper02.GenericStreamingProgram
import Paper02.StreamingComplexity
import Paper02.ParameterGrowth

/-! # Lemma A.2 in the actual bit-space streaming model

The only algorithmic hypothesis is a space-bounded evaluator of a single
weight. All support sampling, updates, sparse decoding, accumulation and
median execution are supplied by the construction proved in this project.
-/
noncomputable section
namespace Paper02.GenericTractability
open BitSpaceModel StreamingSpace StreamingParameters ParameterGrowth WeightEval

/-- The source's single-weight evaluation hypothesis. This contains no sketch,
no moment estimator and no assumption about streaming success. -/
def HasPolylogEvaluator (w : ℤ → ℕ) : Prop :=
  ∃ (C : ℝ) (a : ℕ), 0 ≤ C ∧ ∀ U : ℕ, 1 ≤ U →
    ∃ ev : GenericWeightMachine.Evaluator U w,
      (ev.bits : ℝ) ≤ C * (Real.log (2 * (U : ℝ)) + 1) ^ a

/-- The moment guarantee (1.3), without requiring the weight to be even.
This is precisely the algorithmic conclusion of Lemma A.2. -/
def MomentSketchable (w : ℤ → ℝ) : Prop :=
  ∃ (C : ℝ) (a : ℕ), 0 ≤ C ∧
    ∀ (d U : ℕ), 1 ≤ d → 1 ≤ U →
    ∀ ε δ : ℝ, 0 < ε → ε ≤ 1 → 0 < δ → δ < 1 / 3 →
    ∃ (q out bits : ℕ) (_ : Fact q.Prime) (p : Program d q out),
      UpdateRefines p ∧ DecodeTotal p ∧ Fits p bits ∧
      (bits : ℝ) ≤ C * accuracyParameters d U ε δ ^ a ∧
      ∀ stream : List (SparseRecovery.Update d),
        (∀ i, -(U : ℤ) ≤ SparseRecovery.finalVector stream i ∧
          SparseRecovery.finalVector stream i ≤ U) →
        (Sampling.FiniteLaw.uniform p.Seed).prob
          {seed | Failure p seed stream (Streaming.moment w (SparseRecovery.finalVector stream)) ε} ≤ δ

lemma generic_space_bound {d U q : ℕ} [Fact q.Prime]
    (hd : 1 ≤ d) (hU : 1 ≤ U) {ε δ : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hQ : registerBits q ≤ 8 + 2 * registerBits (d + 1) + registerBits (U + 1))
    {w : ℤ → ℕ} (ev : GenericWeightMachine.Evaluator U w)
    {C : ℝ} {a : ℕ} (hC : 0 ≤ C)
    (he : (ev.bits : ℝ) ≤ C * (Real.log (2 * (U : ℝ)) + 1) ^ a) :
    (GenericStreamingProgram.programBits ev d U (medianHalf δ) (levelCount d)
      (binaryColumns d) (accuracyThreshold ε) q : ℝ) ≤
      ((4096 * 65560 ^ 4 : ℝ) + C) * accuracyParameters d U ε δ ^ (8 + a) := by
  let L := accuracyParameters d U ε δ
  have hL : 1 ≤ L := accuracyParameters_one hd hU hε hε1 hδ hδ1
  have hnat := (GenericStreamingProgram.programBits_le_witness
    (d := d) (b := medianHalf δ) (J := levelCount d) (ℓ := binaryColumns d)
    (K := accuracyThreshold ε) (q := q) ev).trans
      (Nat.add_le_add_right
        (StreamingComplexity.programBits_polynomial d U (medianHalf δ) (levelCount d)
          (binaryColumns d) (accuracyThreshold ε) q
          (logarithmic_dimensions d).1 (logarithmic_dimensions d).2 hQ) ev.bits)
  have hbits : (GenericStreamingProgram.programBits ev d U (medianHalf δ) (levelCount d)
      (binaryColumns d) (accuracyThreshold ε) q : ℝ) ≤
      4096 * (parameterBudget d U ε δ : ℝ) ^ 4 + (ev.bits : ℝ) := by
    exact_mod_cast hnat
  have hg := fourth_power_bound_4096 hd hU hε hε1 hδ hδ1
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hUR : (1 : ℝ) ≤ U := by exact_mod_cast hU
  have hD := Real.log_nonneg (show (1 : ℝ) ≤ 2 * d by linarith)
  have hU' := Real.log_nonneg (show (1 : ℝ) ≤ 2 * U by linarith)
  have hδ' := log_inverse_nonneg hδ hδ1
  have hi : 0 ≤ ε⁻¹ := inv_nonneg.mpr hε.le
  have heL : Real.log (2 * (U : ℝ)) + 1 ≤ L := by dsimp [L, accuracyParameters]; linarith
  have hep := pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ Real.log (2 * (U : ℝ)) + 1) heL a
  have hp8 : L ^ 8 ≤ L ^ (8 + a) := pow_le_pow_right₀ hL (by omega)
  have hpa : L ^ a ≤ L ^ (8 + a) := pow_le_pow_right₀ hL (by omega)
  have hbase : (4096 * 65560 ^ 4 : ℝ) * L ^ 8 ≤ (4096 * 65560 ^ 4 : ℝ) * L ^ (8 + a) :=
    mul_le_mul_of_nonneg_left hp8 (by positivity)
  have heval : (ev.bits : ℝ) ≤ C * L ^ (8 + a) :=
    he.trans ((mul_le_mul_of_nonneg_left hep hC).trans (mul_le_mul_of_nonneg_left hpa hC))
  change _ ≤ ((4096 * 65560 ^ 4 : ℝ) + C) * L ^ (8 + a)
  change _ ≤ (4096 * 65560 ^ 4 : ℝ) * L ^ 8 at hg
  nlinarith only [hbits, hg, hbase, heval]

/-- Full Lemma A.2: a single weight evaluator yields an actual one-pass
turnstile program with a uniform polynomial bit bound, unrestricted integer
updates, final-vector-only frequency promise and failure probability ≤δ. -/
theorem lemma_A2 (w : ℤ → ℕ) (hw0 : w 0 = 0)
    (hw1 : ∀ k, k ≠ 0 → 1 ≤ w k) (hw3 : ∀ k, w k ≤ 3)
    (heval : HasPolylogEvaluator w) : MomentSketchable (fun k => (w k : ℝ)) := by
  obtain ⟨C, a, hC, he⟩ := heval
  refine ⟨(4096 * 65560 ^ 4 : ℝ) + C, 8 + a, by positivity, ?_⟩
  intro d U hd hU ε δ hε hε1 hδ hδthird
  have hδ1 : δ ≤ 1 := by linarith
  obtain ⟨ev, hev⟩ := he U hU
  obtain ⟨q, hprime, hdq, hUq, _, hbudget, hQ⟩ := exists_parameters_prime d U hd hU
  letI : Fact q.Prime := ⟨hprime⟩
  let b := medianHalf δ
  let J := levelCount d
  let ℓ := binaryColumns d
  let K := accuracyThreshold ε
  let p := GenericStreamingProgram.program d U b J ℓ K q ev
  refine ⟨q, GenericAmplifiedDecoderMachine.V J K,
    GenericStreamingProgram.programBits ev d U b J ℓ K q, inferInstance, p,
    GenericStreamingProgram.update_refines ev,
    GenericStreamingProgram.decode_total ev hdq hUq hw0 hw3,
    GenericStreamingProgram.fits ev, ?_, ?_⟩
  · exact generic_space_bound hd hU hε hε1 hδ hδ1 hQ ev hC hev
  · intro stream hv
    exact GenericStreamingProgram.success ev hw0 hw1 hw3
      (coordinate_fits_columns d) (Nat.le_pow_clog (by norm_num) d) hdq hUq
      (accuracyThreshold_ge_two hε hε1) hε hε1 hδ (accuracyThreshold_lower ε)
      hbudget.le (median_repetitions_lower δ) stream hv

end Paper02.GenericTractability
