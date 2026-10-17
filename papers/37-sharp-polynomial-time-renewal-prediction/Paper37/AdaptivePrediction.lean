import Paper37.GenericCompressionPrediction
import Paper37.AdaptiveRisk

/-! The actual occupied-type mixture predictor of Appendix E, with its exact
suffix average and stationary ENNReal risk. -/
namespace Paper37.AdaptivePrediction

open Finset Renewal Prediction Adaptive AdaptiveRisk AnalyticBounds RenewalOccupancy
open Compression Compression.Distribution RenewalCompression

/-- The source Qad family, with the harmless normalized empty-block version. -/
noncomputable def assignment : GenericCompressionPrediction.Assignment where
  mass := adaptiveMass
  positive := adaptiveMass_pos
  normalized := adaptiveMass_sum

/-- At every positive horizon the generic query is exactly the source adaptive query. -/
theorem prefix_eq (N : ℕ) (hN : 1 ≤ N) (z : List Bool) :
    GenericCompressionPrediction.prefixMass assignment N z = adaptivePrefix N z := by
  unfold GenericCompressionPrediction.prefixMass adaptivePrefix
  apply sum_congr rfl
  intro v hv
  change adaptiveMass (z ++ v) = adaptiveBlock (z ++ v)
  apply adaptiveMass_eq
  have hlen := (mem_words (N-z.length) v).mp (List.mem_toFinset.mp hv)
  rw [List.length_append, hlen]
  omega

theorem conditional_eq (N : ℕ) (hN : 1 ≤ N) (z : List Bool) :
    GenericCompressionPrediction.blockConditional assignment N z = adaptiveConditional N z := by
  unfold GenericCompressionPrediction.blockConditional adaptiveConditional
  rw [prefix_eq N hN, prefix_eq N hN]

/-- Exact implementation identity for equation E.11. -/
theorem predict_eq (n : ℕ) (x : List Bool) :
    GenericCompressionPrediction.predict assignment n x = adaptivePredict n x := by
  unfold GenericCompressionPrediction.predict adaptivePredict
  simp_rw [conditional_eq (n+1) (by omega)]

theorem adaptivePredict_interior (n : ℕ) (hn : 0 < n) (x : List Bool) (hx : x.length = n) :
    0 < (adaptivePredict n x : ℝ) ∧ (adaptivePredict n x : ℝ) < 1 := by
  rw [← predict_eq]
  exact GenericCompressionPrediction.predict_interior assignment n hn x hx

/-- The implemented adaptive Dirac prediction kernel, on the source risk domain. -/
noncomputable def sourcePredictor (n : ℕ) (hn : 0 < n) : RandomizedPredictor :=
  GenericCompressionPrediction.sourcePredictor assignment n hn

/-- The risk's prediction measure is concentrated at the source's E.11 parameter. -/
theorem sourcePredictor_on_history (n : ℕ) (hn : 0 < n) (x : List Bool) (hx : x.length = n) :
    (sourcePredictor n hn x).toMeasure = MeasureTheory.Measure.dirac
      ⟨(adaptivePredict n x : ℝ),
        ⟨(adaptivePredict_interior n hn x hx).1.le, (adaptivePredict_interior n hn x hx).2.le⟩⟩ := by
  unfold sourcePredictor GenericCompressionPrediction.sourcePredictor
  simp only [hx, ↓reduceDIte, MeasureTheory.ProbabilityMeasure.toMeasure]
  congr 1
  apply Subtype.ext
  change (GenericCompressionPrediction.predict assignment n x : ℝ) = (adaptivePredict n x : ℝ)
  exact_mod_cast predict_eq n x

/-- Theorem E.4's adaptive risk oracle, for the actual finite-mean renewal law,
actual source mixture and actual stationary-history KL risk. -/
theorem adaptive_risk_oracle (μ : Law) (n : ℕ) (hn : 0 < n) :
    risk n (sourcePredictor n hn) μ ≤ ENNReal.ofReal
      ((Real.log 2 + min (redundancyBound (n+1))
        ((2*occupiedComplexity (n+1) (fun d => μ.mass (d-1)) (mean μ)+6) *
          Real.log (n+2 : ℝ)) + Real.log (n+2 : ℝ)) / n) := by
  apply GenericCompressionPrediction.source_risk_le_of_block_regret assignment μ n hn
  have h := expected_adaptive_regret_le μ (N := n+1) (by omega)
  have heq : (∑ x ∈ (words (n+1)).toFinset, blockMass μ x *
      Real.log (blockMass μ x / (assignment.mass x : ℝ))) =
      ∑ x ∈ (words (n+1)).toFinset, blockMass μ x *
        Real.log (blockMass μ x / (adaptiveBlock x : ℝ)) := by
    apply sum_congr rfl
    intro x hx
    have hlen := (mem_words (n+1) x).mp (List.mem_toFinset.mp hx)
    change blockMass μ x * Real.log (blockMass μ x / (adaptiveMass x : ℝ)) = _
    rw [adaptiveMass_eq x (by rw [hlen]; omega)]
  rw [heq]
  simpa only [Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using h

end Paper37.AdaptivePrediction
