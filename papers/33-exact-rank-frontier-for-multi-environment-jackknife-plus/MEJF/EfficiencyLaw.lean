import MEJF.Efficiency
import MEJF.FiniteExchangeable
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Independence.Basic

/-! # The atomless exchangeable law used by Proposition 7.2

Noise is indexed by block type before the independent type permutation is
sampled. Thus relabeling observed blocks changes only that permutation.
-/
namespace MEJF.EfficiencyLaw

open MeasureTheory Set
open MEJF.Efficiency MEJF.FiniteExchangeable MEJF.OrderStatistics

noncomputable section
attribute [local instance] Classical.propDecidable

abbrev Type20 := ZMod 20
abbrev Coord19 := Fin 19
abbrev NoiseArray := Type20 × Coord19 → ℝ
abbrev Block := Coord19 → (Type20 × Coord19) × ℝ
abbrev BlockArray := Type20 → Block
abbrev Sample := Equiv.Perm Type20 × NoiseArray

local instance : MeasurableSpace (Equiv.Perm Type20) := ⊤
local instance : MeasurableSingletonClass (Equiv.Perm Type20) := ⟨fun _ => trivial⟩

/-- Continuous uniform noise on the bounded interval [-ξ,ξ]. -/
def intervalNoise (ξ : ℝ) : Measure ℝ :=
  (volume (Icc (-ξ) ξ))⁻¹ • volume.restrict (Icc (-ξ) ξ)

theorem intervalNoise_probability {ξ : ℝ} (hξ : 0 < ξ) :
    IsProbabilityMeasure (intervalNoise ξ) := by
  change IsProbabilityMeasure (ProbabilityTheory.cond volume (Icc (-ξ) ξ))
  apply ProbabilityTheory.cond_isProbabilityMeasure_of_finite
  · rw [Real.volume_Icc]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (by linarith))
  · rw [Real.volume_Icc]
    exact ENNReal.ofReal_ne_top

instance intervalNoise_finite (ξ : ℝ) : IsFiniteMeasure (intervalNoise ξ) := by
  haveI : IsZeroOrProbabilityMeasure (intervalNoise ξ) := by
    change IsZeroOrProbabilityMeasure (ProbabilityTheory.cond volume (Icc (-ξ) ξ))
    infer_instance
  infer_instance

instance intervalNoise_noAtoms (ξ : ℝ) : NoAtoms (intervalNoise ξ) :=
  ⟨fun x => by simp [intervalNoise]⟩

theorem intervalNoise_bound (ξ : ℝ) : ∀ᵐ y ∂intervalNoise ξ, |y| ≤ ξ := by
  have h : ∀ᵐ y ∂volume.restrict (Icc (-ξ) ξ), y ∈ Icc (-ξ) ξ :=
    ae_restrict_mem measurableSet_Icc
  have hh := Measure.ae_smul_measure h ((volume (Icc (-ξ) ξ))⁻¹)
  exact hh.mono (fun y hy => abs_le.mpr hy)

/-- Independently sample the 380 response coordinates. -/
def noiseMeasure (ξ : ℝ) : Measure NoiseArray := Measure.pi fun _ => intervalNoise ξ

theorem noiseMeasure_probability {ξ : ℝ} (hξ : 0 < ξ) :
    IsProbabilityMeasure (noiseMeasure ξ) := by
  haveI := intervalNoise_probability hξ
  unfold noiseMeasure
  infer_instance

instance noiseMeasure_finite (ξ : ℝ) : IsFiniteMeasure (noiseMeasure ξ) := by
  unfold noiseMeasure
  infer_instance

instance noiseMeasure_noAtoms (ξ : ℝ) : NoAtoms (noiseMeasure ξ) := by
  unfold noiseMeasure
  infer_instance

theorem noiseMeasure_bound {ξ : ℝ} (hξ : 0 < ξ) :
    ∀ᵐ y ∂noiseMeasure ξ, ∀ i, |y i| ≤ ξ := by
  haveI := intervalNoise_probability hξ
  apply ae_all_iff.mpr
  intro i
  exact (measurePreserving_eval (fun _ : Type20 × Coord19 => intervalNoise ξ) i).quasiMeasurePreserving.ae
    (intervalNoise_bound ξ)

/-- The response noises are independent continuous random variables. -/
theorem noiseMeasure_independent {ξ : ℝ} (hξ : 0 < ξ) :
    ProbabilityTheory.iIndepFun (fun i (y : NoiseArray) => y i) (noiseMeasure ξ) := by
  haveI := intervalNoise_probability hξ
  exact ProbabilityTheory.iIndepFun_pi (fun _ => measurable_id.aemeasurable)

/-- The uniform type permutation and all noise coordinates are independent. -/
def sampleMeasure (ξ : ℝ) : Measure Sample := (permutationMeasure Type20).prod (noiseMeasure ξ)

theorem sampleMeasure_probability {ξ : ℝ} (hξ : 0 < ξ) :
    IsProbabilityMeasure (sampleMeasure ξ) := by
  haveI := noiseMeasure_probability hξ
  unfold sampleMeasure
  infer_instance

instance sampleMeasure_noAtoms (ξ : ℝ) : NoAtoms (sampleMeasure ξ) := by
  unfold sampleMeasure
  infer_instance

/-- Expose all noisy, covariate-labeled blocks after their uniform permutation. -/
def reveal (s : Sample) (i : Type20) (j : Coord19) : (Type20 × Coord19) × ℝ :=
  ((s.1 i, j), s.2 (s.1 i, j))

theorem reveal_measurable : Measurable reveal := by
  apply measurable_from_prod_countable_right
  intro p
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  have hE : Measurable (fun y : NoiseArray => y (p i,j)) := measurable_pi_apply _
  change Measurable (fun y : NoiseArray => (((p i,j) : Type20 × Coord19), y (p i,j)))
  exact measurable_const.prodMk hE

/-- The covariate labels and responses together recover the entire source. -/
theorem reveal_injective : Function.Injective reveal := by
  rintro ⟨p,y⟩ ⟨q,z⟩ hpq
  have hp : p = q := by
    ext i
    exact congrArg (fun a : BlockArray => ((a i 0).1).1) hpq
  subst q
  have hy : y = z := by
    funext a
    obtain ⟨u,j⟩ := a
    have h := congrArg (fun a : BlockArray => (a (p.symm u) j).2) hpq
    simpa [reveal] using h
  exact Prod.ext rfl hy

/-- Actual joint law of all twenty observed blocks. -/
def blockLaw (ξ : ℝ) : Measure BlockArray := (sampleMeasure ξ).map reveal

theorem blockLaw_probability {ξ : ℝ} (hξ : 0 < ξ) :
    IsProbabilityMeasure (blockLaw ξ) := by
  haveI := sampleMeasure_probability hξ
  exact Measure.isProbabilityMeasure_map reveal_measurable.aemeasurable

/-- Every singleton of the entire response/covariate array has probability zero. -/
instance blockLaw_noAtoms (ξ : ℝ) : NoAtoms (blockLaw ξ) := by
  constructor
  intro a
  rw [blockLaw, Measure.map_apply reveal_measurable (measurableSet_singleton a)]
  apply Set.Subsingleton.measure_zero
  intro s hs t ht
  apply reveal_injective
  exact hs.trans ht.symm

/-- Relabeling block positions corresponds to the finite source permutation
bijection, without touching the independently generated type-indexed noise. -/
theorem blockLaw_exchangeable (ξ : ℝ) : Exchangeability.Exchangeable (blockLaw ξ) := by
  intro e
  have hsource : MeasurePreserving (Prod.map (rightRelabel e) id)
      (sampleMeasure ξ) (sampleMeasure ξ) :=
    (rightRelabel_measurePreserving e).prod (MeasurePreserving.id (noiseMeasure ξ))
  have hrelabel : Measurable (Exchangeability.relabel (B := Block) e) := by
    apply measurable_pi_lambda
    intro i
    exact measurable_pi_apply (e.symm i)
  refine ⟨hrelabel, ?_⟩
  change Measure.map (Exchangeability.relabel e) (Measure.map reveal (sampleMeasure ξ)) =
    Measure.map reveal (sampleMeasure ξ)
  rw [Measure.map_map hrelabel reveal_measurable]
  have heq : Exchangeability.relabel e ∘ reveal = reveal ∘ Prod.map (rightRelabel e) id := rfl
  rw [heq, ← Measure.map_map reveal_measurable hsource.measurable, hsource.map_eq]

/-- The support event is stated on the actual independent source. -/
theorem sampleMeasure_bound {ξ : ℝ} (hξ : 0 < ξ) :
    ∀ᵐ s ∂sampleMeasure ξ, ∀ i, |s.2 i| ≤ ξ := by
  exact (measurePreserving_snd (μ := permutationMeasure Type20) (ν := noiseMeasure ξ)).quasiMeasurePreserving.ae
    (noiseMeasure_bound hξ)

/-- Almost every noisy block array obeys the original per-response support bound. -/
theorem blockLaw_response_bound {ξ : ℝ} (hξ : 0 < ξ) :
    ∀ᵐ a ∂blockLaw ξ, ∀ i j, |(a i j).2| ≤ ξ := by
  have hnoise := noiseMeasure_bound hξ
  have hsource : ∀ᵐ s ∂sampleMeasure ξ, ∀ i, |s.2 i| ≤ ξ := by
    exact (measurePreserving_snd (μ := permutationMeasure Type20) (ν := noiseMeasure ξ)).quasiMeasurePreserving.ae hnoise
  have hp : MeasurableSet {a : BlockArray | ∀ i j, |(a i j).2| ≤ ξ} := by
    simp only [setOf_forall]
    apply MeasurableSet.iInter
    intro i
    apply MeasurableSet.iInter
    intro j
    have hr : Measurable (fun a : BlockArray => (a i j).2) :=
      ((measurable_pi_apply j).comp (measurable_pi_apply i)).snd
    have hset : {a : BlockArray | |(a i j).2| ≤ ξ} =
        (fun a : BlockArray => (a i j).2) ⁻¹' Icc (-ξ) ξ := by
      ext a
      change |(a i j).2| ≤ ξ ↔ -ξ ≤ (a i j).2 ∧ (a i j).2 ≤ ξ
      exact abs_le
    rw [hset]
    exact hr measurableSet_Icc
  rw [blockLaw, ae_map_iff reveal_measurable.aemeasurable hp]
  exact hsource.mono (fun s hs i j => hs (s.1 i,j))

/-- Full pairwise prediction table at all nineteen coordinates. -/
def cyclicTable (K : ℝ) (u v : Type20) (j : Coord19) : ℝ :=
  if j = 0 then cyclicPrediction20 K u v else 1

/-- The inner residual quantile from the actual source responses, with the
paper's symmetric omitted-pair prediction table. -/
def cyclicScores (K : ℝ) (s : Sample) (u : Type20) (k : Fin 19) (i : Fin 19) : ℝ :=
  stat (fun j => |s.2 (otherType20 u i,j)-cyclicTable K (otherType20 u i) u j|) k

/-- Endpoint-rule lengths computed from the two actual cyclic quantile levels. -/
def cyclicEndpointLength (K : ℝ) (s : Sample) (u : Type20) (j : Coord19) : ℝ :=
  endpointLength (fun i => cyclicTable K u (otherType20 u i) j)
    (cyclicScores K s u ⟨17, by omega⟩) ⟨1, by omega⟩

/-- Minmax lengths computed from the actual cyclic score quantiles. -/
def cyclicMinmaxLength (K : ℝ) (s : Sample) (u : Type20) (j : Coord19) : ℝ :=
  minmaxLength (fun i => cyclicTable K u (otherType20 u i) j)
    (cyclicScores K s u ⟨15, by omega⟩) ⟨15, by omega⟩

lemma cyclicPredictionTuple (K : ℝ) (u : Type20) (j : Coord19) :
    (fun i => cyclicTable K u (otherType20 u i) j) = coordinatePredictions19 K j := by
  funext i
  simp only [cyclicTable, coordinatePredictions19, cyclicPrediction20_row]

lemma cyclicScores_responseScores (K : ℝ) (s : Sample) (u : Type20) (k : Fin 19) :
    cyclicScores K s u k = responseScores19 (fun i => cyclicPrediction20 K (otherType20 u i) u)
      (fun i j => s.2 (otherType20 u i,j)) k := by
  rfl

/-- The exact noiseless formulas hold for every realized type permutation and
every hypothetical test type, using the actual cyclic residual table. -/
theorem cyclic_zero_lengths {K : ℝ} (hK : 0 < K) (p : Equiv.Perm Type20) (u : Type20) :
    average19 (cyclicEndpointLength K (p, fun _ => 0) u) = 2 ∧
    average19 (cyclicMinmaxLength K (p, fun _ => 0) u) = (2*K+38)/19 ∧
    average19 (fun j => cyclicMinmaxLength K (p, fun _ => 0) u j -
      cyclicEndpointLength K (p, fun _ => 0) u j) = 2*K/19 ∧
    average19 (cyclicEndpointLength K (p, fun _ => 0) u) /
      average19 (cyclicMinmaxLength K (p, fun _ => 0) u) = 38/(2*K+38) := by
  let z := fun i => cyclicPrediction20 K (otherType20 u i) u
  have hs (k : Fin 19) : cyclicScores K (p, fun _ => 0) u k = scores19 z k := by
    rw [cyclicScores_responseScores]
    exact responseScores19_zero z k
  have hep : cyclicEndpointLength K (p, fun _ => 0) u = fun j =>
      endpointLength (coordinatePredictions19 K j) (scores19 z ⟨17, by omega⟩) ⟨1, by omega⟩ := by
    funext j
    rw [cyclicEndpointLength, cyclicPredictionTuple, hs]
  have hmm : cyclicMinmaxLength K (p, fun _ => 0) u = fun j =>
      minmaxLength (coordinatePredictions19 K j) (scores19 z ⟨15, by omega⟩) ⟨15, by omega⟩ := by
    funext j
    rw [cyclicMinmaxLength, cyclicPredictionTuple, hs]
  rw [hep, hmm]
  exact finite_construction19 hK z ⟨15, by omega⟩

/-- Zero responses together with a uniform type permutation give the noiseless
exchangeable block model in the first half of Proposition 7.2. -/
def zeroBlockLaw : Measure BlockArray :=
  (permutationMeasure Type20).map (fun p => reveal (p, fun _ => 0))

instance zeroBlockLaw_probability : IsProbabilityMeasure zeroBlockLaw :=
  Measure.isProbabilityMeasure_map (measurable_of_finite _).aemeasurable

theorem zeroBlockLaw_exchangeable : Exchangeability.Exchangeable zeroBlockLaw := by
  intro e
  have hread : Measurable (fun p : Equiv.Perm Type20 => reveal (p, fun _ => 0)) :=
    measurable_of_finite _
  have hrelabel : Measurable (Exchangeability.relabel (B := Block) e) := by
    apply measurable_pi_lambda
    intro i
    exact measurable_pi_apply (e.symm i)
  refine ⟨hrelabel, ?_⟩
  change Measure.map (Exchangeability.relabel e)
    (Measure.map (fun p => reveal (p, fun _ => 0)) (permutationMeasure Type20)) =
    Measure.map (fun p => reveal (p, fun _ => 0)) (permutationMeasure Type20)
  rw [Measure.map_map hrelabel hread]
  have heq : Exchangeability.relabel e ∘ (fun p => reveal (p, fun _ => 0)) =
      (fun p => reveal (p, fun _ => 0)) ∘ rightRelabel e := rfl
  rw [heq, ← Measure.map_map hread (measurable_of_finite _),
    (rightRelabel_measurePreserving e).map_eq]

/-- The deterministic bounded-noise claim from the actual cyclic table and
actual source responses. No premise postulates a score or endpoint bound. -/
theorem cyclic_pathwise_bounds {K ξ : ℝ} (hK : 0 < K) (hξ : 0 ≤ ξ)
    (hsmall : ξ < K/38) (s : Sample) (hs : ∀ i, |s.2 i| ≤ ξ) (u : Type20) :
    (2*K-76*ξ)/19 ≤ average19 (fun j => cyclicMinmaxLength K s u j-cyclicEndpointLength K s u j) ∧
    0 < (2*K-76*ξ)/19 ∧ average19 (cyclicEndpointLength K s u) ≤ 2+2*ξ ∧
    (2*K+38-38*ξ)/19 ≤ average19 (cyclicMinmaxLength K s u) ∧
    average19 (cyclicEndpointLength K s u) / average19 (cyclicMinmaxLength K s u) ≤
      38*(1+ξ)/(2*K+38-38*ξ) := by
  have hep : cyclicEndpointLength K s u = fun j =>
      endpointLength (coordinatePredictions19 K j)
        (responseScores19 (fun i => cyclicPrediction20 K (otherType20 u i) u)
          (fun i j => s.2 (otherType20 u i,j)) ⟨17, by omega⟩) ⟨1, by omega⟩ := by
    funext j
    rw [cyclicEndpointLength, cyclicPredictionTuple, cyclicScores_responseScores]
  have hmm : cyclicMinmaxLength K s u = fun j =>
      minmaxLength (coordinatePredictions19 K j)
        (responseScores19 (fun i => cyclicPrediction20 K (otherType20 u i) u)
          (fun i j => s.2 (otherType20 u i,j)) ⟨15, by omega⟩) ⟨15, by omega⟩ := by
    funext j
    rw [cyclicMinmaxLength, cyclicPredictionTuple, cyclicScores_responseScores]
  rw [hep, hmm]
  exact finite_noisy_construction19 hK hξ hsmall
    (fun i => cyclicPrediction20 K (otherType20 u i) u)
    (fun i j => s.2 (otherType20 u i,j)) (fun i j => hs _) ⟨15, by omega⟩

/-- One actual atomless exchangeable block model with the required pathwise
length separation on every source realization in its bounded support event. -/
theorem atomless_exchangeable_cyclic_model {K ξ : ℝ} (hK : 0 < K) (hξ : 0 < ξ)
    (hsmall : ξ < K/38) :
    IsProbabilityMeasure (blockLaw ξ) ∧ NoAtoms (blockLaw ξ) ∧
    Exchangeability.Exchangeable (blockLaw ξ) ∧
    ∀ᵐ s ∂sampleMeasure ξ, ∀ u,
      (2*K-76*ξ)/19 ≤ average19 (fun j => cyclicMinmaxLength K s u j-cyclicEndpointLength K s u j) ∧
      0 < (2*K-76*ξ)/19 ∧ average19 (cyclicEndpointLength K s u) ≤ 2+2*ξ ∧
      (2*K+38-38*ξ)/19 ≤ average19 (cyclicMinmaxLength K s u) ∧
      average19 (cyclicEndpointLength K s u) / average19 (cyclicMinmaxLength K s u) ≤
        38*(1+ξ)/(2*K+38-38*ξ) := by
  refine ⟨blockLaw_probability hξ, inferInstance, blockLaw_exchangeable ξ, ?_⟩
  exact (sampleMeasure_bound hξ).mono (fun s hs u =>
    cyclic_pathwise_bounds hK (le_of_lt hξ) hsmall s hs u)

end
end MEJF.EfficiencyLaw
