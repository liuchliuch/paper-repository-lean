import MEJF.MainExact
import MEJF.StabilityProbability

/-! # Stability alone does not improve the unexpanded rule (Remark 6.6)

Positive scaling is performed on the actual prescribed prediction table. The
same additive learner has zero leave-one reference fits on the type orbit,
while its actual leave-two fits are bounded by the required stability tolerance.
-/
namespace MEJF.Scaling

open Finset MeasureTheory MEJF.Setup MEJF.PredictionTable MEJF.Stability MEJF.Exchangeability
noncomputable section
attribute [local instance] Classical.propDecidable

variable {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X] {m n : ℕ}

lemma learner_leaveOne (p : Fin (m+1) → Fin (m+1) → Fin n → ℝ) (hn : 0 < n)
    (u : Fin (m+1)) (j : Fin n) :
    learner p ((univ.erase u).val.map typeBlock) u j = 0 := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  unfold learner
  simp only [Multiset.map_map, Function.comp_apply, contribution_typeBlock]
  have hsum : (∑ v ∈ (univ : Finset (Fin (m+1))).erase u,
      if v = u then (0 : ℝ) else p u v j) = tableConstant p u j := by
    apply sum_congr rfl
    intro v hv
    simp only [(mem_erase.mp hv).1, ↓reduceIte]
  change tableConstant p u j - (∑ v ∈ (univ : Finset (Fin (m+1))).erase u,
      if v = u then (0 : ℝ) else p u v j) = 0
  rw [hsum]
  ring

/-- The full additive formula has the zero leave-one reference claimed in §6.6. -/
theorem model_reference_zero (p : Fin (m+1) → Fin (m+1) → Fin n → ℝ)
    (emb : Fin (m+1) × Fin n → X) (hinj : Function.Injective emb) (hn : 0 < n)
    (u : Fin (m+1)) (j : Fin n) :
    referencePrediction (tableLearner p emb) (modelData emb) u (emb (u,j)) = 0 := by
  have htrain : ((univ.erase u).val.map (modelData emb)) =
      ((univ.erase u).val.map typeBlock).map (embedBlock emb) := by
    simp only [Multiset.map_map, Function.comp_apply]
    rfl
  change ambientLearner p emb _ (emb (u,j)) = _
  rw [htrain, ambientLearner_at p emb hinj, ambientAt_embedMultiset p emb hinj]
  exact learner_leaveOne p hn u j

/-- Actual sorted radii commute with nonnegative table scaling on zero responses. -/
theorem model_radius_scale (p : Fin (m+1) → Fin (m+1) → Fin n → ℝ)
    (emb : Fin (m+1) × Fin n → X) (hinj : Function.Injective emb)
    (c : ℝ) (hc : 0 ≤ c) (t : ℕ) (ht : 1 ≤ t ∧ t ≤ n)
    (u v : Fin (m+1)) (huv : u ≠ v) :
    radius (tableLearner (fun u v j => c*p u v j) emb) (modelData emb) u v t ht =
      c * radius (tableLearner p emb) (modelData emb) u v t ht := by
  rw [model_radius _ emb hinj (by omega) u v huv t ht,
    model_radius p emb hinj (by omega) u v huv t ht]
  simp_rw [abs_mul, abs_of_nonneg hc]
  exact OrderStatistics.stat_map_monotone (fun j => |p u v j|) (fun x => c*x)
    (fun _ _ h => mul_le_mul_of_nonneg_left h hc) _

/-- Positive scaling acts on both genuine endpoint order-statistic stages. -/
theorem model_lowerEndpoint_scale (p : Fin (m+1) → Fin (m+1) → Fin n → ℝ)
    (emb : Fin (m+1) × Fin n → X) (hinj : Function.Injective emb)
    (c : ℝ) (hc : 0 ≤ c) (t ell : ℕ) (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m)
    (u : Fin (m+1)) (j : Fin n) :
    lowerEndpoint (tableLearner (fun u v j => c*p u v j) emb) (modelData emb) u j t ell ht he =
      c * lowerEndpoint (tableLearner p emb) (modelData emb) u j t ell ht he := by
  unfold lowerEndpoint
  have heq : (fun k : Fin m =>
      pairPrediction (tableLearner (fun u v j => c*p u v j) emb) (modelData emb) u (u.succAbove k) (modelData emb u j).1 -
      radius (tableLearner (fun u v j => c*p u v j) emb) (modelData emb) (u.succAbove k) u t ht) =
      fun k : Fin m => c * (pairPrediction (tableLearner p emb) (modelData emb) u (u.succAbove k) (modelData emb u j).1 -
      radius (tableLearner p emb) (modelData emb) (u.succAbove k) u t ht) := by
    funext k
    rw [model_radius_scale p emb hinj c hc t ht _ _ (u.succAbove_ne k)]
    change pairPrediction _ _ _ _ (emb (u,j)) - _ = c*(pairPrediction _ _ _ _ (emb (u,j)) - _)
    rw [model_pairPrediction _ emb hinj (by omega) _ _ (u.ne_succAbove k) j,
      model_pairPrediction p emb hinj (by omega) _ _ (u.ne_succAbove k) j]
    ring
  rw [heq]
  exact OrderStatistics.stat_map_monotone _ (fun x => c*x)
    (fun _ _ h => mul_le_mul_of_nonneg_left h hc) _

theorem model_upperEndpoint_scale (p : Fin (m+1) → Fin (m+1) → Fin n → ℝ)
    (emb : Fin (m+1) × Fin n → X) (hinj : Function.Injective emb)
    (c : ℝ) (hc : 0 ≤ c) (t ell : ℕ) (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m)
    (u : Fin (m+1)) (j : Fin n) :
    upperEndpoint (tableLearner (fun u v j => c*p u v j) emb) (modelData emb) u j t ell ht he =
      c * upperEndpoint (tableLearner p emb) (modelData emb) u j t ell ht he := by
  unfold upperEndpoint
  have heq : (fun k : Fin m =>
      pairPrediction (tableLearner (fun u v j => c*p u v j) emb) (modelData emb) u (u.succAbove k) (modelData emb u j).1 +
      radius (tableLearner (fun u v j => c*p u v j) emb) (modelData emb) (u.succAbove k) u t ht) =
      fun k : Fin m => c * (pairPrediction (tableLearner p emb) (modelData emb) u (u.succAbove k) (modelData emb u j).1 +
      radius (tableLearner p emb) (modelData emb) (u.succAbove k) u t ht) := by
    funext k
    rw [model_radius_scale p emb hinj c hc t ht _ _ (u.succAbove_ne k)]
    change pairPrediction _ _ _ _ (emb (u,j)) + _ = c*(pairPrediction _ _ _ _ (emb (u,j)) + _)
    rw [model_pairPrediction _ emb hinj (by omega) _ _ (u.ne_succAbove k) j,
      model_pairPrediction p emb hinj (by omega) _ _ (u.ne_succAbove k) j]
    ring
  rw [heq]
  exact OrderStatistics.stat_map_monotone _ (fun x => c*x)
    (fun _ _ h => mul_le_mul_of_nonneg_left h hc) _

/-- Positive scaling preserves every coordinate coverage decision of the actual rule. -/
theorem model_covered_scale_iff (p : Fin (m+1) → Fin (m+1) → Fin n → ℝ)
    (emb : Fin (m+1) × Fin n → X) (hinj : Function.Injective emb)
    (c : ℝ) (hc : 0 < c) (t ell : ℕ) (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m)
    (u : Fin (m+1)) (j : Fin n) :
    covered (tableLearner (fun u v j => c*p u v j) emb) (modelData emb) u j t ell ht he ↔
      covered (tableLearner p emb) (modelData emb) u j t ell ht he := by
  unfold covered
  rw [model_lowerEndpoint_scale p emb hinj c hc.le, model_upperEndpoint_scale p emb hinj c hc.le]
  change (c * _ ≤ 0 ∧ 0 ≤ c * _) ↔ (_ ≤ 0 ∧ 0 ≤ _)
  constructor
  · intro h
    constructor
    · exact (mul_le_mul_left hc).mp (by simpa only [mul_zero] using h.1)
    · exact (mul_le_mul_left hc).mp (by simpa only [mul_zero] using h.2)
  · intro h
    constructor
    · simpa only [mul_zero] using (mul_le_mul_left hc).mpr h.1
    · simpa only [mul_zero] using (mul_le_mul_left hc).mpr h.2

/-- Hence every actual unexpanded block-failure indicator is preserved. -/
theorem model_failure_scale_iff (p : Fin (m+1) → Fin (m+1) → Fin n → ℝ)
    (emb : Fin (m+1) × Fin n → X) (hinj : Function.Injective emb)
    (c : ℝ) (hc : 0 < c) (F t ell : ℕ) (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m)
    (u : Fin (m+1)) :
    Setup.failure (tableLearner (fun u v j => c*p u v j) emb) (modelData emb) u F t ell ht he ↔
      Setup.failure (tableLearner p emb) (modelData emb) u F t ell ht he := by
  simp only [Setup.failure, model_covered_scale_iff p emb hinj c hc]

/-- The scaled actual learner satisfies simultaneous on-sample deletion stability. -/
theorem incidence_scaled_stable (R : Fin (m+1) → Fin (m+1) → Prop) [DecidableRel R]
    (B : Fin (m+1) → Fin n → Fin (m+1) → Bool)
    (emb : Fin (m+1) × Fin n → X) (hinj : Function.Injective emb) (hn : 0 < n)
    (c eps : ℝ) (hc : 0 ≤ c) (hce : 3*c ≤ eps) :
    onSampleDeletionStable (tableLearner (fun u v j => c*incidenceTable R B u v j) emb)
      (modelData emb) eps := by
  intro u v huv j
  change |pairPrediction _ _ u v (emb (u,j)) - referencePrediction _ _ u (emb (u,j))| ≤ eps
  rw [model_pairPrediction _ emb hinj hn u v huv j, model_reference_zero _ emb hinj hn u j, sub_zero]
  have hp : 0 ≤ incidenceTable R B u v j := (incidenceTable_ge_one R B u v j).trans' (by norm_num)
  have hle : incidenceTable R B u v j ≤ 3 := by
    rcases incidenceTable_values R B u v j with h | h | h <;> norm_num [h]
  rw [abs_of_nonneg (mul_nonneg hc hp)]
  calc
    c*incidenceTable R B u v j ≤ c*3 := mul_le_mul_of_nonneg_left hle hc
    _ = 3*c := by ring
    _ ≤ eps := hce

local instance : MeasurableSpace (Equiv.Perm (Fin (m+1))) := ⊤
local instance : MeasurableSingletonClass (Equiv.Perm (Fin (m+1))) := ⟨fun _ => trivial⟩

lemma invariant_ae_permutationLaw (P : (Fin (m+1) → Block X n) → Prop)
    (Z : Fin (m+1) → Block X n) (hZ : P Z)
    (hinv : ∀ e : Equiv.Perm (Fin (m+1)), P (relabel e Z)) :
    ∀ᵐ W ∂FiniteExchangeable.blockPermutationLaw Z, P W := by
  let f : Equiv.Perm (Fin (m+1)) → (Fin (m+1) → Block X n) := fun p => Z ∘ p
  have hμ : FiniteExchangeable.blockPermutationLaw Z =
      (FiniteExchangeable.permutationMeasure (Fin (m+1))).map f := by
    unfold FiniteExchangeable.blockPermutationLaw FiniteExchangeable.uniformPermutationLaw
    rw [Measure.map_map (measurable_of_finite _) (measurable_of_finite _)]
    rfl
  rw [hμ]
  have hrange := ae_map_mem_range f (Set.finite_range f).measurableSet
    (FiniteExchangeable.permutationMeasure (Fin (m+1)))
  filter_upwards [hrange] with W hW
  obtain ⟨p, rfl⟩ := hW
  exact hinv p.symm

/-- For every positive tolerance, an actual exchangeable stable experiment
retains the general worst-case failure probability of the unexpanded rule. -/
theorem exists_stable_unexpanded_attaining_model (m n F t ell : ℕ) (eps : ℝ) (heps : 0 < eps)
    (hm : 1 ≤ m) (hF : 1 ≤ F) (hFn : F ≤ n) (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m) :
    ∃ (A : Learner UniversalCovariate n) (Z : Fin (m+1) → Block UniversalCovariate n),
      (FiniteExchangeable.blockPermutationLaw Z).real {W | onSampleDeletionStable A W eps} = 1 ∧
      (FiniteExchangeable.blockPermutationLaw Z).real
        {W | Setup.failure A W (Fin.last m) F t ell ht he} = RankFrontier.failureRate m F t ell := by
  let emb := unitEmbedding (m+1) n
  obtain ⟨R, B, S, hScard, hfail⟩ := Sharpness.exists_exact_failure_model
    m n F t ell hm hF hFn ht he emb emb.injective
  let p := incidenceTable R B
  let c := eps/3
  have hc : 0 < c := by dsimp [c]; positivity
  let A := tableLearner (fun u v j => c*p u v j) emb
  let Z := modelData emb
  let μ := FiniteExchangeable.blockPermutationLaw Z
  have hstable : onSampleDeletionStable A Z eps :=
    incidence_scaled_stable R B emb emb.injective (by omega) c eps hc.le (by dsimp [c]; linarith)
  have hae : ∀ᵐ W ∂μ, onSampleDeletionStable A W eps :=
    invariant_ae_permutationLaw (fun W => onSampleDeletionStable A W eps) Z hstable
      (fun e => (StabilityProbability.onSampleDeletionStable_relabel A Z e eps).mpr hstable)
  have hstableprob : μ.real {W | onSampleDeletionStable A W eps} = 1 := by
    have hs : {W | onSampleDeletionStable A W eps} =ᵐ[μ] Set.univ := by
      filter_upwards [hae] with W hW
      exact propext (iff_true_intro hW)
    rw [measureReal_congr hs]
    exact measureReal_univ_eq_one
  have hset : (univ.filter fun u => Setup.failure A Z u F t ell ht he) = S := by
    ext u
    simp only [mem_filter, mem_univ, true_and]
    exact (model_failure_scale_iff p emb emb.injective c hc F t ell ht he u).trans (hfail u)
  have hcount : (univ.filter fun u => Setup.failure A Z u F t ell ht he).card =
      RankFrontier.failureCount m F t ell := by
    rw [hset]
    simpa only [RankFrontier.failureCount, RankFrontier.capacity] using hScard
  refine ⟨A, Z, hstableprob, ?_⟩
  have hp := FiniteExchangeable.blockPermutationLaw_equivariant_probability Z
    (fun W i => Setup.failure A W i F t ell ht he)
    (fun i => Setup.measurableSet_failure A i F t ell ht he)
    (SetupEquivariance.failure_equivariant A F t ell ht he) (Fin.last m)
  simpa only [hcount, Fintype.card_fin, RankFrontier.failureRate] using hp

/-- The independent stable-class minimax problem for the original unexpanded rule. -/
def stableUnexpandedGamma (m n F t ell : ℕ) (eps : ℝ)
    (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m) : ℝ :=
  sSup {r : ℝ | ∃ (A : Learner UniversalCovariate n)
    (μ : Measure (Fin (m+1) → Block UniversalCovariate n)),
    IsProbabilityMeasure μ ∧ Exchangeable μ ∧
    μ.real {Z | onSampleDeletionStable A Z eps} = 1 ∧
    r = μ.real {Z | Setup.failure A Z (Fin.last m) F t ell ht he}}

/-- Remark 6.6 as an actual minimax identity: positive deletion stability
alone does not improve the original, unexpanded endpoint rule. -/
theorem stableUnexpandedGamma_eq (m n F t ell : ℕ) (eps : ℝ) (heps : 0 < eps)
    (hm : 1 ≤ m) (hF : 1 ≤ F) (hFn : F ≤ n) (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m) :
    stableUnexpandedGamma m n F t ell eps ht he = RankFrontier.failureRate m F t ell := by
  obtain ⟨A, Z, hstable, hprob⟩ := exists_stable_unexpanded_attaining_model
    m n F t ell eps heps hm hF hFn ht he
  let μ := FiniteExchangeable.blockPermutationLaw Z
  have hmem : RankFrontier.failureRate m F t ell ∈
      {r : ℝ | ∃ (A : Learner UniversalCovariate n)
        (ν : Measure (Fin (m+1) → Block UniversalCovariate n)),
        IsProbabilityMeasure ν ∧ Exchangeable ν ∧
        ν.real {W | onSampleDeletionStable A W eps} = 1 ∧
        r = ν.real {W | Setup.failure A W (Fin.last m) F t ell ht he}} :=
    ⟨A, μ, by dsimp [μ]; infer_instance,
      FiniteExchangeable.blockPermutationLaw_exchangeable Z, hstable, hprob.symm⟩
  have hbound : ∀ r ∈ {r : ℝ | ∃ (A : Learner UniversalCovariate n)
        (ν : Measure (Fin (m+1) → Block UniversalCovariate n)),
        IsProbabilityMeasure ν ∧ Exchangeable ν ∧
        ν.real {W | onSampleDeletionStable A W eps} = 1 ∧
        r = ν.real {W | Setup.failure A W (Fin.last m) F t ell ht he}},
      r ≤ RankFrontier.failureRate m F t ell := by
    intro r hr
    obtain ⟨B, ν, hν, hex, hs, rfl⟩ := hr
    letI : IsProbabilityMeasure ν := hν
    exact MainUpper.failure_probability_le B ν hex F t ell ht he (Fin.last m)
  unfold stableUnexpandedGamma
  exact le_antisymm (csSup_le ⟨_, hmem⟩ hbound) (le_csSup ⟨_, hbound⟩ hmem)

end
end MEJF.Scaling
