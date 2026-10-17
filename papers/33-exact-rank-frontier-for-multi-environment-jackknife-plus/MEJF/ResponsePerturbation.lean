import MEJF.PredictionModel

/-! # The constructed learner ignores responses

Arbitrary deterministic or random responses can be placed on the embedded block
types without changing any fitted table entry. This supplies the predictor part
of the response perturbations in Sections 5.1 and 7.2.
-/
namespace MEJF.PredictionTable

open Finset MeasureTheory
noncomputable section
attribute [local instance] Classical.propDecidable

variable {V X I : Type*} [Fintype V] [DecidableEq V] {n N : ℕ}

lemma ambientContribution_congr_covariates (p : V → V → Fin n → ℝ)
    (emb : V × Fin n → X) (Z W : AmbientBlock X n)
    (hx : ∀ j, (Z j).1 = (W j).1) (u : V) (j : Fin n) :
    ambientContribution p emb Z u j = ambientContribution p emb W u j := by
  have hfun : (fun j => (Z j).1) = fun j => (W j).1 := funext hx
  simp only [ambientContribution, ambientRecognizes, hfun]
  apply Finset.sum_congr rfl
  intro v hv
  split_ifs <;> rfl

lemma ambientAt_map_congr_covariates (p : V → V → Fin n → ℝ)
    (emb : V × Fin n → X) (s : Multiset I) (Z W : I → AmbientBlock X n)
    (hx : ∀ i j, (Z i j).1 = (W i j).1) (u : V) (j : Fin n) :
    ambientAt p emb (s.map Z) u j = ambientAt p emb (s.map W) u j := by
  unfold ambientAt
  congr 1
  apply congrArg Multiset.sum
  simp only [Multiset.map_map, Function.comp_apply]
  apply Multiset.map_congr rfl
  intro i _
  exact ambientContribution_congr_covariates p emb (Z i) (W i) (hx i) u j

/-- Equal full covariate tuples give identical predictions, including repeated inputs. -/
theorem ambientLearner_map_congr_covariates (p : V → V → Fin n → ℝ)
    (emb : V × Fin n → X) (s : Multiset I) (Z W : I → AmbientBlock X n)
    (hx : ∀ i j, (Z i j).1 = (W i j).1) (x : X) :
    ambientLearner p emb (s.map Z) x = ambientLearner p emb (s.map W) x := by
  unfold ambientLearner
  apply sum_congr rfl
  intro q _
  rw [ambientAt_map_congr_covariates p emb s Z W hx]

/-- Complete block types with an arbitrary response table. -/
def modelDataWithResponses (emb : Fin N × Fin n → X) (Y : Fin N → Fin n → ℝ) :
    Fin N → Setup.Block X n := fun u j => (emb (u, j), Y u j)

section Model
variable [MeasurableSpace X] [MeasurableSingletonClass X]

/-- Every arbitrary response table leaves the fitted prediction table unchanged. -/
theorem modelResponses_pairPrediction (p : Fin N → Fin N → Fin n → ℝ)
    (emb : Fin N × Fin n → X) (hinj : Function.Injective emb) (hn : 0 < n)
    (Y : Fin N → Fin n → ℝ) (u v : Fin N) (huv : u ≠ v) (j : Fin n) :
    Setup.pairPrediction (tableLearner p emb) (modelDataWithResponses emb Y) u v (emb (u, j)) =
      p u v j := by
  change ambientLearner p emb (((univ.erase u).erase v).val.map (modelDataWithResponses emb Y))
    (emb (u, j)) = _
  rw [ambientLearner_map_congr_covariates p emb _ (modelDataWithResponses emb Y)
    (modelData emb) (by intro i k; rfl)]
  exact model_pairPrediction p emb hinj hn u v huv j

/-- Actual residual order statistics after arbitrary response perturbation. -/
theorem modelResponses_radius (p : Fin N → Fin N → Fin n → ℝ)
    (emb : Fin N × Fin n → X) (hinj : Function.Injective emb) (hn : 0 < n)
    (Y : Fin N → Fin n → ℝ) (u v : Fin N) (huv : u ≠ v)
    (t : ℕ) (ht : 1 ≤ t ∧ t ≤ n) :
    Setup.radius (tableLearner p emb) (modelDataWithResponses emb Y) u v t ht =
      OrderStatistics.stat (fun j => |Y u j - p u v j|) (Setup.innerIndex n t ht) := by
  unfold Setup.radius
  change OrderStatistics.stat (fun j => |Y u j -
    Setup.pairPrediction (tableLearner p emb) (modelDataWithResponses emb Y) u v (emb (u, j))|) _ = _
  simp_rw [modelResponses_pairPrediction p emb hinj hn Y u v huv]

/-- A bounded response perturbation moves each constructed radius by at most its bound. -/
theorem modelResponses_radius_lipschitz (p : Fin N → Fin N → Fin n → ℝ)
    (emb : Fin N × Fin n → X) (hinj : Function.Injective emb) (hn : 0 < n)
    (Y : Fin N → Fin n → ℝ) (xi : ℝ) (hY : ∀ u j, |Y u j| ≤ xi)
    (u v : Fin N) (huv : u ≠ v) (t : ℕ) (ht : 1 ≤ t ∧ t ≤ n) :
    |Setup.radius (tableLearner p emb) (modelDataWithResponses emb Y) u v t ht -
      Setup.radius (tableLearner p emb) (modelData emb) u v t ht| ≤ xi := by
  rw [modelResponses_radius p emb hinj hn Y u v huv t ht,
    model_radius p emb hinj hn u v huv t ht]
  apply OrderStatistics.stat_lipschitz
  intro j
  calc
    abs (abs (Y u j - p u v j) - abs (p u v j)) =
        abs (abs (Y u j - p u v j) - abs (-p u v j)) := by rw [abs_neg]
    _ ≤ |(Y u j - p u v j) - (-p u v j)| := abs_abs_sub_abs_le_abs_sub _ _
    _ = |Y u j| := by ring_nf
    _ ≤ xi := hY u j

end Model
end
end MEJF.PredictionTable
