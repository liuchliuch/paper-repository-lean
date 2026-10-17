import MEJF.EfficiencyLaw
import MEJF.ResponsePerturbation
import MEJF.SetupEquivariance

/-! # Efficiency constructions evaluated by the actual multiset learner

This module connects the probability model and cyclic calculations to the
paper's `Setup.Learner`, `Setup.radius`, and actual endpoint rule.
-/
namespace MEJF.EfficiencyModel

open MEJF.Efficiency MEJF.EfficiencyLaw MEJF.OrderStatistics
open MEJF.SetupEquivariance MEJF.PredictionTable

noncomputable section
attribute [local instance] Classical.propDecidable

/-- One admissible measurable multiset learner realizes all cyclic pair tables. -/
def learner (K : ℝ) : Setup.Learner (Type20 × Coord19) 19 :=
  tableLearner (cyclicTable K) id

/-- The actual tuple of leave-environment predictions for a hypothetical test. -/
def predictions {X : Type*} [MeasurableSpace X] {m n : ℕ}
    (A : Setup.Learner X n) (Z : Fin (m+1) → Setup.Block X n)
    (u : Fin (m+1)) (j : Fin n) (k : Fin m) : ℝ :=
  Setup.pairPrediction A Z u (u.succAbove k) (Z u j).1

/-- The actual calibration score tuple for this hypothetical test. -/
def scores {X : Type*} [MeasurableSpace X] {m n : ℕ}
    (A : Setup.Learner X n) (Z : Fin (m+1) → Setup.Block X n)
    (u : Fin (m+1)) (t : ℕ) (ht : 1 ≤ t ∧ t ≤ n) (k : Fin m) : ℝ :=
  Setup.radius A Z (u.succAbove k) u t ht

/-- Actual endpoint-rule length in the 19-by-19 example. -/
def actualEndpointLength (K : ℝ) (Z : Fin 20 → Setup.Block (Type20 × Coord19) 19)
    (u : Fin 20) (j : Coord19) : ℝ :=
  intervalLength (Setup.lowerEndpoint (learner K) Z u j 2 2 (by omega) (by omega))
    (Setup.upperEndpoint (learner K) Z u j 2 2 (by omega) (by omega))

/-- The minmax envelope uses genuine extrema of the predictions and the genuine
outer δ-quantile of the inner α-score radii. -/
def actualMinmaxLength (K : ℝ) (Z : Fin 20 → Setup.Block (Type20 × Coord19) 19)
    (u : Fin 20) (j : Coord19) : ℝ :=
  minmaxLength (predictions (learner K) Z u j) (scores (learner K) Z u 4 (by omega))
    ⟨15, by omega⟩

lemma endpointLength_perm {m : ℕ} (p S : Fin (m+1) → ℝ) (k : Fin (m+1))
    (e : Equiv.Perm (Fin (m+1))) :
    endpointLength (p ∘ e) (S ∘ e) k = endpointLength p S k := by
  unfold endpointLength
  change intervalLength (stat ((fun i => p i-S i) ∘ e) k)
    (stat ((fun i => p i+S i) ∘ e) k.rev) = _
  rw [stat_perm, stat_perm]

lemma minmaxLength_perm {m : ℕ} (p S : Fin (m+1) → ℝ) (d : Fin (m+1))
    (e : Equiv.Perm (Fin (m+1))) :
    minmaxLength (p ∘ e) (S ∘ e) d = minmaxLength p S d := by
  unfold minmaxLength
  rw [stat_perm, stat_perm, stat_perm]

/-- The cyclic and standard deletion-index enumerations differ by a permutation. -/
def cyclicOtherPerm (u : Type20) : Equiv.Perm (Fin 19) :=
  (otherType20Equiv u).trans (otherEquiv u).symm

lemma cyclicOtherPerm_spec (u : Type20) (i : Fin 19) :
    u.succAbove (cyclicOtherPerm u i) = otherType20 u i := by
  have h := (otherEquiv u).apply_symm_apply (otherType20Equiv u i)
  exact congrArg Subtype.val h

/-- Unpermuted response array on the actual covariate-labelled block space. -/
def typeData (y : NoiseArray) : Fin 20 → Setup.Block (Type20 × Coord19) 19 :=
  modelDataWithResponses id (fun u j => y (u,j))

lemma predictions_typeData (K : ℝ) (y : NoiseArray) (u : Type20) (j : Coord19) :
    predictions (learner K) (typeData y) u j ∘ cyclicOtherPerm u =
      fun i => cyclicTable K u (otherType20 u i) j := by
  funext i
  unfold predictions
  simp only [Function.comp_apply, cyclicOtherPerm_spec]
  change Setup.pairPrediction (tableLearner (cyclicTable K) id)
    (modelDataWithResponses id (fun u j => y (u,j))) u (otherType20 u i) (u,j) = _
  exact modelResponses_pairPrediction (cyclicTable K) id (fun _ _ h => h) (by omega)
    (fun u j => y (u,j)) u (otherType20 u i) (otherType20_ne u i).symm j

lemma scores_typeData (K : ℝ) (y : NoiseArray) (u : Type20)
    (t : ℕ) (ht : 1 ≤ t ∧ t ≤ 19) :
    scores (learner K) (typeData y) u t ht ∘ cyclicOtherPerm u =
      cyclicScores K (Equiv.refl _,y) u (Setup.innerIndex 19 t ht) := by
  funext i
  unfold scores
  simp only [Function.comp_apply, cyclicOtherPerm_spec]
  change Setup.radius (tableLearner (cyclicTable K) id)
    (modelDataWithResponses id (fun u j => y (u,j))) (otherType20 u i) u t ht = _
  rw [modelResponses_radius (cyclicTable K) id (fun _ _ h => h) (by omega)
    (fun u j => y (u,j)) (otherType20 u i) u (otherType20_ne u i) t ht]
  rfl

/-- Both levels of the actual endpoint procedure equal the cyclic calculation. -/
theorem actualEndpointLength_typeData (K : ℝ) (y : NoiseArray) (u : Type20) (j : Coord19) :
    actualEndpointLength K (typeData y) u j = cyclicEndpointLength K (Equiv.refl _,y) u j := by
  change endpointLength (predictions (learner K) (typeData y) u j)
    (scores (learner K) (typeData y) u 2 (by omega)) ⟨1, by omega⟩ = _
  rw [← endpointLength_perm _ _ _ (cyclicOtherPerm u), predictions_typeData, scores_typeData]
  rfl

theorem actualMinmaxLength_typeData (K : ℝ) (y : NoiseArray) (u : Type20) (j : Coord19) :
    actualMinmaxLength K (typeData y) u j = cyclicMinmaxLength K (Equiv.refl _,y) u j := by
  unfold actualMinmaxLength
  rw [← minmaxLength_perm _ _ _ (cyclicOtherPerm u), predictions_typeData, scores_typeData]
  rfl

lemma predictions_relabel {X : Type*} [MeasurableSpace X] {m n : ℕ}
    (A : Setup.Learner X n) (Z : Fin (m+1) → Setup.Block X n)
    (e : Equiv.Perm (Fin (m+1))) (u : Fin (m+1)) (j : Fin n) :
    predictions A (Exchangeability.relabel e Z) (e u) j ∘ otherPerm e u =
      predictions A Z u j := by
  funext k
  unfold predictions
  simp only [Function.comp_apply, otherPerm_spec]
  have hZu : Exchangeability.relabel e Z (e u) = Z u := by simp [Exchangeability.relabel]
  rw [hZu, pairPrediction_relabel]

lemma scores_relabel {X : Type*} [MeasurableSpace X] {m n : ℕ}
    (A : Setup.Learner X n) (Z : Fin (m+1) → Setup.Block X n)
    (e : Equiv.Perm (Fin (m+1))) (u : Fin (m+1))
    (t : ℕ) (ht : 1 ≤ t ∧ t ≤ n) :
    scores A (Exchangeability.relabel e Z) (e u) t ht ∘ otherPerm e u =
      scores A Z u t ht := by
  funext k
  unfold scores
  simp only [Function.comp_apply, otherPerm_spec]
  rw [radius_relabel]

lemma actualEndpointLength_relabel (K : ℝ) (Z : Fin 20 → Setup.Block (Type20 × Coord19) 19)
    (e : Equiv.Perm (Fin 20)) (u : Fin 20) (j : Coord19) :
    actualEndpointLength K (Exchangeability.relabel e Z) (e u) j = actualEndpointLength K Z u j := by
  unfold actualEndpointLength
  rw [lowerEndpoint_relabel, upperEndpoint_relabel]

lemma actualMinmaxLength_relabel (K : ℝ) (Z : Fin 20 → Setup.Block (Type20 × Coord19) 19)
    (e : Equiv.Perm (Fin 20)) (u : Fin 20) (j : Coord19) :
    actualMinmaxLength K (Exchangeability.relabel e Z) (e u) j = actualMinmaxLength K Z u j := by
  unfold actualMinmaxLength
  rw [← minmaxLength_perm _ _ _ (otherPerm e u), predictions_relabel, scores_relabel]

/-- Actual learner/rule equality on every realization of the probabilistic source. -/
theorem actualEndpointLength_reveal (K : ℝ) (s : Sample) (i : Type20) (j : Coord19) :
    actualEndpointLength K (reveal s) i j = cyclicEndpointLength K s (s.1 i) j := by
  have hz : reveal s = Exchangeability.relabel s.1.symm (typeData s.2) := rfl
  rw [hz]
  have h := actualEndpointLength_relabel K (typeData s.2) s.1.symm (s.1 i) j
  have hi : s.1.symm (s.1 i) = i := s.1.left_inv i
  have h' := (congrArg
    (fun l => actualEndpointLength K (Exchangeability.relabel s.1.symm (typeData s.2)) l j) hi.symm).trans h
  exact h'.trans (actualEndpointLength_typeData K s.2 (s.1 i) j)

theorem actualMinmaxLength_reveal (K : ℝ) (s : Sample) (i : Type20) (j : Coord19) :
    actualMinmaxLength K (reveal s) i j = cyclicMinmaxLength K s (s.1 i) j := by
  have hz : reveal s = Exchangeability.relabel s.1.symm (typeData s.2) := rfl
  rw [hz]
  have h := actualMinmaxLength_relabel K (typeData s.2) s.1.symm (s.1 i) j
  have hi : s.1.symm (s.1 i) = i := s.1.left_inv i
  have h' := (congrArg
    (fun l => actualMinmaxLength K (Exchangeability.relabel s.1.symm (typeData s.2)) l j) hi.symm).trans h
  exact h'.trans (actualMinmaxLength_typeData K s.2 (s.1 i) j)

end
end MEJF.EfficiencyModel
