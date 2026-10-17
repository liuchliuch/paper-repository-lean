import MEJF.AmbientLearner
import MEJF.Setup
import Mathlib.Tactic.Positivity

/-! # The prediction-table construction in the paper's statistical model

The arbitrary-table construction is packaged as an admissible jointly measurable
`Setup.Learner` and evaluated on complete embedded block types. The resulting
pair predictions, residual ranks, and endpoint order statistics are the actual
objects defined in Section 2, rather than replacements by scalar formulas.
-/
namespace MEJF.PredictionTable

open Finset MeasureTheory
noncomputable section
attribute [local instance] Classical.propDecidable

variable {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X] {N m n : ℕ}

/-- The all-arity measurable learner realizing any finite prescribed table. -/
def tableLearner (p : Fin N → Fin N → Fin n → ℝ) (emb : Fin N × Fin n → X) :
    Setup.Learner X n where
  predict := ambientLearner p emb
  measurable_predict := measurable_ambientLearner p emb

/-- The zero-response complete block types in (5.1), in the ambient space. -/
def modelData (emb : Fin N × Fin n → X) : Fin N → Setup.Block X n :=
  fun u j => (emb (u, j), 0)

lemma modelData_eq_embedBlock (emb : Fin N × Fin n → X) (u : Fin N) :
    modelData emb u = embedBlock emb (typeBlock u) := rfl

/-- The actual leave-two fit in the statistical setup returns its prescribed entry. -/
theorem model_pairPrediction (p : Fin N → Fin N → Fin n → ℝ)
    (emb : Fin N × Fin n → X) (hinj : Function.Injective emb) (hn : 0 < n)
    (u v : Fin N) (huv : u ≠ v) (j : Fin n) :
    Setup.pairPrediction (tableLearner p emb) (modelData emb) u v (emb (u, j)) = p u v j := by
  have htrain : (((univ.erase u).erase v).val.map (modelData emb)) =
      (leavePair u v).map (embedBlock emb) := by
    simp only [leavePair, Multiset.map_map, Function.comp_apply]
    rfl
  change ambientLearner p emb _ (emb (u, j)) = _
  rw [htrain]
  exact ambientLearner_leavePair p emb hinj hn u v huv j

/-- Exact sorted residuals for an arbitrary prescribed real table. -/
theorem model_radius (p : Fin N → Fin N → Fin n → ℝ)
    (emb : Fin N × Fin n → X) (hinj : Function.Injective emb) (hn : 0 < n)
    (u v : Fin N) (huv : u ≠ v) (t : ℕ) (ht : 1 ≤ t ∧ t ≤ n) :
    Setup.radius (tableLearner p emb) (modelData emb) u v t ht =
      OrderStatistics.stat (fun j => |p u v j|) (Setup.innerIndex n t ht) := by
  unfold Setup.radius
  change OrderStatistics.stat (fun j => |0 -
    Setup.pairPrediction (tableLearner p emb) (modelData emb) u v (emb (u, j))|) _ = _
  simp_rw [model_pairPrediction p emb hinj hn u v huv]
  simp only [zero_sub, abs_neg]

/-- In the actual ambient model the incidence table gives the one/two radii (5.4). -/
theorem model_radius_incidence (edge : Fin N → Fin N → Prop) [DecidableRel edge]
    (hasym : ∀ {u v}, edge u v → ¬ edge v u)
    (B : Fin N → Fin n → Fin N → Bool) (emb : Fin N × Fin n → X)
    (hinj : Function.Injective emb) (t : ℕ) (ht : 1 ≤ t ∧ t ≤ n)
    (hmarked : ∀ u v, edge u v → t ≤ markedCount B u v)
    (hunmarked : ∀ u v, ¬ edge u v → markedCount B u v < t)
    (u v : Fin N) (huv : u ≠ v) :
    Setup.radius (tableLearner (incidenceTable edge B) emb) (modelData emb) u v t ht =
      if edge u v then 2 else 1 := by
  rw [model_radius _ emb hinj (by omega) u v huv t ht]
  simp_rw [abs_of_pos (incidenceTable_pos edge B u v _)]
  exact tableRadius_incidence edge hasym B (by omega) ht.2 hmarked hunmarked u v

/-- Substituting the actual fitted predictions and radii yields (5.5). -/
theorem model_lowerEndpoint_incidence (edge : Fin (m+1) → Fin (m+1) → Prop) [DecidableRel edge]
    (hasym : ∀ {u v}, edge u v → ¬ edge v u)
    (B : Fin (m+1) → Fin n → Fin (m+1) → Bool) (emb : Fin (m+1) × Fin n → X)
    (hinj : Function.Injective emb) (t ell : ℕ) (ht : 1 ≤ t ∧ t ≤ n)
    (he : 1 ≤ ell ∧ ell ≤ m)
    (hmarked : ∀ u v, edge u v → t ≤ markedCount B u v)
    (hunmarked : ∀ u v, ¬ edge u v → markedCount B u v < t)
    (u : Fin (m+1)) (j : Fin n) :
    Setup.lowerEndpoint (tableLearner (incidenceTable edge B) emb) (modelData emb) u j t ell ht he =
      OrderStatistics.stat (fun k : Fin m => incidenceLower edge B u (u.succAbove k) j)
        (Setup.lowerIndex m ell he) := by
  unfold Setup.lowerEndpoint
  congr 1
  funext k
  change Setup.pairPrediction _ _ u (u.succAbove k) (emb (u, j)) - _ = _
  rw [model_pairPrediction _ emb hinj (by omega) u (u.succAbove k) (u.ne_succAbove k) j,
    model_radius_incidence edge hasym B emb hinj t ht hmarked hunmarked (u.succAbove k) u
      (u.succAbove_ne k)]
  rfl

theorem model_upperEndpoint_incidence (edge : Fin (m+1) → Fin (m+1) → Prop) [DecidableRel edge]
    (hasym : ∀ {u v}, edge u v → ¬ edge v u)
    (B : Fin (m+1) → Fin n → Fin (m+1) → Bool) (emb : Fin (m+1) × Fin n → X)
    (hinj : Function.Injective emb) (t ell : ℕ) (ht : 1 ≤ t ∧ t ≤ n)
    (he : 1 ≤ ell ∧ ell ≤ m)
    (hmarked : ∀ u v, edge u v → t ≤ markedCount B u v)
    (hunmarked : ∀ u v, ¬ edge u v → markedCount B u v < t)
    (u : Fin (m+1)) (j : Fin n) :
    Setup.upperEndpoint (tableLearner (incidenceTable edge B) emb) (modelData emb) u j t ell ht he =
      OrderStatistics.stat (fun k : Fin m => incidenceUpper edge B u (u.succAbove k) j)
        (Setup.upperIndex m ell he) := by
  unfold Setup.upperEndpoint
  congr 1
  funext k
  change Setup.pairPrediction _ _ u (u.succAbove k) (emb (u, j)) + _ = _
  rw [model_pairPrediction _ emb hinj (by omega) u (u.succAbove k) (u.ne_succAbove k) j,
    model_radius_incidence edge hasym B emb hinj t ht hmarked hunmarked (u.succAbove k) u
      (u.succAbove_ne k)]
  rfl

/-- Exactly the prescribed coordinates fail for the actual admissible learner. -/
theorem model_failure_set (edge : Fin (m+1) → Fin (m+1) → Prop) [DecidableRel edge]
    (hasym : ∀ {u v}, edge u v → ¬ edge v u)
    (B : Fin (m+1) → Fin n → Fin (m+1) → Bool) (emb : Fin (m+1) × Fin n → X)
    (hinj : Function.Injective emb) (t ell : ℕ) (ht : 1 ≤ t ∧ t ≤ n)
    (he : 1 ≤ ell ∧ ell ≤ m)
    (hmarked : ∀ u v, edge u v → t ≤ markedCount B u v)
    (hunmarked : ∀ u v, ¬ edge u v → markedCount B u v < t)
    (u : Fin (m+1)) (s : Finset (Fin n))
    (hrows : ∀ j ∈ s, (univ.filter fun k : Fin m => B u j (u.succAbove k) = false).card = ell - 1)
    (hzero : ∀ j ∉ s, ∀ k : Fin m, B u j (u.succAbove k) = false) :
    (univ.filter fun j => ¬ Setup.covered
      (tableLearner (incidenceTable edge B) emb) (modelData emb) u j t ell ht he) = s := by
  classical
  ext j
  simp only [mem_filter, mem_univ, true_and, Setup.covered, modelData, Set.mem_Icc]
  rw [model_lowerEndpoint_incidence edge hasym B emb hinj t ell ht he hmarked hunmarked,
    model_upperEndpoint_incidence edge hasym B emb hinj t ell ht he hmarked hunmarked]
  by_cases hj : j ∈ s
  · simp only [hj, iff_true]
    exact incidence_coordinate_miss edge B u j u.succAbove (by omega) he.2 (hrows j hj)
      (Setup.upperIndex m ell he)
  · simp only [hj, iff_false, not_not]
    exact incidence_zero_coordinate_covered edge B u j u.succAbove (hzero j hj)
      (Setup.lowerIndex m ell he) (Setup.upperIndex m ell he)

/-- A concrete injection of the finite covariate table into the paper's `[0,1]`. -/
def unitEmbedding (N n : ℕ) : Fin N × Fin n ↪ Setup.UniversalCovariate where
  toFun q := ⟨((Fintype.equivFin (Fin N × Fin n) q).val : ℝ) /
      (Fintype.card (Fin N × Fin n) + 1), by
    have hd : (0 : ℝ) < Fintype.card (Fin N × Fin n) + 1 := by positivity
    constructor
    · positivity
    · apply (div_le_one hd).mpr
      have hlt := (Fintype.equivFin (Fin N × Fin n) q).isLt
      exact_mod_cast (show (Fintype.equivFin (Fin N × Fin n) q).val ≤
        Fintype.card (Fin N × Fin n) + 1 by omega)⟩
  inj' := by
    intro a b hab
    apply (Fintype.equivFin (Fin N × Fin n)).injective
    apply Fin.ext
    have hval := congrArg (fun z : Setup.UniversalCovariate => (z : ℝ)) hab
    have hd : (Fintype.card (Fin N × Fin n) : ℝ) + 1 ≠ 0 := by positivity
    have hcast := (div_left_inj' hd).mp hval
    exact_mod_cast hcast

end
end MEJF.PredictionTable
