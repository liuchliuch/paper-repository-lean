import MEJF.RandomizedRanks
import MEJF.Extensions
import Mathlib.Data.Finset.Max

/-! Actual finite tournament optimization, with no score characterization assumed. -/
namespace MEJF.TournamentOptimization
open Finset
noncomputable section
attribute [local instance] Classical.propDecidable

abbrev Tour (N : ℕ) := Extensions.Tournament N

instance tourFinite (N : ℕ) : Finite (Tour N) := by
  apply Finite.of_injective (fun T : Tour N => T.wins)
  intro T U h
  cases T
  cases U
  cases h
  rfl

instance tourFintype (N : ℕ) : Fintype (Tour N) := Fintype.ofFinite _

instance tourNonempty (N : ℕ) : Nonempty (Tour N) := by
  refine ⟨⟨fun u v => decide (u < v), ?_, ?_⟩⟩
  · intro u; simp
  · intro u v h
    simp only [decide_eq_true_eq, decide_eq_false_iff_not]
    omega

def relation {N : ℕ} (T : Tour N) (u v : Fin N) : Prop := T.wins u v = true

theorem relation_asymm {N : ℕ} (T : Tour N) :
    ∀ u v, relation T u v → ¬ relation T v u := by
  intro u v huv hvu
  by_cases h : u = v
  · subst v; simpa [relation, T.noLoop] using huv
  · have := (T.complete u v h).mp huv
    rw [hvu] at this
    cases this

def degree {N : ℕ} (T : Tour N) (u : Fin N) : ℕ :=
  ExtremalGraph.outdegree (relation T) u

lemma degree_eq_extensions {N : ℕ} (T : Tour N) (u : Fin N) :
    degree T u = Extensions.Tournament.degree T u := by
  simp only [degree, ExtremalGraph.outdegree, Extensions.Tournament.degree,
    Extensions.Tournament.edge, sum_boole]
  congr 1
  ext v
  simp [relation]

/-- Complete each missing comparison by the fixed order of labels. -/
def complete {N : ℕ} (R : Fin N → Fin N → Prop)
    (hasym : ∀ u v, R u v → ¬ R v u) : Tour N where
  wins u v := decide (R u v ∨ (¬ R v u ∧ u < v))
  noLoop u := by
    have h : ¬ R u u := fun h => hasym u u h h
    simp [h]
  complete u v huv := by
    have hn : ¬ (R u v ∧ R v u) := by rintro ⟨h1,h2⟩; exact hasym u v h1 h2
    by_cases h1 : R u v <;> by_cases h2 : R v u <;> simp_all
    omega

lemma completion_contains {N : ℕ} (R : Fin N → Fin N → Prop)
    (hasym : ∀ u v, R u v → ¬ R v u) {u v : Fin N} (h : R u v) :
    relation (complete R hasym) u v := by simp [relation, complete, h]

lemma completion_degree {N : ℕ} (R : Fin N → Fin N → Prop)
    (hasym : ∀ u v, R u v → ¬ R v u) (u : Fin N) :
    ExtremalGraph.outdegree R u ≤ degree (complete R hasym) u := by
  unfold degree ExtremalGraph.outdegree
  apply card_mono
  intro v hv
  simp only [mem_filter, mem_univ, true_and] at hv ⊢
  exact completion_contains R hasym hv

/-- The actual tournament score payoff appearing in (6.22). -/
def objective (F m t : ℕ) (pi : Fin m → ℝ) (T : Tour (m+1)) : ℝ :=
  ∑ u, RandomizedRanks.payoff F m t pi (degree T u)

theorem exists_maximizer (F m t : ℕ) (pi : Fin m → ℝ) :
    ∃ T : Tour (m+1), ∀ U : Tour (m+1), objective F m t pi U ≤ objective F m t pi T := by
  obtain ⟨T, _, hT⟩ := (univ : Finset (Tour (m+1))).exists_max_image (objective F m t pi) univ_nonempty
  exact ⟨T, fun U => hT U (mem_univ U)⟩

/-- A genuine finite maximum over tournaments. -/
def maxObjective (F m t : ℕ) (pi : Fin m → ℝ) : ℝ :=
  objective F m t pi (Classical.choose (exists_maximizer F m t pi))

theorem le_maxObjective (F m t : ℕ) (pi : Fin m → ℝ) (T : Tour (m+1)) :
    objective F m t pi T ≤ maxObjective F m t pi :=
  Classical.choose_spec (exists_maximizer F m t pi) T

theorem maxObjective_attained (F m t : ℕ) (pi : Fin m → ℝ) :
    ∃ T : Tour (m+1), objective F m t pi T = maxObjective F m t pi :=
  ⟨_, rfl⟩

theorem oriented_payoff_le_max (F m t : ℕ) (pi : Fin m → ℝ) (hpi : ∀ l, 0 ≤ pi l)
    (R : Fin (m+1) → Fin (m+1) → Prop) (hasym : ∀ u v, R u v → ¬ R v u) :
    (∑ u, RandomizedRanks.payoff F m t pi (ExtremalGraph.outdegree R u)) ≤ maxObjective F m t pi := by
  apply le_trans ?_ (le_maxObjective F m t pi (complete R hasym))
  apply sum_le_sum
  intro u _
  exact RandomizedRanks.payoff_mono F m t pi hpi (completion_degree R hasym u)

end
end MEJF.TournamentOptimization
