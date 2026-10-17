import MEJF.PredictionTable
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.Algebra.BigOperators.Fin

/-! # A jointly measurable learner on an ambient covariate space

This extends the finite construction of (5.3) by zero away from an injected
finite set. It acts on complete blocks in `(X × ℝ)^n`, and its evaluation map
is jointly measurable at every training arity. Recognition reads the entire
covariate tuple and ignores all responses.
-/
namespace MEJF.PredictionTable

open Finset MeasureTheory
noncomputable section
attribute [local instance] Classical.propDecidable

variable {V X : Type*} [Fintype V] [DecidableEq V] {n : ℕ}

abbrev AmbientBlock (X : Type*) (n : ℕ) := Fin n → X × ℝ

/-- Embed a complete finite-covariate block, retaining its responses. -/
def embedBlock (emb : V × Fin n → X) (Z : Block V (Fin n)) : AmbientBlock X n :=
  fun j => (emb (Z.x j), Z.y j)

def ambientRecognizes (emb : V × Fin n → X) (Z : AmbientBlock X n) (v : V) : Prop :=
  (fun j => (Z j).1) = fun j => emb (v, j)

/-- One complete ambient block's contribution in (5.3). -/
def ambientContribution (p : V → V → Fin n → ℝ) (emb : V × Fin n → X)
    (Z : AmbientBlock X n) (u : V) (j : Fin n) : ℝ :=
  ∑ v ∈ (univ : Finset V).erase u, if ambientRecognizes emb Z v then p u v j else 0

/-- The additive formula at a designated embedded covariate. -/
def ambientAt (p : V → V → Fin n → ℝ) (emb : V × Fin n → X)
    (T : Multiset (AmbientBlock X n)) (u : V) (j : Fin n) : ℝ :=
  tableConstant p u j - (T.map fun Z => ambientContribution p emb Z u j).sum

/-- One learner on all ambient covariates, with value zero off the finite image. -/
def ambientLearner (p : V → V → Fin n → ℝ) (emb : V × Fin n → X)
    (T : Multiset (AmbientBlock X n)) (x : X) : ℝ :=
  ∑ q : V × Fin n, if emb q = x then ambientAt p emb T q.1 q.2 else 0

lemma ambientLearner_at (p : V → V → Fin n → ℝ) (emb : V × Fin n → X)
    (hinj : Function.Injective emb) (T : Multiset (AmbientBlock X n)) (u : V) (j : Fin n) :
    ambientLearner p emb T (emb (u, j)) = ambientAt p emb T u j := by
  simp [ambientLearner, hinj.eq_iff]

lemma ambientLearner_off (p : V → V → Fin n → ℝ) (emb : V × Fin n → X)
    (T : Multiset (AmbientBlock X n)) (x : X) (hx : x ∉ Set.range emb) :
    ambientLearner p emb T x = 0 := by
  apply sum_eq_zero
  intro q _
  have hne : emb q ≠ x := by
    intro h
    exact hx ⟨q, h⟩
  simp only [hne, ↓reduceIte]

lemma ambientRecognizes_embedBlock (emb : V × Fin n → X) (hinj : Function.Injective emb)
    (Z : Block V (Fin n)) (v : V) :
    ambientRecognizes emb (embedBlock emb Z) v ↔ recognizes Z v := by
  constructor
  · intro h
    funext j
    exact hinj (congrFun h j)
  · intro h
    funext j
    exact congrArg emb (congrFun h j)

lemma ambientContribution_embedBlock (p : V → V → Fin n → ℝ)
    (emb : V × Fin n → X) (hinj : Function.Injective emb)
    (Z : Block V (Fin n)) (u : V) (j : Fin n) :
    ambientContribution p emb (embedBlock emb Z) u j = contribution p Z u j := by
  simp only [ambientContribution, contribution, ambientRecognizes_embedBlock emb hinj]

lemma ambientAt_embedMultiset (p : V → V → Fin n → ℝ)
    (emb : V × Fin n → X) (hinj : Function.Injective emb)
    (T : Multiset (Block V (Fin n))) (u : V) (j : Fin n) :
    ambientAt p emb (T.map (embedBlock emb)) u j = learner p T u j := by
  simp only [ambientAt, learner, Multiset.map_map, Function.comp_apply,
    ambientContribution_embedBlock p emb hinj]

/-- Exact arbitrary-table realization by one learner on the full ambient space. -/
theorem ambientLearner_leavePair (p : V → V → Fin n → ℝ)
    (emb : V × Fin n → X) (hinj : Function.Injective emb) (hn : 0 < n)
    (u v : V) (huv : u ≠ v) (j : Fin n) :
    ambientLearner p emb ((leavePair u v).map (embedBlock emb)) (emb (u, j)) = p u v j := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  rw [ambientLearner_at p emb hinj, ambientAt_embedMultiset p emb hinj,
    learner_leavePair p u v huv]

/-- The construction retains multiplicity and is symmetric in indexed input lists. -/
theorem ambientLearner_list_perm (p : V → V → Fin n → ℝ) (emb : V × Fin n → X)
    (T U : List (AmbientBlock X n)) (h : T.Perm U) (x : X) :
    ambientLearner p emb (T : Multiset (AmbientBlock X n)) x =
      ambientLearner p emb (U : Multiset (AmbientBlock X n)) x := by
  exact congrArg (fun M => ambientLearner p emb M x) (Quot.sound h)

section Measurability
variable [MeasurableSpace X] [MeasurableSingletonClass X]

/-- Full covariate-tuple recognition is measurable; responses remain arbitrary. -/
lemma measurable_ambientContribution (p : V → V → Fin n → ℝ) (emb : V × Fin n → X)
    (u : V) (j : Fin n) :
    Measurable (fun Z : AmbientBlock X n => ambientContribution p emb Z u j) := by
  unfold ambientContribution
  apply Finset.measurable_sum
  intro v _
  apply Measurable.ite _ measurable_const measurable_const
  have hcov : Measurable (fun Z : AmbientBlock X n => fun k => (Z k).1) :=
    measurable_pi_lambda _ fun k => measurable_fst.comp (measurable_pi_apply k)
  exact (measurableSet_singleton (fun k => emb (v, k))).preimage hcov

/-- At each arity, the additive formula is jointly measurable in the training tuple. -/
lemma measurable_ambientAt (p : V → V → Fin n → ℝ) (emb : V × Fin n → X)
    (r : ℕ) (u : V) (j : Fin n) :
    Measurable (fun T : Fin r → AmbientBlock X n =>
      ambientAt p emb ((List.ofFn T : List (AmbientBlock X n)) : Multiset (AmbientBlock X n)) u j) := by
  have hform : (fun T : Fin r → AmbientBlock X n =>
      ambientAt p emb ((List.ofFn T : List (AmbientBlock X n)) : Multiset (AmbientBlock X n)) u j) =
      fun T => tableConstant p u j - ∑ i, ambientContribution p emb (T i) u j := by
    funext T
    simp [ambientAt, List.map_ofFn, List.sum_ofFn]
  rw [hform]
  apply measurable_const.sub
  apply Finset.measurable_sum
  intro i _
  exact (measurable_ambientContribution p emb u j).comp (measurable_pi_apply i)

/-- The exact all-arity joint measurability requirement in Section 2.1. -/
theorem measurable_ambientLearner (p : V → V → Fin n → ℝ) (emb : V × Fin n → X)
    (r : ℕ) :
    Measurable (fun q : (Fin r → AmbientBlock X n) × X =>
      ambientLearner p emb ((List.ofFn q.1 : List (AmbientBlock X n)) : Multiset (AmbientBlock X n)) q.2) := by
  unfold ambientLearner
  apply Finset.measurable_sum
  intro vj _
  apply Measurable.ite
  · simpa only [eq_comm] using (measurableSet_singleton (emb vj)).preimage measurable_snd
  · exact (measurable_ambientAt p emb r vj.1 vj.2).comp measurable_fst
  · exact measurable_const

end Measurability
end
end MEJF.PredictionTable
