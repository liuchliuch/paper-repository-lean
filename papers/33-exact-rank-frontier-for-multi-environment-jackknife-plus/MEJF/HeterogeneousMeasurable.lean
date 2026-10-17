import MEJF.HeterogeneousSetup
import MEJF.SetupMeasurable
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import MEJF.MeasurableSigma

/-! Measurability of the original positive-rank heterogeneous rule. The finite
size domain is explicit. Outside it this auxiliary total event is false; every
law in §6.1 is supported on that domain. No upper-bound premise is introduced. -/
namespace MEJF.HeterogeneousProbability
open MeasureTheory Finset MEJF.HeterogeneousSetup MEJF.MeasurableSigma
noncomputable section
attribute [local instance] Classical.propDecidable
variable {X : Type*} [MeasurableSpace X] [Nonempty X] {m N : ℕ}

/-- Total version of the paper's event on its positive-finite-rank domain. -/
def finiteFailure (A : Learner X) (Z : Fin (m+1) → Block X) (alpha a : ℝ)
    (ell : ℕ) (he : 1 ≤ ell ∧ ell ≤ m) (i : Fin (m+1)) : Prop :=
  ∃ ht : ∀ k, 1 ≤ innerRank a Z k ∧ innerRank a Z k ≤ size (Z k),
    learnerFailure A Z (failureRank alpha Z) (innerRank a Z) ht ell he i

lemma finiteFailure_iff (A : Learner X) (Z : Fin (m+1) → Block X) (alpha a : ℝ)
    (ell : ℕ) (he : 1 ≤ ell ∧ ell ≤ m) (i : Fin (m+1))
    (ht : ∀ k, 1 ≤ innerRank a Z k ∧ innerRank a Z k ≤ size (Z k)) :
    finiteFailure A Z alpha a ell he i ↔
      learnerFailure A Z (failureRank alpha Z) (innerRank a Z) ht ell he i := by
  exact ⟨fun ⟨_,h⟩ => h, fun h => ⟨ht,h⟩⟩

def sizeVector (Z : Fin N → Block X) : Fin N → ℕ+ := fun i => (Z i).1

def coordinate (r : ℕ+) (j : Fin r.val) (z : Block X) : X×ℝ :=
  if h : z.1=r then z.2 (Fin.cast (congrArg PNat.val h).symm j) else (Classical.choice inferInstance,0)

lemma measurable_coordinate (r : ℕ+) (j : Fin r.val) :
    Measurable (coordinate (X := X) r j) := by
  apply measurable_sigma_iff.mpr
  intro s
  by_cases hs : s=r
  · subst s
    simpa only [Function.comp_def,coordinate, dif_pos rfl, Fin.cast_refl] using
      (measurable_pi_apply j : Measurable fun z : Fin r.val → X×ℝ => z j)
  · simpa only [Function.comp_def,coordinate, dif_neg hs] using
      (measurable_const : Measurable fun _ : Fin s.val → X×ℝ =>
        (Classical.choice (inferInstance : Nonempty X), (0:ℝ)))

/-- A measurable fixed-size chart. It agrees with the actual data on its size fiber. -/
def chart (ns : Fin N → ℕ+) (Z : Fin N → Block X) : Fin N → Block X :=
  fun i => ⟨ns i, fun j => coordinate (ns i) j (Z i)⟩

lemma measurable_chart (ns : Fin N → ℕ+) : Measurable (chart (X := X) ns) := by
  apply measurable_pi_iff.mpr
  intro i
  exact (measurable_sigma_mk (ns i)).comp (measurable_pi_iff.mpr fun j =>
    (measurable_coordinate (ns i) j).comp (measurable_pi_apply i))

lemma chart_eq (ns : Fin N → ℕ+) (Z : Fin N → Block X) (h : sizeVector Z=ns) : chart ns Z=Z := by
  funext i
  have hi := congrFun h i
  rcases hz : Z i with ⟨s,z⟩
  change (Z i).1=ns i at hi
  rw [hz] at hi
  cases hi
  change (⟨ns i, fun j => coordinate (ns i) j (Z i)⟩ : Block X) = ⟨ns i,z⟩
  rw [hz]
  simp [coordinate]

lemma measurable_sizeVector : Measurable (sizeVector (X := X) (N := N)) := by
  exact measurable_pi_iff.mpr fun i => measurable_sigma_fst.comp (measurable_pi_apply i)

lemma measurable_predict_finset (A : Learner X) (s : Finset (Fin N)) :
    Measurable (fun q : (Fin N → Block X)×X => A.predict (s.val.map q.1) q.2) := by
  have henum : Measurable (fun q : (Fin N → Block X)×X =>
      ((fun l : Fin s.card => q.1 (s.orderEmbOfFin rfl l)), q.2)) :=
    (measurable_pi_iff.mpr fun l => (measurable_pi_apply _).comp measurable_fst).prodMk measurable_snd
  have h := (A.measurable_predict s.card).comp henum
  simpa only [Function.comp_def, Setup.ofFn_finset_map] using h

lemma measurable_pairPrediction (A : Learner X) (i k : Fin N) :
    Measurable (fun q : (Fin N → Block X)×X => pairPrediction A q.1 i k q.2) :=
  measurable_predict_finset A ((univ.erase i).erase k)

lemma measurable_chartResponse (ns : Fin N → ℕ+) (i : Fin N) (j : Fin (ns i).val) :
    Measurable (fun Z : Fin N → Block X => ((chart ns Z i).2 j).2) :=
  measurable_snd.comp ((measurable_coordinate (ns i) j).comp (measurable_pi_apply i))

lemma measurable_chartPrediction (A : Learner X) (ns : Fin N → ℕ+)
    (i k : Fin N) (j : Fin (ns i).val) :
    Measurable (fun Z : Fin N → Block X =>
      pairPrediction A (chart ns Z) i k ((chart ns Z i).2 j).1) :=
  (measurable_pairPrediction A i k).comp ((measurable_chart ns).prodMk
    (measurable_fst.comp ((measurable_coordinate (ns i) j).comp (measurable_pi_apply i))))

lemma measurable_chartScore (A : Learner X) (ns : Fin (m+1) → ℕ+)
    (t : Fin (m+1) → ℕ) (ht : ∀ k, 1 ≤ t k ∧ t k ≤ (ns k).val) (i k : Fin (m+1)) :
    Measurable (fun Z : Fin (m+1) → Block X =>
      score (fun i => (ns i).val) (learnerResponses (chart ns Z))
        (learnerPredictions A (chart ns Z)) t ht i k) := by
  apply OrderStatistics.measurable_stat_comp
  intro j
  exact continuous_abs.measurable.comp
    ((measurable_chartResponse ns i j).sub (measurable_chartPrediction A ns i k j))

lemma measurable_chartLower (A : Learner X) (ns : Fin (m+1) → ℕ+)
    (t : Fin (m+1) → ℕ) (ht : ∀ k, 1 ≤ t k ∧ t k ≤ (ns k).val)
    (ell : ℕ) (he : 1 ≤ ell ∧ ell ≤ m) (i : Fin (m+1)) (j : Fin (ns i).val) :
    Measurable (fun Z : Fin (m+1) → Block X =>
      lower (fun i => (ns i).val) (learnerResponses (chart ns Z))
        (learnerPredictions A (chart ns Z)) t ht ell he i j) := by
  apply OrderStatistics.measurable_stat_comp
  intro k
  exact (measurable_chartPrediction A ns i (i.succAbove k) j).sub
    (measurable_chartScore A ns t ht (i.succAbove k) i)

lemma measurable_chartUpper (A : Learner X) (ns : Fin (m+1) → ℕ+)
    (t : Fin (m+1) → ℕ) (ht : ∀ k, 1 ≤ t k ∧ t k ≤ (ns k).val)
    (ell : ℕ) (he : 1 ≤ ell ∧ ell ≤ m) (i : Fin (m+1)) (j : Fin (ns i).val) :
    Measurable (fun Z : Fin (m+1) → Block X =>
      upper (fun i => (ns i).val) (learnerResponses (chart ns Z))
        (learnerPredictions A (chart ns Z)) t ht ell he i j) := by
  apply OrderStatistics.measurable_stat_comp
  intro k
  exact (measurable_chartPrediction A ns i (i.succAbove k) j).add
    (measurable_chartScore A ns t ht (i.succAbove k) i)

lemma measurableSet_chartFailure (A : Learner X) (ns : Fin (m+1) → ℕ+)
    (alpha a : ℝ) (ell : ℕ) (he : 1 ≤ ell ∧ ell ≤ m) (i : Fin (m+1)) :
    MeasurableSet {Z : Fin (m+1) → Block X | finiteFailure A (chart ns Z) alpha a ell he i} := by
  let t : Fin (m+1) → ℕ := fun k => ⌊a*((ns k).val+1)⌋₊
  let F : Fin (m+1) → ℕ := fun k => ⌊alpha*(ns k).val⌋₊+1
  by_cases ht : ∀ k, 1 ≤ t k ∧ t k ≤ (ns k).val
  · have hm : Measurable (fun Z : Fin (m+1) → Block X =>
        ∑ j : Fin (ns i).val, if ¬ covered (fun k => (ns k).val)
          (learnerResponses (chart ns Z)) (learnerPredictions A (chart ns Z)) t ht ell he i j
            then (1:ℕ) else 0) := by
      apply Finset.measurable_sum
      intro j _
      have hc : MeasurableSet {Z : Fin (m+1) → Block X |
          covered (fun k => (ns k).val) (learnerResponses (chart ns Z))
            (learnerPredictions A (chart ns Z)) t ht ell he i j} :=
        (measurableSet_le (measurable_chartLower A ns t ht ell he i j)
          (measurable_chartResponse ns i j)).inter
        (measurableSet_le (measurable_chartResponse ns i j)
          (measurable_chartUpper A ns t ht ell he i j))
      exact Measurable.ite hc.compl measurable_const measurable_const
    have hc : MeasurableSet {Z : Fin (m+1) → Block X |
        failure (fun k => (ns k).val) (learnerResponses (chart ns Z))
          (learnerPredictions A (chart ns Z)) F t ht ell he i} := by
      have hh := measurableSet_le (measurable_const (a := F i)) hm
      simpa only [HeterogeneousSetup.failure,Finset.sum_boole] using hh
    have heq : {Z : Fin (m+1) → Block X | finiteFailure A (chart ns Z) alpha a ell he i} =
        {Z | failure (fun k => (ns k).val) (learnerResponses (chart ns Z))
          (learnerPredictions A (chart ns Z)) F t ht ell he i} := by
      ext Z
      exact finiteFailure_iff A (chart ns Z) alpha a ell he i ht
    rw [heq]
    exact hc
  · have heq : {Z : Fin (m+1) → Block X | finiteFailure A (chart ns Z) alpha a ell he i} = ∅ := by
      ext Z
      simp only [Set.mem_setOf_eq,Set.mem_empty_iff_false,iff_false]
      intro ⟨hz,_⟩
      exact ht hz
    rw [heq]
    exact MeasurableSet.empty

/-- Countable size fibers prove measurability on the genuine disjoint-union
sample space; no measurability of the failure event is added as a premise. -/
theorem measurableSet_finiteFailure (A : Learner X) (alpha a : ℝ)
    (ell : ℕ) (he : 1 ≤ ell ∧ ell ≤ m) (i : Fin (m+1)) :
    MeasurableSet {Z : Fin (m+1) → Block X | finiteFailure A Z alpha a ell he i} := by
  have heq : {Z : Fin (m+1) → Block X | finiteFailure A Z alpha a ell he i} =
      ⋃ ns : Fin (m+1) → ℕ+, {Z | sizeVector Z=ns} ∩
        {Z | finiteFailure A (chart ns Z) alpha a ell he i} := by
    ext Z
    simp only [Set.mem_setOf_eq,Set.mem_iUnion,Set.mem_inter_iff]
    constructor
    · intro h
      refine ⟨sizeVector Z,rfl,?_⟩
      rwa [chart_eq _ Z rfl]
    · rintro ⟨ns,hsize,hfail⟩
      rwa [chart_eq ns Z hsize] at hfail
  rw [heq]
  exact MeasurableSet.iUnion fun ns =>
    ((measurableSet_singleton ns).preimage measurable_sizeVector).inter
      (measurableSet_chartFailure A ns alpha a ell he i)

end
end MEJF.HeterogeneousProbability
