import MEJF.HeterogeneousSetup
import MEJF.SetupEquivariance
import MEJF.HeterogeneousMeasurable

/-! # Relabeling covariance of the actual variable-size rule

Total adaptive radii are used only to avoid dependent casts when changing block
labels. On the positive finite-rank domain they are proved equal to the actual
score from `HeterogeneousSetup`; the final event remains the original event.
-/
namespace MEJF.HeterogeneousEquivariance

open Finset MeasureTheory MEJF.Exchangeability MEJF.HeterogeneousSetup
noncomputable section
attribute [local instance] Classical.propDecidable

variable {X : Type*} [MeasurableSpace X] {m N : ℕ}

lemma training_relabel (Z : Fin N → Block X) (e : Equiv.Perm (Fin N)) (i k : Fin N) :
    (((univ.erase (e i)).erase (e k)).val.map (relabel e Z)) =
      (((univ.erase i).erase k).val.map Z) := by
  have hs : (((univ.erase (e i)).erase (e k)).map e.symm.toEmbedding) =
      (univ.erase i).erase k := by simp
  have hh := congrArg (fun s : Finset (Fin N) => s.val.map Z) hs
  simpa only [Finset.map_val, Multiset.map_map, Equiv.coe_toEmbedding,
    Function.comp_def, relabel] using hh

lemma pairPrediction_relabel (A : Learner X) (Z : Fin N → Block X)
    (e : Equiv.Perm (Fin N)) (i k : Fin N) (x : X) :
    pairPrediction A (relabel e Z) (e i) (e k) x = pairPrediction A Z i k x := by
  unfold pairPrediction
  rw [training_relabel]

/-- The source's realized unordered size multiset is invariant, retaining multiplicities. -/
theorem sizeMultiset_relabel (Z : Fin N → Block X) (e : Equiv.Perm (Fin N)) :
    sizeMultiset (relabel e Z) = sizeMultiset Z := by
  have hs : (univ : Finset (Fin N)).map e.symm.toEmbedding = univ := by simp
  have hh := congrArg (fun s : Finset (Fin N) => s.val.map (fun i => size (Z i))) hs
  simpa only [sizeMultiset, Finset.map_val, Multiset.map_map, Equiv.coe_toEmbedding,
    Function.comp_def, relabel] using hh

lemma innerRank_relabel (Z : Fin N → Block X) (e : Equiv.Perm (Fin N)) (a : ℝ) (i : Fin N) :
    innerRank a (relabel e Z) (e i) = innerRank a Z i := by
  simp only [innerRank, relabel, Function.comp_apply, Equiv.symm_apply_apply]

lemma failureRank_relabel (Z : Fin N → Block X) (e : Equiv.Perm (Fin N)) (alpha : ℝ) (i : Fin N) :
    failureRank alpha (relabel e Z) (e i) = failureRank alpha Z i := by
  simp only [failureRank, relabel, Function.comp_apply, Equiv.symm_apply_apply]

/-- The domain required in §6.1: all source inner ranks are positive and finite. -/
def finiteDomain (Z : Fin (m+1) → Block X) (a : ℝ) : Prop :=
  ∀ i, 1 ≤ innerRank a Z i ∧ innerRank a Z i ≤ size (Z i)

lemma finiteDomain_relabel (Z : Fin (m+1) → Block X) (e : Equiv.Perm (Fin (m+1))) (a : ℝ) :
    finiteDomain (relabel e Z) a ↔ finiteDomain Z a := by
  constructor
  · intro h i
    have hi := h (e i)
    simpa only [innerRank, relabel, Function.comp_apply, Equiv.symm_apply_apply] using hi
  · intro h k
    obtain ⟨i, rfl⟩ := e.surjective k
    simpa only [innerRank, relabel, Function.comp_apply, Equiv.symm_apply_apply] using h i

/-- A total radius as a function of one whole block; this avoids transporting
coordinate types when the block label changes. -/
def blockRadius (A : Learner X) (T : Multiset (Block X)) (z : Block X) (a : ℝ) : ℝ :=
  if ht : 1 ≤ ⌊a*(size z+1)⌋₊ ∧ ⌊a*(size z+1)⌋₊ ≤ size z then
    OrderStatistics.stat (fun j : Fin (size z) => |(z.2 j).2 - A.predict T (z.2 j).1|)
      (Setup.innerIndex (size z) ⌊a*(size z+1)⌋₊ ht)
  else 0

/-- A total adaptive radius; outside the finite domain this auxiliary value is zero. -/
def adaptiveRadius (A : Learner X) (Z : Fin (m+1) → Block X) (a : ℝ) (i k : Fin (m+1)) : ℝ :=
  blockRadius A (((univ.erase i).erase k).val.map Z) (Z i) a

lemma adaptiveRadius_relabel (A : Learner X) (Z : Fin (m+1) → Block X)
    (e : Equiv.Perm (Fin (m+1))) (a : ℝ) (i k : Fin (m+1)) :
    adaptiveRadius A (relabel e Z) a (e i) (e k) = adaptiveRadius A Z a i k := by
  unfold adaptiveRadius
  rw [training_relabel]
  have hZi : relabel e Z (e i) = Z i := by simp only [relabel, Function.comp_apply, Equiv.symm_apply_apply]
  rw [hZi]

lemma adaptiveRadius_eq (A : Learner X) (Z : Fin (m+1) → Block X) (a : ℝ)
    (ht : finiteDomain Z a) (i k : Fin (m+1)) :
    adaptiveRadius A Z a i k = HeterogeneousSetup.radius A Z (innerRank a Z) ht i k := by
  have hti : 1 ≤ ⌊a*(size (Z i)+1)⌋₊ ∧ ⌊a*(size (Z i)+1)⌋₊ ≤ size (Z i) := ht i
  rw [adaptiveRadius, blockRadius, dif_pos hti]
  rfl

/-- Total endpoints at an arbitrary covariate, independent of its block's coordinate type. -/
def adaptiveLowerAt (A : Learner X) (Z : Fin (m+1) → Block X) (a : ℝ)
    (ell : ℕ) (he : 1 ≤ ell ∧ ell ≤ m) (i : Fin (m+1)) (x : X) : ℝ :=
  OrderStatistics.stat (fun k : Fin m => pairPrediction A Z i (i.succAbove k) x -
    adaptiveRadius A Z a (i.succAbove k) i) (Setup.lowerIndex m ell he)

def adaptiveUpperAt (A : Learner X) (Z : Fin (m+1) → Block X) (a : ℝ)
    (ell : ℕ) (he : 1 ≤ ell ∧ ell ≤ m) (i : Fin (m+1)) (x : X) : ℝ :=
  OrderStatistics.stat (fun k : Fin m => pairPrediction A Z i (i.succAbove k) x +
    adaptiveRadius A Z a (i.succAbove k) i) (Setup.upperIndex m ell he)

lemma adaptiveLowerAt_relabel (A : Learner X) (Z : Fin (m+1) → Block X)
    (e : Equiv.Perm (Fin (m+1))) (a : ℝ) (ell : ℕ) (he : 1 ≤ ell ∧ ell ≤ m)
    (i : Fin (m+1)) (x : X) :
    adaptiveLowerAt A (relabel e Z) a ell he (e i) x = adaptiveLowerAt A Z a ell he i x := by
  unfold adaptiveLowerAt
  rw [← OrderStatistics.stat_perm _ (SetupEquivariance.otherPerm e i)]
  apply congrArg (fun u : Fin m → ℝ => OrderStatistics.stat u (Setup.lowerIndex m ell he))
  funext k
  simp only [Function.comp_apply, SetupEquivariance.otherPerm_spec]
  rw [adaptiveRadius_relabel, pairPrediction_relabel]

lemma adaptiveUpperAt_relabel (A : Learner X) (Z : Fin (m+1) → Block X)
    (e : Equiv.Perm (Fin (m+1))) (a : ℝ) (ell : ℕ) (he : 1 ≤ ell ∧ ell ≤ m)
    (i : Fin (m+1)) (x : X) :
    adaptiveUpperAt A (relabel e Z) a ell he (e i) x = adaptiveUpperAt A Z a ell he i x := by
  unfold adaptiveUpperAt
  rw [← OrderStatistics.stat_perm _ (SetupEquivariance.otherPerm e i)]
  apply congrArg (fun u : Fin m → ℝ => OrderStatistics.stat u (Setup.upperIndex m ell he))
  funext k
  simp only [Function.comp_apply, SetupEquivariance.otherPerm_spec]
  rw [adaptiveRadius_relabel, pairPrediction_relabel]

lemma adaptiveLowerAt_eq (A : Learner X) (Z : Fin (m+1) → Block X) (a : ℝ)
    (ht : finiteDomain Z a) (ell : ℕ) (he : 1 ≤ ell ∧ ell ≤ m)
    (i : Fin (m+1)) (j : Fin (size (Z i))) :
    adaptiveLowerAt A Z a ell he i ((Z i).2 j).1 =
      lowerEndpoint A Z (innerRank a Z) ht ell he i j := by
  unfold adaptiveLowerAt
  simp_rw [adaptiveRadius_eq A Z a ht]
  rfl

lemma adaptiveUpperAt_eq (A : Learner X) (Z : Fin (m+1) → Block X) (a : ℝ)
    (ht : finiteDomain Z a) (ell : ℕ) (he : 1 ≤ ell ∧ ell ≤ m)
    (i : Fin (m+1)) (j : Fin (size (Z i))) :
    adaptiveUpperAt A Z a ell he i ((Z i).2 j).1 =
      upperEndpoint A Z (innerRank a Z) ht ell he i j := by
  unfold adaptiveUpperAt
  simp_rw [adaptiveRadius_eq A Z a ht]
  rfl

/-- A total coverage predicate with both actual adaptive endpoint orders. -/
def adaptiveCoveredAt (A : Learner X) (Z : Fin (m+1) → Block X) (a : ℝ)
    (ell : ℕ) (he : 1 ≤ ell ∧ ell ≤ m) (i : Fin (m+1)) (x : X) (y : ℝ) : Prop :=
  adaptiveLowerAt A Z a ell he i x ≤ y ∧ y ≤ adaptiveUpperAt A Z a ell he i x

lemma adaptiveCoveredAt_relabel (A : Learner X) (Z : Fin (m+1) → Block X)
    (e : Equiv.Perm (Fin (m+1))) (a : ℝ) (ell : ℕ) (he : 1 ≤ ell ∧ ell ≤ m)
    (i : Fin (m+1)) (x : X) (y : ℝ) :
    adaptiveCoveredAt A (relabel e Z) a ell he (e i) x y ↔ adaptiveCoveredAt A Z a ell he i x y := by
  simp only [adaptiveCoveredAt, adaptiveLowerAt_relabel, adaptiveUpperAt_relabel]

/-- Coordinate misses as a function of one whole block. -/
def blockMissCount (lo hi : X → ℝ) (z : Block X) : ℕ :=
  (univ.filter fun j : Fin (size z) => ¬ (lo (z.2 j).1 ≤ (z.2 j).2 ∧
    (z.2 j).2 ≤ hi (z.2 j).1)).card

/-- Total failure event used only for proving covariance, with the source floors. -/
def adaptiveFailure (A : Learner X) (Z : Fin (m+1) → Block X) (alpha a : ℝ)
    (ell : ℕ) (he : 1 ≤ ell ∧ ell ≤ m) (i : Fin (m+1)) : Prop :=
  failureRank alpha Z i ≤ blockMissCount (adaptiveLowerAt A Z a ell he i)
    (adaptiveUpperAt A Z a ell he i) (Z i)

lemma adaptiveFailure_relabel (A : Learner X) (Z : Fin (m+1) → Block X)
    (e : Equiv.Perm (Fin (m+1))) (alpha a : ℝ) (ell : ℕ) (he : 1 ≤ ell ∧ ell ≤ m)
    (i : Fin (m+1)) :
    adaptiveFailure A (relabel e Z) alpha a ell he (e i) ↔ adaptiveFailure A Z alpha a ell he i := by
  have hZi : relabel e Z (e i) = Z i := by simp only [relabel, Function.comp_apply, Equiv.symm_apply_apply]
  have hl : adaptiveLowerAt A (relabel e Z) a ell he (e i) = adaptiveLowerAt A Z a ell he i :=
    funext fun x => adaptiveLowerAt_relabel A Z e a ell he i x
  have hu : adaptiveUpperAt A (relabel e Z) a ell he (e i) = adaptiveUpperAt A Z a ell he i :=
    funext fun x => adaptiveUpperAt_relabel A Z e a ell he i x
  simp only [adaptiveFailure, failureRank_relabel, hl, hu, hZi]

/-- On its stated domain, the total event is exactly the paper's original event. -/
lemma adaptiveFailure_iff (A : Learner X) (Z : Fin (m+1) → Block X) (alpha a : ℝ)
    (ht : finiteDomain Z a) (ell : ℕ) (he : 1 ≤ ell ∧ ell ≤ m) (i : Fin (m+1)) :
    adaptiveFailure A Z alpha a ell he i ↔
      learnerFailure A Z (failureRank alpha Z) (innerRank a Z) ht ell he i := by
  have hset : (univ.filter fun j : Fin (size (Z i)) =>
      ¬ adaptiveCoveredAt A Z a ell he i ((Z i).2 j).1 ((Z i).2 j).2) =
      (univ.filter fun j : Fin (size (Z i)) =>
        ¬ covered (fun k => size (Z k)) (learnerResponses Z) (learnerPredictions A Z)
          (innerRank a Z) ht ell he i j) := by
    ext j
    simp only [mem_filter, mem_univ, true_and, adaptiveCoveredAt]
    rw [adaptiveLowerAt_eq A Z a ht, adaptiveUpperAt_eq A Z a ht]
    rfl
  have hcard : blockMissCount (adaptiveLowerAt A Z a ell he i) (adaptiveUpperAt A Z a ell he i) (Z i) =
      (univ.filter fun j : Fin (size (Z i)) =>
        ¬ covered (fun k => size (Z k)) (learnerResponses Z) (learnerPredictions A Z)
          (innerRank a Z) ht ell he i j).card := by
    unfold blockMissCount
    apply congrArg Finset.card
    ext j
    simpa only [mem_filter, mem_univ, true_and, adaptiveCoveredAt] using (Finset.ext_iff.mp hset j)
  change _ ≤ _ ↔ _ ≤ _
  rw [hcard]

/-- The actual source event is the positive domain together with the equivalent
adaptive event. This is a derived equivalence, not a replacement of the event. -/
lemma finiteFailure_iff_domain_adaptive (A : Learner X) (Z : Fin (m+1) → Block X)
    (alpha a : ℝ) (ell : ℕ) (he : 1 ≤ ell ∧ ell ≤ m) (i : Fin (m+1)) :
    HeterogeneousProbability.finiteFailure A Z alpha a ell he i ↔
      finiteDomain Z a ∧ adaptiveFailure A Z alpha a ell he i := by
  constructor
  · rintro ⟨ht, hf⟩
    exact ⟨ht, (adaptiveFailure_iff A Z alpha a ht ell he i).mpr hf⟩
  · rintro ⟨ht, hf⟩
    exact ⟨ht, (adaptiveFailure_iff A Z alpha a ht ell he i).mp hf⟩

/-- Genuine covariance of the original heterogeneous failure predicate. -/
theorem finiteFailure_relabel (A : Learner X) (Z : Fin (m+1) → Block X)
    (e : Equiv.Perm (Fin (m+1))) (alpha a : ℝ) (ell : ℕ) (he : 1 ≤ ell ∧ ell ≤ m)
    (i : Fin (m+1)) :
    HeterogeneousProbability.finiteFailure A (relabel e Z) alpha a ell he (e i) ↔
      HeterogeneousProbability.finiteFailure A Z alpha a ell he i := by
  rw [finiteFailure_iff_domain_adaptive, finiteFailure_iff_domain_adaptive]
  exact and_congr (finiteDomain_relabel Z e a) (adaptiveFailure_relabel A Z e alpha a ell he i)

/-- The measurable original event family satisfies the exchangeability framework. -/
theorem finiteFailure_equivariant (A : Learner X) (alpha a : ℝ)
    (ell : ℕ) (he : 1 ≤ ell ∧ ell ≤ m) :
    Equivariant (fun Z : Fin (m+1) → Block X => fun i =>
      HeterogeneousProbability.finiteFailure A Z alpha a ell he i) :=
  fun e Z i => finiteFailure_relabel A Z e alpha a ell he i

/-- The actual sorted heterogeneous frontier is also invariant under labels. -/
theorem realizedFrontier_relabel (Z : Fin (m+1) → Block X)
    (e : Equiv.Perm (Fin (m+1))) (alpha a : ℝ) (ell : ℕ) :
    realizedFrontier alpha a ell (relabel e Z) = realizedFrontier alpha a ell Z :=
  realizedFrontier_eq_of_sizeMultiset_eq alpha a ell (relabel e Z) Z (sizeMultiset_relabel Z e)

end
end MEJF.HeterogeneousEquivariance
