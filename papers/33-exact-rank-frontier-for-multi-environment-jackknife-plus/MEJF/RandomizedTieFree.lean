import MEJF.RandomizedProbability
import MEJF.TieFreeSharpness

/-! A single tie-free common-rank extremizer, preserving every positive-mass
rank/label failure pair by the universal weighted optimum. -/
namespace MEJF.RandomizedTieFree
open Finset MeasureTheory Setup PredictionTable TournamentOptimization RandomizedProbability
noncomputable section
attribute [local instance] Classical.propDecidable

lemma stat_one_of_few_nonpositive {m ell : ℕ} (a : Fin m → ℝ)
    (he : 1 ≤ ell ∧ ell ≤ m) (hv : ∀ i, a i = 1 ∨ a i ≤ 0)
    (hc : OrderStatistics.count a (· ≤ 0) ≤ ell-1) :
    OrderStatistics.stat a (Setup.lowerIndex m ell he) = 1 := by
  have h := hv (Tuple.sort a (Setup.lowerIndex m ell he))
  change OrderStatistics.stat a (Setup.lowerIndex m ell he) = 1 ∨
    OrderStatistics.stat a (Setup.lowerIndex m ell he) ≤ 0 at h
  rcases h with h | h
  · exact h
  · have hh := (OrderStatistics.stat_le_iff_count a (Setup.lowerIndex m ell he) 0).mp h
    change ell-1 < _ at hh
    omega

/-- The common capacity table has a unit lower-side failure margin at every
rank whose threshold the vertex degree meets. -/
lemma lower_one_of_capacity {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    {m n t ell : ℕ} (R : Fin (m+1) → Fin (m+1) → Prop)
    (hasym : ∀ u v, R u v → ¬ R v u)
    (B : Fin (m+1) → Fin n → Fin (m+1) → Bool)
    (emb : Fin (m+1) × Fin n → X) (hinj : Function.Injective emb)
    (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m)
    (hmark : ∀ u v, R u v → t ≤ markedCount B u v)
    (hunmark : ∀ u v, ¬ R u v → markedCount B u v < t)
    (u : Fin (m+1)) (j : Fin n) (c : ℕ) (hc : c ≤ m)
    (hrow : (univ.filter fun k : Fin m => B u j (u.succAbove k) = false).card = m-c)
    (hd : m+1-ell ≤ c) :
    lowerEndpoint (tableLearner (incidenceTable R B) emb) (modelData emb) u j t ell ht he = 1 := by
  rw [model_lowerEndpoint_incidence R (fun {u v} => hasym u v) B emb hinj t ell ht he hmark hunmark]
  apply stat_one_of_few_nonpositive _ he
  · intro k
    cases hB : B u j (u.succAbove k)
    · exact Or.inr (incidenceLower_unmarked R B u (u.succAbove k) j hB)
    · exact Or.inl (incidenceLower_marked R B u (u.succAbove k) j hB)
  · have hcount : OrderStatistics.count
        (fun k : Fin m => incidenceLower R B u (u.succAbove k) j) (· ≤ 0) = m-c := by
      simpa only [OrderStatistics.count,incidenceLower_nonpositive_iff] using hrow
    rw [hcount]
    omega

/-- One perturbation removes every relevant tie and jointly realizes the exact
failure indicators for all ranks having positive probability. -/
theorem exists_supported_tieFree_model (m n F t : ℕ) (hF : 1 ≤ F) (hFn : F ≤ n)
    (ht : 1 ≤ t ∧ t ≤ F) (pi : RankLaw m) (eta : ℝ) (heta : 0 < eta) (heta' : eta < 1/4) :
    ∃ (T : Tour (m+1)) (A : Learner UniversalCovariate n)
      (Z : Fin (m+1) → Block UniversalCovariate n),
      objective F m t pi.mass T = maxObjective F m t pi.mass ∧
      (∀ (ell : ℕ) (he : 1 ≤ ell ∧ ell ≤ m),
        TieFreeSharpness.ActualTieFree A Z t ell ⟨ht.1,ht.2.trans hFn⟩ he) ∧
      (∀ (l : Fin m), 0 < pi.mass l → ∀ u,
        Setup.failure A Z u F t (l.val+1) ⟨ht.1,ht.2.trans hFn⟩ (rankValid l) ↔
          Incidence.threshold F m (m+1-(l.val+1)) t ≤ degree T u) := by
  classical
  obtain ⟨T,hT⟩ := maxObjective_attained F m t pi.mass
  let R := relation T
  have hasym := relation_asymm T
  let emb := unitEmbedding (m+1) n
  let htN : 1 ≤ t ∧ t ≤ n := ⟨ht.1,ht.2.trans hFn⟩
  obtain ⟨B,hmark,hunmark,hrow,hzero⟩ := RandomizedRanks.exists_capacity_array R hasym hFn ht.1 ht.2
  let p := incidenceTable R B
  obtain ⟨z,hz,htf,hpres⟩ := TieFreeTable.quantitative_tie_removal p (incidenceTable_ge_one R B) eta heta heta'
  let A := tableLearner (TieFreeSharpness.vectorPredictions z) emb
  let Z := TieFreeSharpness.vectorData emb z
  let oldH := fun (u : Fin (m+1)) (l : Fin m) =>
    Incidence.threshold F m (m+1-(l.val+1)) t ≤ degree T u
  let newH := fun (u : Fin (m+1)) (l : Fin m) =>
    Setup.failure A Z u F t (l.val+1) htN (rankValid l)
  have hzdeg (u : Fin (m+1)) : degree T u ≤ m := by
    rw [degree,←Sharpness.marked_card_eq_degree R hasym u]
    simpa using card_le_univ (univ.filter fun k : Fin m => R u (u.succAbove k))
  have holdpres : ∀ u l, oldH u l → newH u l := by
    intro u l hold
    have hc := (RandomizedRanks.capacityAt_bounds F m t (degree T u) ht.1 ht.2 (hzdeg u)).2.1
    have hcap := (RandomizedRanks.capacityAt_iff_threshold F m t (degree T u)
      (m+1-(l.val+1)) ht.1 ht.2 (hzdeg u) (by omega)).mpr hold
    have hlow : ∀ j : Fin n, j.val < F →
        TieFreeTable.aggregate (TieFreeTable.baseline p) false u j (innerIndex n t htN)
          (lowerIndex m (l.val+1) (rankValid l)) = 1 := by
      intro j hj
      rw [←TieFreeSharpness.vector_lowerEndpoint emb emb.injective (TieFreeTable.baseline p)
        t (l.val+1) htN (rankValid l) u j]
      change lowerEndpoint (tableLearner p emb) (modelData emb) u j t (l.val+1) htN (rankValid l) = 1
      exact lower_one_of_capacity R hasym B emb emb.injective htN (rankValid l) hmark hunmark u j
        (RandomizedRanks.capacityAt F m t (degree T u)) hc (hrow u j hj) hcap
    have hs : Sharpness.firstRows F n ⊆ univ.filter (fun j => ¬ Setup.covered A Z u j t (l.val+1) htN (rankValid l)) := by
      intro j hj
      have hjF : j.val < F := by simpa [Sharpness.firstRows] using hj
      have hmargin : TieFreeTable.response u j (TieFreeTable.baseline p)+1 ≤
          TieFreeTable.aggregate (TieFreeTable.baseline p) false u j (innerIndex n t htN)
            (lowerIndex m (l.val+1) (rankValid l)) := by
        rw [hlow j hjF]
        norm_num [TieFreeTable.response,TieFreeTable.baseline]
      have hstrict := hpres u j (innerIndex n t htN) (lowerIndex m (l.val+1) (rankValid l)) hmargin
      rw [←TieFreeSharpness.vector_lowerEndpoint emb emb.injective z t (l.val+1) htN (rankValid l) u j] at hstrict
      simp only [mem_filter,mem_univ,true_and]
      intro hcov
      exact (not_le_of_gt hstrict) hcov.1
    have hcard := card_mono hs
    rw [Sharpness.firstRows_card hFn] at hcard
    exact hcard
  let f := fun u l => if oldH u l then pi.mass l else 0
  let g := fun u l => if newH u l then pi.mass l else 0
  have hfg : ∀ u l, f u l ≤ g u l := by
    intro u l
    dsimp [f,g]
    by_cases ho : oldH u l
    · simp only [if_pos ho,if_pos (holdpres u l ho),le_refl]
    · by_cases hn : newH u l
      · simpa only [if_neg ho,if_pos hn] using pi.nonneg l
      · simp only [if_neg ho,if_neg hn,le_refl]
  have hbase : (∑ u,∑ l,f u l) = maxObjective F m t pi.mass := by
    change objective F m t pi.mass T = _
    exact hT
  have hupper : (∑ u,∑ l,g u l) ≤ maxObjective F m t pi.mass :=
    pointwise_weighted_count_le A Z htN ht.2 pi.mass pi.nonneg
  have hsum : (∑ u,∑ l,f u l) = ∑ u,∑ l,g u l := by
    apply le_antisymm (sum_le_sum (fun u _ => sum_le_sum (fun l _ => hfg u l)))
    rw [hbase]
    exact hupper
  have hterms : ∀ u l, f u l = g u l := by
    intro u l
    have hu := (Finset.sum_eq_sum_iff_of_le
      (fun u (_ : u ∈ (univ : Finset (Fin (m+1)))) => sum_le_sum (fun l _ => hfg u l))).mp hsum u (mem_univ u)
    exact (Finset.sum_eq_sum_iff_of_le (fun l _ => hfg u l)).mp hu l (mem_univ l)
  refine ⟨T,A,Z,hT,?_,?_⟩
  · intro ell he
    exact TieFreeSharpness.actualTieFree_of_table emb emb.injective z htf t ell htN he
  · intro l hpi u
    constructor
    · intro hn
      by_contra ho
      have heq := hterms u l
      dsimp [f,g,oldH,newH] at heq
      simp only [if_neg ho,if_pos hn] at heq
      linarith
    · exact holdpres u l

/-- The common-rank law can be attained by a finite exchangeable model that is
almost surely free of all the relevant ties, jointly for every positive rank. -/
theorem exists_tieFree_attaining_law (m n F t : ℕ) (hF : 1 ≤ F) (hFn : F ≤ n)
    (ht : 1 ≤ t ∧ t ≤ F) (pi : RankLaw m) (eta : ℝ) (heta : 0 < eta) (heta' : eta < 1/4) :
    ∃ (A : Learner UniversalCovariate n) (Z : Fin (m+1) → Block UniversalCovariate n),
      (∀ᵐ W ∂FiniteExchangeable.blockPermutationLaw Z, ∀ l : Fin m,
        TieFreeSharpness.ActualTieFree A W t (l.val+1) ⟨ht.1,ht.2.trans hFn⟩ (rankValid l)) ∧
      weightedProbability pi.mass A (FiniteExchangeable.blockPermutationLaw Z) F t
        ⟨ht.1,ht.2.trans hFn⟩ (Fin.last m) = maxObjective F m t pi.mass/(m+1 : ℕ) := by
  obtain ⟨T,A,Z,hT,htf,hfail⟩ := exists_supported_tieFree_model m n F t hF hFn ht pi eta heta heta'
  refine ⟨A,Z,?_,?_⟩
  · apply ae_all_iff.mpr
    intro l
    exact TieFreeSharpness.actualTieFree_ae_permutationLaw (htf (l.val+1) (rankValid l))
  · rw [orbit_weighted_probability]
    have heq : (∑ u : Fin (m+1),∑ l : Fin m,
        if Setup.failure A Z u F t (l.val+1) ⟨ht.1,ht.2.trans hFn⟩ (rankValid l) then pi.mass l else 0) =
        objective F m t pi.mass T := by
      apply sum_congr rfl
      intro u _
      unfold RandomizedRanks.payoff
      apply sum_congr rfl
      intro l _
      by_cases hz : pi.mass l=0
      · simp only [hz,ite_self]
      · have hp : 0 < pi.mass l := lt_of_le_of_ne (pi.nonneg l) (Ne.symm hz)
        rw [hfail l hp u]
        split_ifs <;> rfl
    rw [heq,hT]

end
end MEJF.RandomizedTieFree
