import MEJF.Sharpness

/-! Simultaneous actual lower construction for the hidden global outer rank. -/
namespace MEJF.RandomizedRanks
open Finset Incidence Sharpness
noncomputable section
attribute [local instance] Classical.propDecidable

/-- The common per-vertex row degree in equation (6.23). -/
def capacityAt (F m t z : ℕ) : ℕ := (m*(t-1)+z*(F-t+1))/F

lemma capacityAt_bounds (F m t z : ℕ) (ht : 1 ≤ t) (htF : t ≤ F) (hz : z ≤ m) :
    z ≤ capacityAt F m t z ∧ capacityAt F m t z ≤ m ∧
      z*t ≤ F*capacityAt F m t z ∧
      F*capacityAt F m t z ≤ z*F+(m-z)*(t-1) := by
  have hF : 0 < F := by omega
  have hFt : F = (t-1)+(F-t+1) := by omega
  have hmz : m = z+(m-z) := by omega
  have hlo : z*F ≤ m*(t-1)+z*(F-t+1) := by nlinarith
  have hzcap : z ≤ capacityAt F m t z := (Nat.le_div_iff_mul_le hF).2 hlo
  have hnum : m*(t-1)+z*(F-t+1) < (m+1)*F := by nlinarith
  have hcm : capacityAt F m t z ≤ m := by
    have := (Nat.div_lt_iff_lt_mul hF).2 hnum
    dsimp [capacityAt]
    omega
  have hupper := Nat.div_mul_le_self (m*(t-1)+z*(F-t+1)) F
  change capacityAt F m t z * F ≤ m*(t-1)+z*(F-t+1) at hupper
  refine ⟨hzcap, hcm, ?_, ?_⟩ <;> nlinarith

/-- The row-capacity test is exactly the rank-specific outdegree test (6.25). -/
lemma capacityAt_iff_threshold (F m t z d : ℕ) (ht : 1 ≤ t) (htF : t ≤ F)
    (hz : z ≤ m) (hd : d ≤ m) :
    d ≤ capacityAt F m t z ↔ threshold F m d t ≤ z := by
  have hF : 0 < F := by omega
  have hD : 0 < F-t+1 := by omega
  have hFt : F = (t-1)+(F-t+1) := by omega
  have hmz : m = z+(m-z) := by omega
  have hmd : m = d+(m-d) := by omega
  constructor
  · intro h
    have hc := (capacityAt_bounds F m t z ht htF hz).2.2.2
    apply degree_threshold_of_capacity F m d t z ht htF hd hz
    nlinarith
  · intro h
    have hq : m-z ≤ F*(m-d)/(F-t+1) := by
      dsimp [threshold] at h
      have := min_le_right m (F*(m-d)/(F-t+1))
      omega
    have hmul := (Nat.le_div_iff_mul_le hD).1 hq
    apply (Nat.le_div_iff_mul_le hF).2
    nlinarith

/-- Simultaneous incidence construction for every vertex of an actual oriented
graph. The statement is stronger than the tournament-only lower construction. -/
theorem exists_capacity_array {m n F t : ℕ} (R : Fin (m+1) → Fin (m+1) → Prop)
    (hasym : ∀ u v, R u v → ¬ R v u) (hFn : F ≤ n) (ht : 1 ≤ t) (htF : t ≤ F) :
    ∃ B : Fin (m+1) → Fin n → Fin (m+1) → Bool,
      (∀ u v, R u v → t ≤ PredictionTable.markedCount B u v) ∧
      (∀ u v, ¬ R u v → PredictionTable.markedCount B u v < t) ∧
      (∀ u (j : Fin n), j.val < F →
        (univ.filter fun k : Fin m => B u j (u.succAbove k) = false).card =
          m-capacityAt F m t (ExtremalGraph.outdegree R u)) ∧
      (∀ u (j : Fin n), F ≤ j.val → ∀ k : Fin m, B u j (u.succAbove k) = false) := by
  classical
  let z := fun u => ExtremalGraph.outdegree R u
  have hz : ∀ u, z u ≤ m := by
    intro u
    change ExtremalGraph.outdegree R u ≤ m
    rw [← marked_card_eq_degree R hasym u]
    simpa using (card_le_univ (univ.filter fun k : Fin m => R u (u.succAbove k)))
  have hmats : ∀ u : Fin (m+1), ∃ M : Fin F → Fin m → Prop,
      (∀ r, rowSum M r = capacityAt F m t (z u)) ∧
      (∀ k, R u (u.succAbove k) → t ≤ colSum M k) ∧
      (∀ k, ¬ R u (u.succAbove k) → colSum M k ≤ t-1) := by
    intro u
    let marked : Finset (Fin m) := univ.filter fun k => R u (u.succAbove k)
    have hmcard : marked.card = z u := marked_card_eq_degree R hasym u
    have hb := capacityAt_bounds F m t (z u) ht htF (hz u)
    obtain ⟨M, hr, hm, hn⟩ := realize_marked_columns F (capacityAt F m t (z u)) t
      marked ht htF (by simpa [hmcard] using hb.2.2.1)
      (by simpa [hmcard] using hb.2.2.2)
    exact ⟨M, hr, fun k hk => hm k (by simp [marked, hk]),
      fun k hk => hn k (by simp [marked, hk])⟩
  choose A hA using hmats
  refine ⟨typeBits A, ?_, ?_, ?_, ?_⟩
  · intro u v huv
    have hvu : v ≠ u := by intro h; subst v; exact hasym u u huv huv
    obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hvu
    rw [typeBits_column hFn]
    exact (hA u).2.1 k huv
  · intro u v huv
    by_cases hvu : v = u
    · subst v; simp [PredictionTable.markedCount]; omega
    · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hvu
      rw [typeBits_column hFn]
      have := (hA u).2.2 k huv
      omega
  · intro u j hj
    have htrue : (univ.filter fun k : Fin m => typeBits A u j (u.succAbove k) = true).card =
        capacityAt F m t (z u) := by
      simpa [typeBits_other, extendRows, hj, rowSum] using (hA u).1 ⟨j.val, hj⟩
    have hpart := filter_card_add_filter_neg_card_eq_card (s := (univ : Finset (Fin m)))
      (p := fun k => typeBits A u j (u.succAbove k) = true)
    simp only [Bool.not_eq_true, card_univ, Fintype.card_fin] at hpart
    dsimp [z] at htrue
    omega
  · intro u j hj k
    exact typeBits_zero_row A u j (by omega) k

/-- A common row capacity gives the exact failure test at every positive outer
rank; all quantities here are the actual fitted model endpoints. -/
lemma model_failure_iff_capacity {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    {m n F t ell : ℕ} (R : Fin (m+1) → Fin (m+1) → Prop)
    (hasym : ∀ u v, R u v → ¬ R v u)
    (B : Fin (m+1) → Fin n → Fin (m+1) → Bool)
    (emb : Fin (m+1) × Fin n → X) (hinj : Function.Injective emb)
    (hF : 1 ≤ F) (hFn : F ≤ n) (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m)
    (hmarked : ∀ u v, R u v → t ≤ PredictionTable.markedCount B u v)
    (hunmarked : ∀ u v, ¬ R u v → PredictionTable.markedCount B u v < t)
    (u : Fin (m+1)) (c : ℕ) (hc : c ≤ m)
    (hrow : ∀ (j : Fin n), j.val < F →
      (univ.filter fun k : Fin m => B u j (u.succAbove k) = false).card = m-c)
    (hzero : ∀ (j : Fin n), F ≤ j.val → ∀ k : Fin m, B u j (u.succAbove k) = false) :
    Setup.failure (PredictionTable.tableLearner (PredictionTable.incidenceTable R B) emb)
      (PredictionTable.modelData emb) u F t ell ht he ↔ m+1-ell ≤ c := by
  classical
  let A := PredictionTable.tableLearner (PredictionTable.incidenceTable R B) emb
  let Z := PredictionTable.modelData emb
  have hactive : ∀ (j : Fin n), j.val < F →
      (Setup.covered A Z u j t ell ht he ↔ c < m+1-ell) := by
    intro j hj
    simp only [A, Z, Setup.covered, PredictionTable.modelData, Set.mem_Icc]
    rw [PredictionTable.model_lowerEndpoint_incidence R (fun {u v} => hasym u v) B emb hinj
        t ell ht he hmarked hunmarked,
      PredictionTable.model_upperEndpoint_incidence R (fun {u v} => hasym u v) B emb hinj
        t ell ht he hmarked hunmarked]
    have hupper : 0 ≤ OrderStatistics.stat
        (fun k : Fin m => PredictionTable.incidenceUpper R B u (u.succAbove k) j)
        (Setup.upperIndex m ell he) := by
      apply OrderStatistics.min_le_stat
      intro k
      exact le_of_lt (PredictionTable.incidenceUpper_pos R B u (u.succAbove k) j)
    have hcount : OrderStatistics.count
        (fun k : Fin m => PredictionTable.incidenceLower R B u (u.succAbove k) j)
        (· ≤ 0) = m-c := by
      simpa only [OrderStatistics.count, PredictionTable.incidenceLower_nonpositive_iff] using hrow j hj
    have hlow : (OrderStatistics.stat
        (fun k : Fin m => PredictionTable.incidenceLower R B u (u.succAbove k) j)
        (Setup.lowerIndex m ell he) ≤ 0) ↔ c < m+1-ell := by
      rw [OrderStatistics.stat_le_iff_count, hcount]
      change ell-1 < m-c ↔ c < m+1-ell
      omega
    exact (and_iff_left hupper).trans hlow
  have hinactive : ∀ (j : Fin n), F ≤ j.val → Setup.covered A Z u j t ell ht he := by
    intro j hj
    simp only [A, Z, Setup.covered, PredictionTable.modelData, Set.mem_Icc]
    rw [PredictionTable.model_lowerEndpoint_incidence R (fun {u v} => hasym u v) B emb hinj
        t ell ht he hmarked hunmarked,
      PredictionTable.model_upperEndpoint_incidence R (fun {u v} => hasym u v) B emb hinj
        t ell ht he hmarked hunmarked]
    exact PredictionTable.incidence_zero_coordinate_covered R B u j u.succAbove (hzero j hj)
      (Setup.lowerIndex m ell he) (Setup.upperIndex m ell he)
  have hset : (univ.filter fun j => ¬ Setup.covered A Z u j t ell ht he) =
      if m+1-ell ≤ c then firstRows F n else ∅ := by
    ext j
    simp only [mem_filter, mem_univ, true_and]
    by_cases hdc : m+1-ell ≤ c
    · simp only [if_pos hdc, firstRows, mem_filter, mem_univ, true_and]
      by_cases hj : j.val < F
      · rw [hactive j hj]
        omega
      · have hcov := hinactive j (by omega)
        simp [hcov, hj]
    · simp only [if_neg hdc, notMem_empty, iff_false, not_not]
      by_cases hj : j.val < F
      · exact (hactive j hj).mpr (by omega)
      · exact hinactive j (by omega)
  change F ≤ (univ.filter fun j => ¬ Setup.covered A Z u j t ell ht he).card ↔ m+1-ell ≤ c
  rw [hset]
  by_cases hdc : m+1-ell ≤ c
  · simp [hdc, firstRows_card hFn]
  · simp [hdc]
    omega

/-- One admissible learner simultaneously realizes every outer rank's degree
threshold, independently of any distribution placed on those ranks. -/
theorem exists_joint_rank_model {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    {m n F t : ℕ} (R : Fin (m+1) → Fin (m+1) → Prop)
    (hasym : ∀ u v, R u v → ¬ R v u) (hF : 1 ≤ F) (hFn : F ≤ n)
    (ht : 1 ≤ t ∧ t ≤ F) (emb : Fin (m+1) × Fin n → X) (hinj : Function.Injective emb) :
    ∃ (A : Setup.Learner X n) (Z : Fin (m+1) → Setup.Block X n),
      ∀ (ell : ℕ) (he : 1 ≤ ell ∧ ell ≤ m) (u : Fin (m+1)),
        Setup.failure A Z u F t ell ⟨ht.1, ht.2.trans hFn⟩ he ↔
          threshold F m (m+1-ell) t ≤ ExtremalGraph.outdegree R u := by
  classical
  obtain ⟨B, hmark, hunmark, hrow, hzero⟩ := exists_capacity_array R hasym hFn ht.1 ht.2
  refine ⟨PredictionTable.tableLearner (PredictionTable.incidenceTable R B) emb,
    PredictionTable.modelData emb, ?_⟩
  intro ell he u
  have hz : ExtremalGraph.outdegree R u ≤ m := by
    rw [← marked_card_eq_degree R hasym u]
    simpa using (card_le_univ (univ.filter fun k : Fin m => R u (u.succAbove k)))
  have hc := (capacityAt_bounds F m t (ExtremalGraph.outdegree R u) ht.1 ht.2 hz).2.1
  exact (model_failure_iff_capacity R hasym B emb hinj hF hFn ⟨ht.1, ht.2.trans hFn⟩ he
    hmark hunmark u (capacityAt F m t (ExtremalGraph.outdegree R u)) hc (hrow u) (hzero u)).trans
      (capacityAt_iff_threshold F m t (ExtremalGraph.outdegree R u) (m+1-ell) ht.1 ht.2 hz (by omega))

/-- The rank payoff in (6.20), using zero-based `Fin m` to index ranks `1,...,m`. -/
def payoff (F m t : ℕ) (pi : Fin m → ℝ) (z : ℕ) : ℝ :=
  ∑ l : Fin m, if threshold F m (m+1-(l.val+1)) t ≤ z then pi l else 0

/-- The same learner attains every weighted global-rank objective. The learner
is chosen before `pi`, so in particular it cannot inspect the realized rank. -/
theorem exists_joint_payoff_model {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    {m n F t : ℕ} (R : Fin (m+1) → Fin (m+1) → Prop)
    (hasym : ∀ u v, R u v → ¬ R v u) (hF : 1 ≤ F) (hFn : F ≤ n)
    (ht : 1 ≤ t ∧ t ≤ F) (emb : Fin (m+1) × Fin n → X) (hinj : Function.Injective emb) :
    ∃ (A : Setup.Learner X n) (Z : Fin (m+1) → Setup.Block X n),
      ∀ pi : Fin m → ℝ,
        (∑ u : Fin (m+1), ∑ l : Fin m,
          if Setup.failure A Z u F t (l.val+1) ⟨ht.1, ht.2.trans hFn⟩ (by omega)
          then pi l else 0) =
        ∑ u : Fin (m+1), payoff F m t pi (ExtremalGraph.outdegree R u) := by
  classical
  obtain ⟨A, Z, hfail⟩ := exists_joint_rank_model R hasym hF hFn ht emb hinj
  refine ⟨A, Z, fun pi => ?_⟩
  apply sum_congr rfl
  intro u _
  unfold payoff
  apply sum_congr rfl
  intro l _
  rw [hfail (l.val+1) (by omega) u]
  by_cases hdeg : threshold F m (m+1-(l.val+1)) t ≤ ExtremalGraph.outdegree R u <;> simp [hdeg]

/-- Adding outgoing comparisons can only increase the nonnegative rank payoff. -/
theorem payoff_mono (F m t : ℕ) (pi : Fin m → ℝ) (hpi : ∀ l, 0 ≤ pi l) :
    Monotone (payoff F m t pi) := by
  intro x y hxy
  unfold payoff
  apply sum_le_sum
  intro l _
  by_cases hx : threshold F m (m+1-(l.val+1)) t ≤ x
  · have hy := hx.trans hxy
    simp only [if_pos hx, if_pos hy, le_refl]
  · by_cases hy : threshold F m (m+1-(l.val+1)) t ≤ y
    · simpa only [if_neg hx, if_pos hy] using hpi l
    · simp only [if_neg hx, if_neg hy, le_refl]

/-- Rankwise degree bounds combine under one global rank law. -/
theorem weighted_bound_of_failure_forces {m F t : ℕ}
    (H : Fin m → Fin (m+1) → Prop) (z : Fin (m+1) → ℕ)
    (pi : Fin m → ℝ) (hpi : ∀ l, 0 ≤ pi l)
    (hforce : ∀ l u, H l u → threshold F m (m+1-(l.val+1)) t ≤ z u) :
    (∑ u : Fin (m+1), ∑ l : Fin m, if H l u then pi l else 0) ≤
      ∑ u : Fin (m+1), payoff F m t pi (z u) := by
  classical
  apply sum_le_sum
  intro u _
  unfold payoff
  apply sum_le_sum
  intro l _
  by_cases hH : H l u
  · have hz := hforce l u hH
    simp only [if_pos hH, if_pos hz, le_refl]
  · by_cases hz : threshold F m (m+1-(l.val+1)) t ≤ z u
    · simpa only [if_neg hH, if_pos hz] using hpi l
    · simp only [if_neg hH, if_neg hz, le_refl]

end
end MEJF.RandomizedRanks
