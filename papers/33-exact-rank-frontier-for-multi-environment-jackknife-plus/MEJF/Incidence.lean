import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.SplitIfs

/-! Finite binary-incidence counting and equal-row-sum realization. -/
namespace MEJF.Incidence

open Finset

/-- The number of incidences in one row of a finite binary matrix. -/
noncomputable def rowSum {R C : Type*} [Fintype C] (B : R → C → Prop) (r : R) : ℕ := by
  classical
  exact ∑ c, if B r c then 1 else 0

/-- The number of incidences in one column. -/
noncomputable def colSum {R C : Type*} [Fintype R] (B : R → C → Prop) (c : C) : ℕ := by
  classical
  exact ∑ r, if B r c then 1 else 0

theorem total_incidence {R C : Type*} [Fintype R] [Fintype C] (B : R → C → Prop) :
    (∑ r, rowSum B r) = ∑ c, colSum B c := by
  classical
  exact Finset.sum_comm

theorem colSum_le {R C : Type*} [Fintype R] (B : R → C → Prop) (c : C) :
    colSum B c ≤ Fintype.card R := by
  classical
  calc
    colSum B c ≤ ∑ _ : R, 1 := Finset.sum_le_sum (fun _ _ => by split_ifs <;> omega)
    _ = _ := by simp

/-- Allocate an integer total among finitely many bounded capacities. -/
theorem allocate_capacity {C : Type*} [DecidableEq C] (s : Finset C) (u : C → ℕ)
    (q : ℕ) (hq : q ≤ ∑ j ∈ s, u j) :
    ∃ a : C → ℕ, (∀ j, a j ≤ u j) ∧ ∑ j ∈ s, a j = q := by
  classical
  induction s using Finset.induction_on generalizing q with
  | empty =>
      have : q = 0 := by simpa using hq
      exact ⟨fun _ => 0, fun _ => Nat.zero_le _, by simp [this]⟩
  | @insert j s hjs ih =>
      have hrest : q - min q (u j) ≤ ∑ k ∈ s, u k := by
        simp only [sum_insert hjs] at hq
        omega
      obtain ⟨a, ha, hsum⟩ := ih _ hrest
      refine ⟨Function.update a j (min q (u j)), ?_, ?_⟩
      · intro k
        by_cases hk : k = j
        · subst k; simp
        · simpa [Function.update_of_ne hk] using ha k
      · rw [sum_insert hjs]
        simp only [Function.update_self]
        have hsame : ∑ k ∈ s, Function.update a j (min q (u j)) k = ∑ k ∈ s, a k := by
          apply sum_congr rfl
          intro k hk
          exact Function.update_of_ne (ne_of_mem_of_not_mem hk hjs) _ _
        rw [hsame, hsum]
        omega

/-- The incidence bound underlying Lemma 4.2, for any specified set of outgoing
columns. Columns that reach threshold `t` must be in that set. -/
theorem incidence_capacity {R C : Type*} [Fintype R] [Fintype C] [DecidableEq C]
    (B : R → C → Prop) (out : Finset C) (d t : ℕ)
    (hrow : ∀ r, d ≤ rowSum B r)
    (hforce : ∀ c, t ≤ colSum B c → c ∈ out) :
    Fintype.card R * d ≤
      out.card * Fintype.card R + (Fintype.card C - out.card) * (t - 1) := by
  classical
  have htotal : Fintype.card R * d ≤ ∑ c, colSum B c := by
    calc
      Fintype.card R * d = ∑ _ : R, d := by simp
      _ ≤ ∑ r, rowSum B r := sum_le_sum (fun r _ => hrow r)
      _ = _ := total_incidence B
  have hcol : ∀ c, colSum B c ≤ if c ∈ out then Fintype.card R else t - 1 := by
    intro c
    split_ifs with hc
    · exact colSum_le B c
    · have : ¬ t ≤ colSum B c := fun h => hc (hforce c h)
      omega
  have hsum := sum_le_sum (s := (univ : Finset C)) (fun c _ => hcol c)
  have hid : (∑ c : C, if c ∈ out then Fintype.card R else t - 1) =
      out.card * Fintype.card R + (Fintype.card C - out.card) * (t - 1) := by
    rw [sum_ite]
    simp [filter_notMem_eq_sdiff, card_sdiff]
  rw [hid] at hsum
  exact htotal.trans hsum

/-- Rewrite the incidence bound into the floor formula for the least required
number of outgoing columns. Here `m-d = ell-1` in the paper's notation. -/
theorem degree_threshold_of_capacity (F m d t z : ℕ) (ht : 1 ≤ t) (htF : t ≤ F)
    (hd : d ≤ m) (hz : z ≤ m)
    (hcap : F * d ≤ z * F + (m-z) * (t-1)) :
    m - min m (F * (m-d) / (F-t+1)) ≤ z := by
  have hD : 0 < F-t+1 := by omega
  have hproduct : (m-z) * (F-t+1) ≤ F * (m-d) := by
    have hFt : F = (t-1) + (F-t+1) := by omega
    have hmz : m = z + (m-z) := by omega
    have hmd : m = d + (m-d) := by omega
    nlinarith
  have hdiv : m-z ≤ F * (m-d) / (F-t+1) := (Nat.le_div_iff_mul_le hD).2 hproduct
  omega

/-- Given natural column degrees bounded by the number of rows, the only additional
condition for a binary matrix with all row sums equal is equality of the total. -/
theorem realize_column_degrees {C : Type*} [Fintype C] [DecidableEq C]
    (F d : ℕ) (c : C → ℕ) (hc : ∀ j, c j ≤ F)
    (htotal : ∑ j, c j = F * d) :
    ∃ B : Fin F → C → Prop,
      (∀ r, rowSum B r = d) ∧ (∀ j, colSum B j = c j) := by
  classical
  induction F generalizing c with
  | zero =>
      refine ⟨fun r => Fin.elim0 r, ?_, ?_⟩
      · intro r; exact Fin.elim0 r
      · intro j; have := hc j; simp [colSum]; omega
  | succ F ih =>
      let full : Finset C := univ.filter (fun j => c j = F + 1)
      let pos : Finset C := univ.filter (fun j => 0 < c j)
      have hfp : full ⊆ pos := by
        intro j hj
        simp only [full, pos, mem_filter, mem_univ, true_and] at hj ⊢
        omega
      have hfull : full.card ≤ d := by
        have hsum : ∑ j : C, (if j ∈ full then F + 1 else 0) ≤ ∑ j, c j := by
          apply sum_le_sum
          intro j _
          split_ifs with hj
          · have : c j = F + 1 := by simpa [full] using hj
            omega
          · exact Nat.zero_le _
        have hid : (∑ j : C, (if j ∈ full then F + 1 else 0)) = full.card * (F + 1) := by
          rw [← sum_filter]
          simp
        rw [hid, htotal] at hsum
        nlinarith
      have hpos : d ≤ pos.card := by
        have hsum : ∑ j : C, c j ≤ ∑ j : C, (if j ∈ pos then F + 1 else 0) := by
          apply sum_le_sum
          intro j _
          split_ifs with hj
          · exact hc j
          · have hzero : c j = 0 := by simpa [pos] using hj
            simp [hzero]
        have hid : (∑ j : C, (if j ∈ pos then F + 1 else 0)) = pos.card * (F + 1) := by
          rw [← sum_filter]
          simp
        rw [hid, htotal] at hsum
        nlinarith
      obtain ⟨s, hfs, hsp, hs⟩ := exists_subsuperset_card_eq hfp hfull hpos
      let c' : C → ℕ := fun j => c j - if j ∈ s then 1 else 0
      have hc' : ∀ j, c' j ≤ F := by
        intro j
        dsimp [c']
        split_ifs with hj
        · have hposj := hsp hj
          have : 0 < c j := by simpa [pos] using hposj
          have := hc j
          omega
        · have hnotfull : j ∉ full := fun h => hj (hfs h)
          have : c j ≠ F + 1 := by simpa [full] using hnotfull
          have := hc j
          omega
      have htotal' : ∑ j, c' j = F * d := by
        have hsub : ∀ j ∈ (univ : Finset C), (if j ∈ s then 1 else 0) ≤ c j := by
          intro j _
          split_ifs with hj
          · have := hsp hj
            have : 0 < c j := by simpa [pos] using this
            omega
          · exact Nat.zero_le _
        have hind : (∑ j : C, (if j ∈ s then 1 else 0)) = d := by
          rw [← sum_filter]
          simpa using hs
        dsimp [c']
        rw [Finset.sum_tsub_distrib univ hsub, htotal, hind]
        simp only [Nat.add_mul, one_mul]
        omega
      obtain ⟨B, hrow, hcol⟩ := ih c' hc' htotal'
      refine ⟨Fin.cases (fun j => j ∈ s) B, ?_, ?_⟩
      · intro r
        refine Fin.cases ?_ (fun r => ?_) r
        · unfold rowSum
          have heq : (∑ j : C, if Fin.cases (fun j => j ∈ s) B (0 : Fin (F+1)) j then 1 else 0) =
              ∑ j : C, if j ∈ s then 1 else 0 := by
            apply sum_congr rfl
            intro j _
            by_cases hj : j ∈ s <;> simp [hj]
          rw [heq, ← sum_filter]
          simpa using hs
        · simpa [rowSum] using hrow r
      · intro j
        have hdec : colSum (Fin.cases (fun j => j ∈ s) B) j =
            (if j ∈ s then 1 else 0) + colSum B j := by
          unfold colSum
          rw [Fin.sum_univ_succ]
          by_cases hj : j ∈ s
          · simp only [Fin.cases_zero, Fin.cases_succ, if_pos hj]
          · simp only [Fin.cases_zero, Fin.cases_succ, if_neg hj]
        rw [hdec, hcol]
        dsimp [c']
        split_ifs with hj
        · have := hsp hj
          have : 0 < c j := by simpa [pos] using this
          omega
        · omega

/-- Column interval capacities suffice for an equal-row-sum binary matrix. -/
theorem realize_column_intervals {C : Type*} [Fintype C] [DecidableEq C]
    (F d : ℕ) (lo hi : C → ℕ) (hlo : ∀ j, lo j ≤ hi j)
    (hhi : ∀ j, hi j ≤ F) (hlow : ∑ j, lo j ≤ F*d)
    (hupp : F*d ≤ ∑ j, hi j) :
    ∃ B : Fin F → C → Prop, (∀ r, rowSum B r = d) ∧
      (∀ j, lo j ≤ colSum B j ∧ colSum B j ≤ hi j) := by
  classical
  have hsumsub : (∑ j, (hi j - lo j)) = (∑ j, hi j) - ∑ j, lo j :=
    sum_tsub_distrib univ (fun j _ => hlo j)
  have hroom : F*d - (∑ j, lo j) ≤ ∑ j, (hi j - lo j) := by
    rw [hsumsub]
    omega
  obtain ⟨a, ha, hsum⟩ := allocate_capacity univ (fun j => hi j - lo j) _ hroom
  let c : C → ℕ := fun j => lo j + a j
  have hc : ∀ j, c j ≤ F := by
    intro j
    have := ha j
    have := hlo j
    have := hhi j
    dsimp [c]
    omega
  have htotal : ∑ j, c j = F*d := by
    dsimp [c]
    rw [sum_add_distrib, hsum]
    omega
  obtain ⟨B, hrow, hcol⟩ := realize_column_degrees F d c hc htotal
  refine ⟨B, hrow, fun j => ?_⟩
  rw [hcol]
  have := ha j
  have := hlo j
  dsimp [c]
  omega

/-- Incidence realization under exactly the two capacity inequalities in the
proof of Lemma 5.2. The marked columns may be any specified finite subset. -/
theorem realize_marked_columns {C : Type*} [Fintype C] [DecidableEq C]
    (F d t : ℕ) (marked : Finset C) (ht : 1 ≤ t) (htF : t ≤ F)
    (hlow : marked.card*t ≤ F*d)
    (hupp : F*d ≤ marked.card*F + (Fintype.card C-marked.card)*(t-1)) :
    ∃ B : Fin F → C → Prop, (∀ r, rowSum B r = d) ∧
      (∀ j ∈ marked, t ≤ colSum B j) ∧
      (∀ j ∉ marked, colSum B j ≤ t-1) := by
  classical
  let lo : C → ℕ := fun j => if j ∈ marked then t else 0
  let hi : C → ℕ := fun j => if j ∈ marked then F else t-1
  have hlh : ∀ j, lo j ≤ hi j := by
    intro j; dsimp [lo, hi]; split_ifs <;> omega
  have hhi : ∀ j, hi j ≤ F := by
    intro j; dsimp [hi]; split_ifs <;> omega
  have hls : (∑ j, lo j) = marked.card*t := by
    dsimp [lo]
    rw [← sum_filter]
    simp
  have hus : (∑ j, hi j) = marked.card*F + (Fintype.card C-marked.card)*(t-1) := by
    dsimp [hi]
    rw [sum_ite]
    simp [filter_notMem_eq_sdiff, card_sdiff]
  obtain ⟨B, hrow, hcol⟩ := realize_column_intervals F d lo hi hlh hhi
    (by rwa [hls]) (by rwa [hus])
  exact ⟨B, hrow, fun j hj => by simpa [lo, hj] using (hcol j).1,
    fun j hj => by simpa [hi, hj] using (hcol j).2⟩

/-- The nontrivial branch of the exact incidence demand, written using a floor
and truncated subtraction, hence without integer ceilings. -/
def threshold (F m d t : ℕ) : ℕ := m - min m (F*(m-d)/(F-t+1))

theorem threshold_le_row (F m d t : ℕ) (ht : 1 ≤ t) (htF : t ≤ F) (hd : d ≤ m) :
    threshold F m d t ≤ d := by
  have hD : 0 < F-t+1 := by omega
  have hmul : (m-d)*(F-t+1) ≤ F*(m-d) := by
    have : F-t+1 ≤ F := by omega
    nlinarith
  have := (Nat.le_div_iff_mul_le hD).2 hmul
  dsimp [threshold]
  omega

theorem threshold_capacity (F m d t : ℕ) (ht : 1 ≤ t) (htF : t ≤ F) (hd : d ≤ m) :
    F*d ≤ threshold F m d t*F + (m-threshold F m d t)*(t-1) := by
  have hD : 0 < F-t+1 := by omega
  have hdiv := Nat.div_mul_le_self (F*(m-d)) (F-t+1)
  have hmin : min m (F*(m-d)/(F-t+1)) ≤ F*(m-d)/(F-t+1) := min_le_right _ _
  have hw : threshold F m d t ≤ m := Nat.sub_le _ _
  have hcomp : m-threshold F m d t = min m (F*(m-d)/(F-t+1)) := by
    exact Nat.sub_sub_self (min_le_left m (F*(m-d)/(F-t+1)))
  have hm : (m-threshold F m d t)*(F-t+1) ≤ F*(m-d) := by
    rw [hcomp]
    nlinarith
  have hFt : F = (t-1)+(F-t+1) := by omega
  have hmd : m = d+(m-d) := by omega
  have hmw : m = threshold F m d t + (m-threshold F m d t) := by omega
  nlinarith

/-- Lemma 5.2 in the `1 ≤ t ≤ F` branch, including the exact threshold formula. -/
theorem realize_exact_threshold {C : Type*} [Fintype C] [DecidableEq C]
    (F d t : ℕ) (marked : Finset C) (ht : 1 ≤ t) (htF : t ≤ F)
    (hd : d ≤ Fintype.card C)
    (hmarked : marked.card = threshold F (Fintype.card C) d t) :
    ∃ B : Fin F → C → Prop, (∀ r, rowSum B r = d) ∧
      (∀ j ∈ marked, t ≤ colSum B j) ∧
      (∀ j ∉ marked, colSum B j ≤ t-1) := by
  apply realize_marked_columns F d t marked ht htF
  · rw [hmarked]
    have := threshold_le_row F (Fintype.card C) d t ht htF hd
    nlinarith
  · rw [hmarked]
    exact threshold_capacity F (Fintype.card C) d t ht htF hd

/-- The automatic `t > F` branch of Lemma 5.2: there are no marked columns,
and any row degree at most the number of columns can be realized. -/
theorem realize_above_row_count {C : Type*} [Fintype C] [DecidableEq C]
    (F d t : ℕ) (htF : F < t) (hd : d ≤ Fintype.card C) :
    ∃ B : Fin F → C → Prop, (∀ r, rowSum B r = d) ∧
      (∀ j, colSum B j ≤ t-1) := by
  classical
  obtain ⟨B, hrow, hcol⟩ := realize_column_intervals F d (fun _ : C => 0)
    (fun _ : C => F) (fun _ => Nat.zero_le _) (fun _ => le_rfl)
    (by simp) (by simp; nlinarith)
  refine ⟨B, hrow, fun j => ?_⟩
  have := (hcol j).2
  omega

/-- Combined incidence realization, using the zero threshold in the automatic
branch and the exact floor threshold in the nontrivial branch. -/
theorem realize_frontier {C : Type*} [Fintype C] [DecidableEq C]
    (F d t : ℕ) (marked : Finset C) (ht : 1 ≤ t) (hd : d ≤ Fintype.card C)
    (hmarked : marked.card = if F < t then 0 else threshold F (Fintype.card C) d t) :
    ∃ B : Fin F → C → Prop, (∀ r, rowSum B r = d) ∧
      (∀ j ∈ marked, t ≤ colSum B j) ∧
      (∀ j ∉ marked, colSum B j ≤ t-1) := by
  classical
  by_cases htF : F < t
  · have hm : marked = ∅ := card_eq_zero.mp (by simpa [htF] using hmarked)
    obtain ⟨B, hrow, hcol⟩ := realize_above_row_count F d t htF hd
    exact ⟨B, hrow, by simp [hm], fun j _ => hcol j⟩
  · apply realize_exact_threshold F d t marked ht (by omega) hd
    simpa [htF] using hmarked

/-- Lemma 4.2's finite incidence conclusion, after the residual order-statistic
argument has shown that a column with at least `t` misses is outgoing. -/
theorem failure_forces_frontier {R C : Type*} [Fintype R] [Fintype C] [DecidableEq C]
    (B : R → C → Prop) (out : Finset C) (d t : ℕ) (ht : 1 ≤ t)
    (hd : d ≤ Fintype.card C) (hrow : ∀ r, d ≤ rowSum B r)
    (hforce : ∀ c, t ≤ colSum B c → c ∈ out) :
    (if Fintype.card R < t then 0 else threshold (Fintype.card R) (Fintype.card C) d t)
      ≤ out.card := by
  classical
  split_ifs with hF
  · exact Nat.zero_le _
  · exact degree_threshold_of_capacity (Fintype.card R) (Fintype.card C) d t out.card
      ht (by omega) hd (card_le_univ out) (incidence_capacity B out d t hrow hforce)

end MEJF.Incidence
