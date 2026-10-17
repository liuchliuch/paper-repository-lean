import Paper37.DPBounds

/-! The occupied-coordinate refinement in Appendix E. Each refined entry is
specified independently as an actual finite count-vector sum. The projection
and divisibility statements do not assume the recurrence or a word/DP bridge. -/
namespace Paper37.AdaptiveDP
open Finset
open Paper37.DP

/-- Occupied coordinates after adding the future histogram to the observed one. -/
def occupied (a : ℕ → ℕ) (s : Finset ℕ) (b : ℕ → ℕ) : ℕ :=
  (s.filter (fun d => 0 < a d + b d)).card

lemma occupied_le (a : ℕ → ℕ) (s : Finset ℕ) (b : ℕ → ℕ) : occupied a s b ≤ s.card :=
  card_filter_le _ _

/-- Refined G table, before restricting the occupied-type coordinate. -/
noncomputable def refinedG (a : ℕ → ℕ) (s : Finset ℕ) (k u j : ℕ) : ℕ :=
  ∑ b ∈ s.piAntidiag k,
    if lengthSum s b = u ∧ occupied a s b = j then
      Nat.multinomial s b * weight a s b else 0

/-- Refined marked S table from E.6. -/
noncomputable def refinedS (a : ℕ → ℕ) (s : Finset ℕ) (A k u j : ℕ) : ℕ :=
  ∑ b ∈ s.piAntidiag k,
    if lengthSum s b = u ∧ occupied a s b = j then
      Nat.multinomial s b * weight a s b * marked s A b else 0

/-- Refined first-admissible ordering aggregate. -/
noncomputable def refinedF (a : ℕ → ℕ) (s : Finset ℕ) (A k u j : ℕ) : ℕ :=
  ∑ b ∈ s.piAntidiag k,
    if lengthSum s b = u ∧ occupied a s b = j then
      admissibleOrders s A b * weight a s b else 0

/-- E.8: summing the occupied coordinate recovers the ordinary table exactly. -/
theorem refinedG_projection (a : ℕ → ℕ) (s : Finset ℕ) (k u L : ℕ) (hL : s.card ≤ L) :
    ∑ j ∈ range (L+1), refinedG a s k u j = G a s k u := by
  classical
  unfold refinedG G
  rw [sum_comm]
  apply sum_congr rfl
  intro b hb
  have hj : occupied a s b ∈ range (L+1) := mem_range.mpr (by have := occupied_le a s b; omega)
  by_cases hu : lengthSum s b = u
  · simp [hu,eq_comm,hj]
  · simp [hu]

theorem refinedS_projection (a : ℕ → ℕ) (s : Finset ℕ) (A k u L : ℕ) (hL : s.card ≤ L) :
    ∑ j ∈ range (L+1), refinedS a s A k u j = S a s A k u := by
  classical
  unfold refinedS S
  rw [sum_comm]
  apply sum_congr rfl
  intro b hb
  have hj : occupied a s b ∈ range (L+1) := mem_range.mpr (by have := occupied_le a s b; omega)
  by_cases hu : lengthSum s b = u
  · simp [hu,eq_comm,hj]
  · simp [hu]

lemma refinedG_le_G (a : ℕ → ℕ) (s : Finset ℕ) (k u j : ℕ) :
    refinedG a s k u j ≤ G a s k u := by
  classical
  apply sum_le_sum
  intro b hb
  split_ifs <;> omega

lemma refinedS_le_S (a : ℕ → ℕ) (s : Finset ℕ) (A k u j : ℕ) :
    refinedS a s A k u j ≤ S a s A k u := by
  classical
  apply sum_le_sum
  intro b hb
  split_ifs <;> omega

/-- Every occupied-type slice retains the exact integer division certificate. -/
theorem refinedS_eq_mul_F (a : ℕ → ℕ) (s : Finset ℕ) (A k u j : ℕ) :
    refinedS a s A k u j = k * refinedF a s A k u j := by
  classical
  unfold refinedS refinedF
  rw [mul_sum]
  apply sum_congr rfl
  intro b hb
  split_ifs with h
  · have ho := marked_ordering_identity s A b
    rw [(mem_piAntidiag.mp hb).1] at ho
    calc
      _ = (Nat.multinomial s b * marked s A b) * weight a s b := by ring
      _ = _ := by rw [ho]; ring
  · simp

lemma refinedS_divisible (a : ℕ → ℕ) (s : Finset ℕ) (A k u j : ℕ) :
    k ∣ refinedS a s A k u j := by
  rw [refinedS_eq_mul_F]
  exact dvd_mul_right k _

/-- The prefix sum in the occupied coordinate is exact divisibility, too. -/
theorem restrictedS_divisible (a : ℕ → ℕ) (s : Finset ℕ) (A k u t : ℕ) :
    k ∣ ∑ j ∈ range (t+1), refinedS a s A k u j := by
  exact dvd_sum (fun j hj => refinedS_divisible a s A k u j)

/-- Refined entries inherit genuine ordinary-table numeric bounds. -/
theorem refinedS_le_power (a : ℕ → ℕ) (s : Finset ℕ) (A k u j N : ℕ)
    (hN : 0 < N) (hcard : s.card ≤ N) (hsize : s.sum a + k ≤ N) :
    refinedS a s A k u j ≤ N^(2*N+1) :=
  (refinedS_le_S _ _ _ _ _ _).trans (S_le_power _ _ _ _ _ _ hN hcard hsize)

lemma refinedG_binarySize (a : ℕ → ℕ) (s : Finset ℕ) (k u j N : ℕ)
    (hN : 0 < N) (hcard : s.card ≤ N) (hsize : s.sum a + k ≤ N) :
    (refinedG a s k u j).size ≤ 2*N*N.size+1 := by
  apply binarySize_le_of_le_pow
  calc
    _ ≤ G a s k u := refinedG_le_G _ _ _ _ _
    _ ≤ N^(2*N) := by
      have hh := G_le_square_power a s k u N hN hcard hsize
      simpa [pow_add,two_mul] using hh

private lemma new_zero {s : Finset ℕ} {d k : ℕ} {b : ℕ → ℕ}
    (hd : d ∉ s) (hb : b ∈ s.piAntidiag k) : b d = 0 := by
  by_contra h
  exact hd ((mem_piAntidiag.mp hb).2 d h)

private lemma new_at {s : Finset ℕ} {d k c : ℕ} {b : ℕ → ℕ}
    (hd : d ∉ s) (hb : b ∈ s.piAntidiag k) :
    (b + fun i => if i = d then c else 0) d = c := by
  simp [Pi.add_apply,new_zero hd hb]

private lemma old_at {s : Finset ℕ} {d c : ℕ} {b : ℕ → ℕ}
    (hd : d ∉ s) {i : ℕ} (hi : i ∈ s) :
    (b + fun i => if i = d then c else 0) i = b i := by
  have hh : i ≠ d := ne_of_mem_of_not_mem hi hd
  simp [Pi.add_apply,hh]

private lemma weight_new {s : Finset ℕ} {d k c : ℕ} {b : ℕ → ℕ}
    (a : ℕ → ℕ) (hd : d ∉ s) (hb : b ∈ s.piAntidiag k) :
    weight a (s.cons d hd) (b + fun i => if i = d then c else 0) =
      (a d+c)^(a d+c)*weight a s b := by
  simp only [weight,prod_cons,new_at hd hb]
  congr 1
  exact prod_congr rfl (fun i hi => by rw [old_at hd hi])

private lemma length_new {s : Finset ℕ} {d k c : ℕ} {b : ℕ → ℕ}
    (hd : d ∉ s) (hb : b ∈ s.piAntidiag k) :
    lengthSum (s.cons d hd) (b + fun i => if i = d then c else 0) = d*c+lengthSum s b := by
  simp only [lengthSum,sum_cons,new_at hd hb]
  congr 1
  exact sum_congr rfl (fun i hi => by rw [old_at hd hi])

private lemma marked_new {s : Finset ℕ} {A d k c : ℕ} {b : ℕ → ℕ}
    (hd : d ∉ s) (hb : b ∈ s.piAntidiag k) :
    marked (s.cons d hd) A (b + fun i => if i = d then c else 0) =
      (if A<d then c else 0)+marked s A b := by
  simp only [marked,sum_cons,new_at hd hb]
  congr 1
  exact sum_congr rfl (fun i hi => by rw [old_at hd hi])

private lemma multinomial_new {s : Finset ℕ} {d k c : ℕ} {b : ℕ → ℕ}
    (hd : d ∉ s) (hb : b ∈ s.piAntidiag k) :
    Nat.multinomial (s.cons d hd) (b + fun i => if i = d then c else 0) =
      (c+k).choose c * Nat.multinomial s b := by
  rw [Nat.multinomial_cons,new_at hd hb]
  have hs : ∑ i ∈ s, (b + fun i => if i = d then c else 0) i = k := by
    rw [← (mem_piAntidiag.mp hb).1]
    exact sum_congr rfl (fun i hi => old_at hd hi)
  rw [hs]
  congr 1
  exact Nat.multinomial_congr (fun i hi => old_at hd hi)

/-- The extra coordinate increments iff the new total count is positive. -/
lemma occupied_new {s : Finset ℕ} {d k c : ℕ} {b : ℕ → ℕ}
    (a : ℕ → ℕ) (hd : d ∉ s) (hb : b ∈ s.piAntidiag k) :
    occupied a (s.cons d hd) (b + fun i => if i = d then c else 0) =
      occupied a s b + (if 0<a d+c then 1 else 0) := by
  classical
  have heq : s.filter (fun i => 0<a i+(b + fun i => if i=d then c else 0) i) =
      s.filter (fun i => 0<a i+b i) := by
    apply filter_congr
    intro i hi
    rw [old_at hd hi]
  unfold occupied
  rw [Finset.cons_eq_insert,filter_insert,new_at hd hb,heq]
  split_ifs with h
  · rw [card_insert_of_notMem (fun hi => hd (mem_filter.mp hi).1)]
  · omega

/-- E.5 derived from the independent filtered count-vector specification,
with out-of-range occupied-coordinate states explicitly zero. -/
theorem refinedG_cons (a : ℕ → ℕ) (s : Finset ℕ) (d k u j : ℕ) (hd : d ∉ s) :
    refinedG a (s.cons d hd) k u j =
      ∑ p ∈ antidiagonal k,
        if d*p.1 ≤ u ∧ (if 0<a d+p.1 then 1 else 0) ≤ j then
          k.choose p.1*(a d+p.1)^(a d+p.1)*
            refinedG a s p.2 (u-d*p.1) (j-(if 0<a d+p.1 then 1 else 0))
        else 0 := by
  classical
  unfold refinedG
  rw [piAntidiag_cons,sum_disjiUnion]
  apply sum_congr rfl
  intro p hp
  rw [sum_map]
  have hp' := mem_antidiagonal.mp hp
  simp only [addRightEmbedding_apply]
  by_cases hg : d*p.1 ≤ u ∧ (if 0<a d+p.1 then 1 else 0) ≤ j
  · rw [if_pos hg,mul_sum]
    apply sum_congr rfl
    intro b hb
    rw [length_new hd hb,occupied_new a hd hb,multinomial_new hd hb,weight_new a hd hb]
    have he : d*p.1+lengthSum s b=u ∧ occupied a s b+(if 0<a d+p.1 then 1 else 0)=j ↔
        lengthSum s b=u-d*p.1 ∧ occupied a s b=j-(if 0<a d+p.1 then 1 else 0) := by omega
    simp only [he,hp']
    split_ifs <;> ring
  · rw [if_neg hg]
    apply sum_eq_zero
    intro b hb
    rw [length_new hd hb,occupied_new a hd hb]
    have he : ¬(d*p.1+lengthSum s b=u ∧ occupied a s b+(if 0<a d+p.1 then 1 else 0)=j) := by omega
    rw [if_neg he]

/-- E.6, including the marked contribution of new gap copies. -/
theorem refinedS_cons (a : ℕ → ℕ) (s : Finset ℕ) (A d k u j : ℕ) (hd : d ∉ s) :
    refinedS a (s.cons d hd) A k u j =
      ∑ p ∈ antidiagonal k,
        if d*p.1 ≤ u ∧ (if 0<a d+p.1 then 1 else 0) ≤ j then
          k.choose p.1*(a d+p.1)^(a d+p.1)*
            (refinedS a s A p.2 (u-d*p.1) (j-(if 0<a d+p.1 then 1 else 0)) +
              (if A<d then p.1 else 0)*refinedG a s p.2 (u-d*p.1) (j-(if 0<a d+p.1 then 1 else 0)))
        else 0 := by
  classical
  unfold refinedS refinedG
  rw [piAntidiag_cons,sum_disjiUnion]
  apply sum_congr rfl
  intro p hp
  rw [sum_map]
  have hp' := mem_antidiagonal.mp hp
  simp only [addRightEmbedding_apply]
  by_cases hg : d*p.1 ≤ u ∧ (if 0<a d+p.1 then 1 else 0) ≤ j
  · rw [if_pos hg,mul_sum,← sum_add_distrib,mul_sum]
    apply sum_congr rfl
    intro b hb
    rw [length_new hd hb,occupied_new a hd hb,multinomial_new hd hb,weight_new a hd hb,marked_new hd hb]
    have he : d*p.1+lengthSum s b=u ∧ occupied a s b+(if 0<a d+p.1 then 1 else 0)=j ↔
        lengthSum s b=u-d*p.1 ∧ occupied a s b=j-(if 0<a d+p.1 then 1 else 0) := by omega
    simp only [he,hp']
    split_ifs <;> ring
  · rw [if_neg hg]
    apply sum_eq_zero
    intro b hb
    rw [length_new hd hb,occupied_new a hd hb]
    have he : ¬(d*p.1+lengthSum s b=u ∧ occupied a s b+(if 0<a d+p.1 then 1 else 0)=j) := by omega
    rw [if_neg he]

private lemma gapSet_step (d : ℕ) :
    gapSet (d+1) = (gapSet d).cons (d+1) (by simp [gapSet]) := by
  ext i
  simp only [gapSet,mem_Icc,mem_cons]
  omega

noncomputable def refinedGd (a : ℕ → ℕ) (d k u j : ℕ) : ℕ := refinedG a (gapSet d) k u j
noncomputable def refinedSd (a : ℕ → ℕ) (A d k u j : ℕ) : ℕ := refinedS a (gapSet d) A k u j

@[simp] lemma refinedGd_zero (a : ℕ → ℕ) (k u j : ℕ) :
    refinedGd a 0 k u j = if k=0 ∧ u=0 ∧ j=0 then 1 else 0 := by
  by_cases hk : k=0
  · subst k
    simp [refinedGd,refinedG,occupied,lengthSum,weight,eq_comm]
  · simp [refinedGd,refinedG,hk]

@[simp] lemma refinedSd_zero (a : ℕ → ℕ) (A k u j : ℕ) : refinedSd a A 0 k u j = 0 := by
  simp [refinedSd,refinedS,marked]

lemma refinedGd_step (a : ℕ → ℕ) (d k u j : ℕ) :
    refinedGd a (d+1) k u j =
      ∑ b ∈ range (k+1), if (d+1)*b ≤ u ∧ (if 0<a (d+1)+b then 1 else 0) ≤ j then
        k.choose b*(a (d+1)+b)^(a (d+1)+b)*
          refinedGd a d (k-b) (u-(d+1)*b) (j-(if 0<a (d+1)+b then 1 else 0)) else 0 := by
  unfold refinedGd
  rw [gapSet_step,refinedG_cons,Nat.antidiagonal_eq_map,sum_map]
  rfl

lemma refinedSd_step (a : ℕ → ℕ) (A d k u j : ℕ) :
    refinedSd a A (d+1) k u j =
      ∑ b ∈ range (k+1), if (d+1)*b ≤ u ∧ (if 0<a (d+1)+b then 1 else 0) ≤ j then
        k.choose b*(a (d+1)+b)^(a (d+1)+b)*
          (refinedSd a A d (k-b) (u-(d+1)*b) (j-(if 0<a (d+1)+b then 1 else 0)) +
            (if A<d+1 then b else 0)*refinedGd a d (k-b) (u-(d+1)*b) (j-(if 0<a (d+1)+b then 1 else 0))) else 0 := by
  unfold refinedSd refinedGd
  rw [gapSet_step,refinedS_cons,Nat.antidiagonal_eq_map,sum_map]
  rfl

/-- A materialized rolling layer with the three `k,u,j` axes. -/
abbrev RefinedLayer (N : ℕ) := Vector (Vector (Vector (ℕ×ℕ) (N+1)) (N+1)) (N+1)

private def subIdx {N : ℕ} (i : Fin (N+1)) (b : ℕ) : Fin (N+1) :=
  ⟨i.val-b,lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩

/-- Lookup in the materialized three-axis rolling layer. -/
def refinedAt {N : ℕ} (old : RefinedLayer N) (k u j : Fin (N+1)) : ℕ×ℕ :=
  old[k.val][u.val][j.val]
attribute [irreducible] refinedAt

private def refinedEntry (N : ℕ) (a : ℕ → ℕ) (A d : ℕ) (old : RefinedLayer N)
    (k u j : Fin (N+1)) : ℕ×ℕ :=
    (∑ b ∈ range (k.val+1),
      if (d+1)*b ≤ u.val ∧ (if 0<a (d+1)+b then 1 else 0) ≤ j.val then
        k.val.choose b*(a (d+1)+b)^(a (d+1)+b)*
          (refinedAt old (subIdx k b) (subIdx u ((d+1)*b)) (subIdx j (if 0<a (d+1)+b then 1 else 0))).1 else 0,
     ∑ b ∈ range (k.val+1),
      if (d+1)*b ≤ u.val ∧ (if 0<a (d+1)+b then 1 else 0) ≤ j.val then
        k.val.choose b*(a (d+1)+b)^(a (d+1)+b)*
          ((refinedAt old (subIdx k b) (subIdx u ((d+1)*b)) (subIdx j (if 0<a (d+1)+b then 1 else 0))).2 +
            (if A<d+1 then b else 0)*
              (refinedAt old (subIdx k b) (subIdx u ((d+1)*b)) (subIdx j (if 0<a (d+1)+b then 1 else 0))).1) else 0)

/-- Executable one-layer update for the independently specified aggregates. -/
def refinedStep (N : ℕ) (a : ℕ → ℕ) (A d : ℕ) (old : RefinedLayer N) : RefinedLayer N :=
  Vector.ofFn fun k => Vector.ofFn fun u => Vector.ofFn fun j => refinedEntry N a A d old k u j

private lemma refinedAt_step (N : ℕ) (a : ℕ → ℕ) (A d : ℕ) (old : RefinedLayer N)
    (k u j : Fin (N+1)) : refinedAt (refinedStep N a A d old) k u j = refinedEntry N a A d old k u j := by
  unfold refinedAt refinedStep
  simp only [Vector.getElem_ofFn]

def refinedRun (N : ℕ) (a : ℕ → ℕ) (A : ℕ) : ℕ → RefinedLayer N
  | 0 => Vector.ofFn fun k => Vector.ofFn fun u => Vector.ofFn fun j =>
      (if k.val=0 ∧ u.val=0 ∧ j.val=0 then 1 else 0,0)
  | d+1 => refinedStep N a A d (refinedRun N a A d)

set_option maxHeartbeats 400000 in
/-- Every materialized entry equals its independent count-vector sum. -/
theorem refinedRun_correct (N : ℕ) (a : ℕ → ℕ) (A d : ℕ) (k u j : Fin (N+1)) :
    refinedAt (refinedRun N a A d) k u j =
      (refinedGd a d k.val u.val j.val,refinedSd a A d k.val u.val j.val) := by
  induction d generalizing k u j with
  | zero => simp [refinedRun,refinedAt]
  | succ d ih =>
    rw [refinedRun,refinedAt_step]
    unfold refinedEntry
    apply Prod.ext
    · dsimp only
      conv_rhs => rw [refinedGd_step]
      apply sum_congr rfl
      intro b hb
      by_cases hg : (d+1)*b ≤ u.val ∧ (if 0<a (d+1)+b then 1 else 0) ≤ j.val
      · rw [if_pos hg,if_pos hg]
        rw [ih (subIdx k b) (subIdx u ((d+1)*b)) (subIdx j (if 0<a (d+1)+b then 1 else 0))]
        rfl
      · rw [if_neg hg,if_neg hg]
    · dsimp only
      conv_rhs => rw [refinedSd_step]
      apply sum_congr rfl
      intro b hb
      by_cases hg : (d+1)*b ≤ u.val ∧ (if 0<a (d+1)+b then 1 else 0) ≤ j.val
      · rw [if_pos hg,if_pos hg]
        rw [ih (subIdx k b) (subIdx u ((d+1)*b)) (subIdx j (if 0<a (d+1)+b then 1 else 0))]
        rfl
      · rw [if_neg hg,if_neg hg]

/-- Exact recurrence-summand count of the displayed materialized layer schedule. -/
def refinedUpdateCount (N L : ℕ) : ℕ :=
  ∑ d ∈ range L, ∑ k ∈ range (N+1), ∑ u ∈ range (N+1), ∑ j ∈ range (N+1), (k+1)

lemma refinedUpdateCount_le (N L : ℕ) : refinedUpdateCount N L ≤ L*(N+1)^4 := by
  unfold refinedUpdateCount
  calc
    _ ≤ ∑ _d ∈ range L, ∑ _k ∈ range (N+1), ∑ _u ∈ range (N+1), ∑ _j ∈ range (N+1), (N+1) := by
      apply sum_le_sum
      intro d hd
      apply sum_le_sum
      intro k hk
      apply sum_le_sum
      intro u hu
      apply sum_le_sum
      intro j hj
      have hh := mem_range.mp hk
      omega
    _ = _ := by simp [pow_succ,mul_assoc]

/-- The genuine finite update schedule has the stated fifth-degree bound. -/
theorem refinedUpdateCount_quintic (N L : ℕ) (hL : L ≤ N) :
    refinedUpdateCount N L ≤ (N+1)^5 := by
  calc
    _ ≤ L*(N+1)^4 := refinedUpdateCount_le N L
    _ ≤ (N+1)*(N+1)^4 := Nat.mul_le_mul_right _ (by omega)
    _ = _ := by ring

end Paper37.AdaptiveDP
