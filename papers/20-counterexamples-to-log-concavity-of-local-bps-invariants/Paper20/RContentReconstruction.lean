import Paper20.RContent36
import Paper20.PhiEvaluation

namespace Paper20.RContent36
open Finset
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

def aWeight (h i j c : ℕ) : ℤ :=
  (IntegerPolynomial.numeratorA ((c:ℤ)^2) (decide (c%2=0)) j).getD i 0*
    (FastQ36.cofactor h j:ℤ)

def evaluate (s : State) (h i : ℕ) : ℤ :=
  ((List.range (h+1)).map (fun j =>
    (s.map (fun p => p.2.getD (h-j) 0*aWeight h i j p.1)).sum)).sum

lemma single_weight_sum (k B : ℕ) (hk : k ≤ B) (v : ℤ) (w : ℕ → ℤ) :
    (∑ c ∈ range (B+1), (if k=c then v else 0)*w c) = v*w k := by
  rw [Finset.sum_eq_single k]
  · simp
  · intro c hc hck
    rw [if_neg (Ne.symm hck),zero_mul]
  · intro hnot
    exact False.elim (hnot (Finset.mem_range.mpr (by omega)))

theorem query_weight_sum (s : State) (B : ℕ) (hb : ∀ p ∈ s, p.1 ≤ B)
    (j : ℕ) (w : ℕ → ℤ) :
    (∑ c ∈ range (B+1), query c s j*w c) =
      (s.map (fun p => p.2.getD j 0*w p.1)).sum := by
  induction s with
  | nil => simp [query]
  | cons p s ih =>
    rcases p with ⟨k,v⟩
    simp only [query,add_mul,Finset.sum_add_distrib,List.map_cons,List.sum_cons]
    rw [single_weight_sum k B (hb (k,v) (by simp)),ih (fun p hp => hb p (by simp [hp]))]

lemma partition_query_weight_sum (pss : List (List ℕ)) (B : ℕ)
    (hb : ∀ ps ∈ pss, content ps ≤ B) (j : ℕ) (w : ℕ → ℤ) :
    (∑ c ∈ range (B+1),
      (pss.map (fun ps => if content ps=c then (weightedValues ps).getD j 0 else 0)).sum*w c) =
      (pss.map (fun ps => (weightedValues ps).getD j 0*w (content ps))).sum := by
  induction pss with
  | nil => simp
  | cons ps pss ih =>
    simp only [List.map_cons,List.sum_cons,add_mul,Finset.sum_add_distrib]
    rw [single_weight_sum (content ps) B (hb ps (by simp)),
      ih (fun p hp => hb p (by simp [hp]))]

lemma range_sum_list_comm {α : Type*} (xs : List α) (m : ℕ) (f : ℕ → α → ℤ) :
    (∑ j ∈ range m, (xs.map (f j)).sum) =
      (xs.map (fun x => ∑ j ∈ range m, f j x)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [Finset.sum_add_distrib,ih]

theorem partNumerator_abs (h i : ℕ) (ps : List ℕ) :
    FastQ36.partNumerator h i ps =
      ∑ j ∈ range (h+1), (weightedValues ps).getD (h-j) 0*aWeight h i j (content ps) := by
  have hs : contentOf ps*contentOf ps = (content ps:ℤ)^2 := by
    rw [content,Int.natAbs_pow_two]
    ring
  have hp : decide (contentOf ps%2=0) = decide (content ps%2=0) := by
    simp only [content,Phi.content_parity]
  dsimp only [FastQ36.partNumerator]
  rw [sum_map_range_int,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [weightedValues_getD,hs,hp]
  unfold aWeight
  ring

/-- The grouped certificate is reconstructed into the exact complete
integer Q numerator, by all content keys and every partition. -/
theorem evaluate_eq_totalNumerator (s : State) (hs : Correct root s)
    (hb : ∀ p ∈ s, p.1 ≤ 630) (h i : ℕ) (hH : h ≤ 22) :
    evaluate s h i = FastQ36.totalNumerator h i := by
  have hq : ∀ c j, j < 23 → query c s j =
      ((partitionsOf 36).map (fun ps => if content ps=c then
        (weightedValues ps).getD j 0 else 0)).sum := by
    intro c j hj
    simpa only [← parts_root] using hs c j hj
  rw [evaluate,sum_map_range_int]
  calc
    _ = ∑ j ∈ range (h+1), ∑ c ∈ range (630+1),
        query c s (h-j)*aWeight h i j c := by
      apply Finset.sum_congr rfl
      intro j hj
      exact (query_weight_sum s 630 hb (h-j) (aWeight h i j)).symm
    _ = ∑ j ∈ range (h+1),
        ((partitionsOf 36).map (fun ps => (weightedValues ps).getD (h-j) 0*
          aWeight h i j (content ps))).sum := by
      apply Finset.sum_congr rfl
      intro j hj
      simp only [hq _ _ (by omega : h-j < 23)]
      exact partition_query_weight_sum _ 630 (fun ps hp => content_bound hp) _ _
    _ = ((partitionsOf 36).map (fun ps =>
        ∑ j ∈ range (h+1), (weightedValues ps).getD (h-j) 0*aWeight h i j (content ps))).sum :=
      range_sum_list_comm _ _ _
    _ = _ := by
      unfold FastQ36.totalNumerator
      apply congrArg List.sum
      apply List.map_congr_left
      intro ps hp
      exact (partNumerator_abs h i ps).symm

theorem evaluate_scaled (s : State) (hs : Correct root s)
    (hb : ∀ p ∈ s, p.1 ≤ 630) (h i : ℕ) (hH : h ≤ 22) :
    (evaluate s h i:ℚ) = (FastQ36.denominator h:ℚ)*((36:ℕ).factorial:ℚ)*
      cget (Qcoeff 36 h) i := by
  rw [evaluate_eq_totalNumerator s hs hb h i hH]
  exact FastQ36.totalNumerator_scaled h i hH

end
end Paper20.RContent36
