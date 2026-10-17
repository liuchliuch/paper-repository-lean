import Paper37.PartitionBound
import Paper37.EnvelopeBridge

/-! Finite Euler-box proof of the uniform partition estimate. -/
noncomputable section
open scoped BigOperators
namespace Paper37.PartitionBound
open Finset Paper37.AnalyticBounds

lemma positive_multiset_card_le_sum (m : Multiset ℕ)
    (h : ∀ d ∈ m, 0 < d) : m.card ≤ m.sum := by
  induction m using Multiset.induction_on with
  | empty => simp
  | @cons a m ih =>
    have ha := h a (by simp)
    have hm := ih (fun d hd => h d (Multiset.mem_cons_of_mem hd))
    simp only [Multiset.card_cons, Multiset.sum_cons]
    omega

def partitionVector (n : ℕ) (p : Nat.Partition n) : Fin n → Fin (n+1) := fun i =>
  ⟨p.parts.count (i.val+1), Nat.lt_succ_of_le
    ((Multiset.count_le_card _ _).trans ((positive_multiset_card_le_sum p.parts
      (fun d hd => p.parts_pos hd)).trans_eq p.parts_sum))⟩

lemma partition_support (n : ℕ) (p : Nat.Partition n) : p.parts.toFinset ⊆ Icc 1 n := by
  intro d hd
  have hmem := Multiset.mem_toFinset.mp hd
  exact mem_Icc.mpr ⟨p.parts_pos hmem, (Multiset.le_sum_of_mem hmem).trans_eq p.parts_sum⟩

lemma partitionVector_injective (n : ℕ) : Function.Injective (partitionVector n) := by
  intro p q heq
  apply Nat.Partition.ext
  apply Multiset.ext.mpr
  intro d
  by_cases hd : d ∈ Icc 1 n
  · have hd' := mem_Icc.mp hd
    let i : Fin n := ⟨d-1, by omega⟩
    have hi : i.val+1=d := by dsimp [i]; omega
    have hh := congrArg Fin.val (congrFun heq i)
    simpa [partitionVector, hi] using hh
  · have hp : d ∉ p.parts := fun h => hd (partition_support n p (Multiset.mem_toFinset.mpr h))
    have hq : d ∉ q.parts := fun h => hd (partition_support n q (Multiset.mem_toFinset.mpr h))
    simp [Multiset.count_eq_zero_of_notMem hp, Multiset.count_eq_zero_of_notMem hq]

lemma prod_fin_succ_eq_Icc {M : Type*} [CommMonoid M] (n : ℕ) (f : ℕ → M) :
    (∏ i : Fin n, f (i.val+1)) = ∏ d ∈ Icc 1 n, f d := by
  apply prod_bij (fun i _ => i.val+1)
  · intro i hi; exact mem_Icc.mpr ⟨by omega, by omega⟩
  · intro i hi j hj h; apply Fin.ext; omega
  · intro d hd; exact ⟨⟨d-1, by have := mem_Icc.mp hd; omega⟩, mem_univ _, by
      have := mem_Icc.mp hd; dsimp; omega⟩
  · intro i hi; rfl

lemma exp_gap_product (θ : ℝ) (m : Multiset ℕ) :
    (m.map (fun d : ℕ => Real.exp (-θ * (d : ℝ)))).prod = Real.exp (-θ * (m.sum : ℝ)) := by
  induction m using Multiset.induction_on with
  | empty => simp
  | @cons a m ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.sum_cons, Nat.cast_add]
    rw [ih, ← Real.exp_add]
    congr 1
    ring

lemma partition_weight (n : ℕ) (p : Nat.Partition n) (θ : ℝ) :
    (∏ i : Fin n, Real.exp (-θ * ((i.val+1 : ℕ) : ℝ)) ^ (partitionVector n p i).val) =
      Real.exp (-θ * n) := by
  change (∏ i : Fin n, Real.exp (-θ * ((i.val+1 : ℕ) : ℝ)) ^ p.parts.count (i.val+1)) = _
  rw [prod_fin_succ_eq_Icc n (fun d : ℕ => Real.exp (-θ * (d : ℝ)) ^ p.parts.count d)]
  calc
    _ = ∏ d ∈ p.parts.toFinset, Real.exp (-θ * d) ^ p.parts.count d := by
      symm
      apply prod_subset (partition_support n p)
      intro d hd hnot
      rw [Multiset.count_eq_zero_of_notMem (fun h => hnot (Multiset.mem_toFinset.mpr h)), pow_zero]
    _ = (p.parts.map (fun d : ℕ => Real.exp (-θ*(d : ℝ)))).prod :=
      (prod_multiset_map_count _ _).symm
    _ = _ := by rw [exp_gap_product, p.parts_sum]

lemma partition_weighted_le_box (n : ℕ) (θ : ℝ) :
    (Fintype.card (Nat.Partition n) : ℝ) * Real.exp (-θ*n) ≤
      ∏ i : Fin n, ∑ b : Fin (n+1), Real.exp (-θ*((i.val+1 : ℕ) : ℝ)) ^ b.val := by
  let w : (Fin n → Fin (n+1)) → ℝ := fun v =>
    ∏ i, Real.exp (-θ*((i.val+1 : ℕ) : ℝ)) ^ (v i).val
  have hi := partitionVector_injective n
  calc
    _ = ∑ p : Nat.Partition n, Real.exp (-θ*n) := by
      simp only [sum_const, card_univ, nsmul_eq_mul]
    _ = ∑ p : Nat.Partition n, w (partitionVector n p) := by
      apply sum_congr rfl
      intro p hp
      exact (partition_weight n p θ).symm
    _ = ∑ v ∈ univ.image (partitionVector n), w v := by
      rw [sum_image (fun p hp q hq h => hi h)]
    _ ≤ ∑ v : Fin n → Fin (n+1), w v :=
      sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun v hv hn => by dsimp [w]; positivity)
    _ = _ := by
      dsimp only [w]
      exact (Fintype.prod_sum (fun i : Fin n => fun b : Fin (n+1) =>
        Real.exp (-θ*((i.val+1 : ℕ) : ℝ)) ^ b.val)).symm

lemma partition_weighted_bound (n : ℕ) {θ : ℝ} (hθ : 0 < θ) :
    (Fintype.card (Nat.Partition n) : ℝ) * Real.exp (-θ*n) ≤
      Real.exp (Real.pi^2/(6*θ)) := by
  calc
    _ ≤ ∏ i : Fin n, ∑ b : Fin (n+1), Real.exp (-θ*((i.val+1 : ℕ) : ℝ)) ^ b.val :=
      partition_weighted_le_box n θ
    _ ≤ ∏ i : Fin n, (1-Real.exp (-θ*((i.val+1 : ℕ) : ℝ)))⁻¹ := by
      apply prod_le_prod
      · intro i hi; positivity
      · intro i hi
        have hr : Real.exp (-θ*((i.val+1 : ℕ) : ℝ)) < 1 := Real.exp_lt_one_iff.mpr (by
          have : (0:ℝ) < ((i.val+1 : ℕ) : ℝ) := by positivity
          nlinarith)
        have hg := geom_sum_Ico_le_of_lt_one (K:=ℝ) (m:=0) (n:=n+1)
          (Real.exp_nonneg (-θ*((i.val+1 : ℕ) : ℝ))) hr
        rw [Nat.Ico_zero_eq_range, pow_zero, one_div] at hg
        calc
          _ = ∑ b ∈ range (n+1), Real.exp (-θ*((i.val+1 : ℕ) : ℝ)) ^ b :=
            Fin.sum_univ_eq_sum_range _ _
          _ ≤ _ := hg

    _ = Real.exp (∑ i : Fin n, -Real.log (1-Real.exp (-θ*((i.val+1 : ℕ) : ℝ)))) := by
      rw [Real.exp_sum]
      apply prod_congr rfl
      intro i hi
      have hp : 0 < 1-Real.exp (-θ*((i.val+1 : ℕ) : ℝ)) := by
        apply sub_pos.mpr
        apply Real.exp_lt_one_iff.mpr
        have : (0:ℝ) < ((i.val+1 : ℕ) : ℝ) := by positivity
        nlinarith
      rw [Real.exp_neg, Real.exp_log hp]
    _ ≤ _ := Real.exp_le_exp.mpr (by
      simpa only [Nat.cast_add, Nat.cast_one] using euler_log_sum_le hθ n)

/-- A nonasymptotic partition estimate valid for every positive integer, B.6. -/
theorem partition_exp_bound (n : ℕ) :
    (Fintype.card (Nat.Partition n) : ℝ) ≤ Real.exp (partitionConstant * Real.sqrt n) := by
  by_cases hn : n = 0
  · subst n; simp
  have hn' : (0:ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hr : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn'
  let θ := partitionConstant / (2 * Real.sqrt (n : ℝ))
  have hθ : 0 < θ := div_pos partitionConstant_pos (by positivity)
  have hb := partition_weighted_bound n hθ
  have hc : 3*partitionConstant^2 = 2*Real.pi^2 := by
    unfold partitionConstant
    calc
      _ = 3*Real.pi^2*(Real.sqrt (2/3 : ℝ))^2 := by ring
      _ = _ := by rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2/3)]; ring
  have hs := Real.sq_sqrt hn'.le
  have he : θ * n + Real.pi^2/(6*θ) = partitionConstant * Real.sqrt n := by
    have hfirst : θ * n = partitionConstant * Real.sqrt n / 2 := by
      have hdiv : (n : ℝ) / Real.sqrt n = Real.sqrt n :=
        (div_eq_iff hr.ne').2 (by nlinarith [hs])
      calc
        _ = partitionConstant / 2 * ((n : ℝ) / Real.sqrt n) := by
          dsimp [θ]
          field_simp [hr.ne']
          <;> ring
        _ = _ := by rw [hdiv]; ring
    have hsecond : Real.pi^2/(6*θ) = partitionConstant * Real.sqrt n / 2 := by
      apply (div_eq_iff (ne_of_gt (mul_pos (show (0:ℝ) < 6 by norm_num) hθ))).2
      dsimp [θ]
      field_simp [hr.ne']
      nlinarith [congrArg (fun x : ℝ => x * Real.sqrt n) hc]
    rw [hfirst, hsecond]
    ring
  calc
    _ ≤ Real.exp (Real.pi^2/(6*θ)) / Real.exp (-θ*n) :=
      (le_div_iff₀ (Real.exp_pos _)).mpr hb
    _ = Real.exp (θ*n+Real.pi^2/(6*θ)) := by rw [← Real.exp_sub]; congr 1; ring
    _ = _ := by rw [he]

/-- The cumulative bound in source B.5, on the standard partition type. -/
theorem cumulativePartitions_exp_bound (L : ℕ) :
    (Paper37.Envelope.cumulativePartitions L : ℝ) ≤
      (1+2*Real.sqrt L/partitionConstant)*Real.exp (partitionConstant*Real.sqrt L) := by
  unfold Paper37.Envelope.cumulativePartitions
  push_cast
  calc
    _ ≤ ∑ s : Fin (L+1), Real.exp (partitionConstant*Real.sqrt s.val) :=
      sum_le_sum fun s hs => partition_exp_bound s.val
    _ = ∑ s ∈ range (L+1), Real.exp (partitionConstant*Real.sqrt s) := by
      exact Fin.sum_univ_eq_sum_range (fun s : ℕ => Real.exp (partitionConstant*Real.sqrt s)) (L+1)
    _ ≤ _ := sum_exp_sqrt_le partitionConstant_pos L

end Paper37.PartitionBound
