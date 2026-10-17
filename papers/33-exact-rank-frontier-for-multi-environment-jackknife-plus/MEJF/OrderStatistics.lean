import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Real.Basic
import Mathlib.Data.EReal.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-! # Tie-preserving finite order statistics for the endpoint rule

The input is an indexed tuple, so equal values are retained with their original
multiplicity. `stat u k` has zero-based index `k`; paper rank `r` is index `r-1`.
-/
namespace MEJF.OrderStatistics

open Finset

noncomputable section

variable {α : Type*} [LinearOrder α] {n : ℕ}

/-- Ascending order statistic, retaining every indexed occurrence. -/
def stat (u : Fin n → α) (k : Fin n) : α := u (Tuple.sort u k)

/-- Number of indexed entries satisfying a predicate. -/
def count (u : Fin n → α) (p : α → Prop) : ℕ := by
  classical
  exact (Finset.univ.filter fun i => p (u i)).card

lemma stat_monotone_rank (u : Fin n → α) : Monotone (stat u) :=
  Tuple.monotone_sort u

lemma stat_of_monotone (u : Fin n → α) (hu : Monotone u) (k : Fin n) :
    stat u k = u k := by
  simp only [stat, Tuple.sort_eq_refl_iff_monotone.mpr hu, Equiv.refl_apply]

lemma stat_perm (u : Fin n → α) (σ : Equiv.Perm (Fin n)) (k : Fin n) :
    stat (u ∘ σ) k = stat u k := by
  exact congrFun (Tuple.comp_perm_comp_sort_eq_comp_sort (f := u) (σ := σ)) k

lemma count_perm (u : Fin n → α) (p : α → Prop) (σ : Equiv.Perm (Fin n)) :
    count (u ∘ σ) p = count u p := by
  classical
  simp only [count, ← Fintype.card_subtype]
  exact Fintype.card_congr (Equiv.subtypeEquiv σ fun i => Iff.rfl)

lemma stat_le_iff_count (u : Fin n → α) (k : Fin n) (x : α) :
    stat u k ≤ x ↔ k.val < count u (· ≤ x) := by
  classical
  have h := Tuple.lt_card_le_iff_apply_le_of_monotone
    (u ∘ Tuple.sort u) x (Tuple.monotone_sort u) k
  have hc : Fintype.card {i // (u ∘ Tuple.sort u) i ≤ x} =
      count (u ∘ Tuple.sort u) (· ≤ x) := by
    simp only [Fintype.card_subtype, count]
    congr 1
    ext i
    simp
  rw [hc, count_perm] at h
  exact h.symm

lemma lt_stat_iff_count (u : Fin n → α) (k : Fin n) (x : α) :
    x < stat u k ↔ count u (· ≤ x) ≤ k.val := by
  rw [← not_le, stat_le_iff_count, not_lt]

lemma count_mono (u : Fin n → α) {p q : α → Prop}
    (hpq : ∀ a, p a → q a) : count u p ≤ count u q := by
  classical
  apply Finset.card_mono
  intro i hi
  simp only [mem_filter, mem_univ, true_and] at *
  exact hpq _ hi

lemma count_le_add_count_gt (u : Fin n → α) (x : α) :
    count u (· ≤ x) + count u (x < ·) = n := by
  classical
  have h := Finset.filter_card_add_filter_neg_card_eq_card
    (s := (univ : Finset (Fin n))) (fun i : Fin n => u i ≤ x)
  have h₁ : count u (· ≤ x) = (univ.filter fun i : Fin n => u i ≤ x).card := by
    unfold count
    congr 1
    ext i
    simp
  have h₂ : count u (x < ·) = (univ.filter fun i : Fin n => ¬ u i ≤ x).card := by
    unfold count
    congr 1
    ext i
    simp
  rw [h₁, h₂]
  simpa using h

lemma count_le_self_stat (u : Fin n → α) (k : Fin n) :
    k.val + 1 ≤ count u (· ≤ stat u k) := by
  exact (stat_le_iff_count u k _).mp le_rfl

lemma stat_mono {u v : Fin n → α} (huv : ∀ i, u i ≤ v i) (k : Fin n) :
    stat u k ≤ stat v k := by
  apply (stat_le_iff_count _ _ _).mpr
  apply lt_of_lt_of_le ((stat_le_iff_count v k _).mp le_rfl)
  classical
  apply Finset.card_mono
  intro i hi
  simp only [count] at *
  simp only [mem_filter, mem_univ, true_and] at *
  exact (huv i).trans hi


lemma stat_le_max (u : Fin n → α) (k : Fin n) (M : α)
    (h : ∀ i, u i ≤ M) : stat u k ≤ M := h _

lemma min_le_stat (u : Fin n → α) (k : Fin n) (M : α)
    (h : ∀ i, M ≤ u i) : M ≤ stat u k := h _

@[simp] lemma stat_const (c : α) (k : Fin n) : stat (fun _ : Fin n => c) k = c := rfl

lemma le_stat_last {m : ℕ} (u : Fin (m+1) → α) (i : Fin (m+1)) :
    u i ≤ stat u (Fin.last m) := by
  have h := stat_monotone_rank u (Fin.le_last ((Tuple.sort u).symm i))
  simpa [stat] using h

lemma stat_map_monotone {β : Type*} [LinearOrder β] (u : Fin n → α)
    (g : α → β) (hg : Monotone g) (k : Fin n) :
    stat (g ∘ u) k = g (stat u k) := by
  have h := Tuple.unique_monotone (Tuple.monotone_sort (g ∘ u))
    (hg.comp (Tuple.monotone_sort u))
  exact congrFun h k

@[simp] lemma stat_add_const (u : Fin n → ℝ) (k : Fin n) (c : ℝ) :
    stat (fun i => u i + c) k = stat u k + c :=
  stat_map_monotone u (fun x => x + c) (fun _ _ h => add_le_add_right h c) k

@[simp] lemma stat_sub_const (u : Fin n → ℝ) (k : Fin n) (c : ℝ) :
    stat (fun i => u i - c) k = stat u k - c := by
  simpa only [sub_eq_add_neg] using stat_add_const u k (-c)

lemma stat_lipschitz (u v : Fin n → ℝ) (k : Fin n) (ε : ℝ)
    (h : ∀ i, |u i - v i| ≤ ε) : |stat u k - stat v k| ≤ ε := by
  apply abs_le.mpr
  have h₁ := stat_mono (u := u) (v := fun i => v i + ε)
    (fun i => by have := (abs_le.mp (h i)).2; linarith) k
  have h₂ := stat_mono (u := v) (v := fun i => u i + ε)
    (fun i => by have := (abs_le.mp (h i)).1; linarith) k
  simp only [stat_add_const] at h₁ h₂
  constructor <;> linarith

/-- The actual statistic is a one-Lipschitz map for the finite-product sup metric. -/
lemma lipschitz_stat (k : Fin n) :
    LipschitzWith 1 (fun u : Fin n → ℝ => stat u k) := by
  refine LipschitzWith.of_dist_le_mul fun u v => ?_
  simp only [NNReal.coe_one, one_mul, Real.dist_eq]
  exact stat_lipschitz u v k (dist u v) fun i => by
    simpa only [Real.dist_eq] using dist_le_pi_dist u v i

lemma continuous_stat (k : Fin n) : Continuous (fun u : Fin n → ℝ => stat u k) :=
  (lipschitz_stat k).continuous

lemma measurable_stat (k : Fin n) : Measurable (fun u : Fin n → ℝ => stat u k) :=
  (continuous_stat k).measurable

/-- Jointly measurable inputs give a measurable score quantile. -/
lemma measurable_stat_comp {Ω : Type*} [MeasurableSpace Ω]
    (u : Ω → Fin n → ℝ) (hu : ∀ i, Measurable fun ω => u ω i) (k : Fin n) :
    Measurable (fun ω => stat (u ω) k) :=
  (measurable_stat k).comp (measurable_pi_lambda _ hu)

/-- At least `n-k` indexed values strictly exceed any value below statistic `k`. -/
lemma count_gt_of_lt_stat (u : Fin n → α) (k : Fin n) (x : α)
    (h : x < stat u k) : n - k.val ≤ count u (x < ·) := by
  have h₁ := (lt_stat_iff_count u k x).mp h
  have h₂ := count_le_add_count_gt u x
  omega

/-- At least `k+1` indexed values are strictly below any value above statistic `k`. -/
lemma count_lt_of_stat_lt (u : Fin n → α) (k : Fin n) (x : α)
    (h : stat u k < x) : k.val + 1 ≤ count u (· < x) := by
  exact (count_le_self_stat u k).trans (count_mono u fun _ hle => hle.trans_lt h)

/-- The strict count criterion for the ascending rank `n+1-t` in the paper. -/
lemma residual_rank_gt (u : Fin n → α) (t : ℕ) (ht : 1 ≤ t) (htn : t ≤ n)
    (x : α) (h : t ≤ count u (x < ·)) :
    x < stat u ⟨n-t, by omega⟩ := by
  apply (lt_stat_iff_count _ _ _).mpr
  change count u (· ≤ x) ≤ n-t
  have := count_le_add_count_gt u x
  omega

/-- Extended paper ranks: zero is bottom and every rank beyond the tuple is top. -/
def extended [OrderBot α] [OrderTop α] (u : Fin n → α) (r : ℕ) : α :=
  if hr : r = 0 then ⊥ else if hn : r ≤ n then stat u ⟨r-1, by omega⟩ else ⊤

@[simp] lemma extended_zero [OrderBot α] [OrderTop α] (u : Fin n → α) :
    extended u 0 = ⊥ := by simp [extended]

@[simp] lemma extended_succ_length [OrderBot α] [OrderTop α] (u : Fin n → α) :
    extended u (n+1) = ⊤ := by simp [extended]

lemma extended_finite [OrderBot α] [OrderTop α] (u : Fin n → α) (r : ℕ)
    (hr : 1 ≤ r) (hn : r ≤ n) :
    extended u r = stat u ⟨r-1, by omega⟩ := by simp [extended, hn, show r ≠ 0 by omega]

/-- Lemma 4.1, deterministic endpoint part. Different ranks are allowed. -/
lemma aggregate_nonempty {A B : Fin n → α} (hAB : ∀ i, A i ≤ B i)
    (ell d : Fin n) (hed : ell ≤ d) : stat A ell ≤ stat B d :=
  (stat_mono hAB ell).trans (stat_monotone_rank B hed)

/-- A missed aggregate interval gives many missed candidate intervals even if
its aggregate endpoints cross. Paper ranks are `ell+1`, `d+1`; the balanced
outer-rank condition is `d+1 = n-ell`. -/
lemma aggregate_miss_count (A B : Fin n → α) (ell d : Fin n)
    (hrank : d.val + 1 = n - ell.val) (y : α)
    (hmiss : ¬ (stat A ell ≤ y ∧ y ≤ stat B d)) :
    d.val + 1 ≤ count (fun i => (A i, B i))
      (fun p => ¬ (p.1 ≤ y ∧ y ≤ p.2)) := by
  classical
  by_cases hl : stat A ell ≤ y
  · have hu : stat B d < y := lt_of_not_ge (fun h => hmiss ⟨hl,h⟩)
    apply (count_lt_of_stat_lt B d y hu).trans
    apply Finset.card_mono
    intro i hi
    simp only [count, mem_filter, mem_univ, true_and] at *
    exact fun h => (not_le_of_gt hi) h.2
  · have hl' : y < stat A ell := lt_of_not_ge hl
    rw [hrank]
    apply (count_gt_of_lt_stat A ell y hl').trans
    apply Finset.card_mono
    intro i hi
    simp only [count, mem_filter, mem_univ, true_and] at *
    exact fun h => (not_le_of_gt hi) h.1

/-- For finite centers and radii, a candidate miss is precisely a strict residual excess. -/
lemma candidate_miss_iff (y p r : ℝ) :
    ¬ (p-r ≤ y ∧ y ≤ p+r) ↔ r < |y-p| := by
  have hh : (p-r ≤ y ∧ y ≤ p+r) ↔ |y-p| ≤ r := by
    rw [abs_le]
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  simpa only [not_le] using not_congr hh

end
end MEJF.OrderStatistics
