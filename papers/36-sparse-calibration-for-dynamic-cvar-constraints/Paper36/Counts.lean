import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-! The frozen episode-start visit counts in Appendix C. Counts are actual
prefix sums of arbitrary bounded episode visit sequences. All potentials below
are proved from this recurrence, rather than assumed charging inequalities. -/
namespace Paper36.Counts
noncomputable section
open scoped BigOperators

def before (v : ℕ → ℕ) (k : ℕ) : ℕ := ∑ i ∈ Finset.range k, v i

@[simp] theorem before_zero (v : ℕ → ℕ) : before v 0 = 0 := by simp [before]
@[simp] theorem before_succ (v : ℕ → ℕ) (k : ℕ) :
    before v (k+1) = before v k + v k := by simp [before, Finset.sum_range_succ]

theorem before_le_succ (v : ℕ → ℕ) (k : ℕ) : before v k ≤ before v (k+1) := by
  rw [before_succ]
  omega

theorem before_bound {v : ℕ → ℕ} {H : ℕ} (hv : ∀ k, v k ≤ H) (K : ℕ) :
    before v K ≤ K * H := by
  unfold before
  calc
    _ ≤ ∑ _i ∈ Finset.range K, H := Finset.sum_le_sum fun i _ => hv i
    _ = _ := by simp

def lowCharge (v : ℕ → ℕ) (H K : ℕ) : ℕ :=
  ∑ k ∈ Finset.range K, if before v k < H then v k else 0

def highLogCharge (v : ℕ → ℕ) (H K : ℕ) : ℝ :=
  ∑ k ∈ Finset.range K, if H ≤ before v k then (v k : ℝ) / before v k else 0

def highSqrtCharge (v : ℕ → ℕ) (H K : ℕ) : ℝ :=
  ∑ k ∈ Finset.range K, if H ≤ before v k then (v k : ℝ) / Real.sqrt (before v k) else 0

/-- Including the final entire low-count episode costs strictly less than 2H. -/
theorem low_charge_lt {v : ℕ → ℕ} {H : ℕ} (hH : 0 < H)
    (hv : ∀ k, v k ≤ H) (K : ℕ) : lowCharge v H K < 2 * H := by
  have hinv : ∀ n : ℕ,
      (before v n < H → lowCharge v H n = before v n) ∧
      (H ≤ before v n → lowCharge v H n < 2 * H) := by
    intro n
    induction n with
    | zero => simp [lowCharge, hH]
    | succ n ih =>
      simp only [lowCharge, Finset.sum_range_succ]
      by_cases hn : before v n < H
      · rw [if_pos hn]
        have heq := ih.1 hn
        unfold lowCharge at heq
        rw [heq]
        constructor
        · intro _
          exact (before_succ v n).symm
        · intro _
          have hvn := hv n
          omega
      · rw [if_neg hn, add_zero]
        constructor
        · intro hnext
          have := before_le_succ v n
          omega
        · intro _
          exact ih.2 (Nat.le_of_not_gt hn)
  by_cases hlast : before v K < H
  · rw [(hinv K).1 hlast]
    omega
  · exact (hinv K).2 (Nat.le_of_not_gt hlast)

/-- The local logarithmic inequality can be derived from log z ≤ z−1. -/
theorem log_step {N n : ℝ} (hN : 0 < N) (hn : 0 ≤ n) (hnN : n ≤ N) :
    n / N ≤ 2 * (Real.log (N + n) - Real.log N) := by
  have hden : 0 < N + n := by linarith
  have hlog := Real.log_le_sub_one_of_pos (div_pos hN hden)
  rw [Real.log_div hN.ne' hden.ne'] at hlog
  have heq : N / (N + n) - 1 = -(n / (N+n)) := by field_simp; ring
  rw [heq] at hlog
  have hfrac : n / N ≤ 2 * (n / (N + n)) := by
    calc
      n / N ≤ (2 * n) / (N + n) := (div_le_div_iff₀ hN hden).2 (by nlinarith)
      _ = _ := by ring
  linarith

/-- The corresponding square-root potential increment. -/
theorem sqrt_step {N n : ℝ} (hN : 0 < N) (hn : 0 ≤ n) (hnN : n ≤ N) :
    n / Real.sqrt N ≤ 3 * (Real.sqrt (N+n) - Real.sqrt N) := by
  have ha := Real.sqrt_nonneg N
  have hb := Real.sqrt_nonneg (N+n)
  have hasq := Real.sq_sqrt hN.le
  have hbsq := Real.sq_sqrt (show 0 ≤ N+n by linarith)
  have hab : Real.sqrt N ≤ Real.sqrt (N+n) := Real.sqrt_le_sqrt (by linarith)
  have hb2 : Real.sqrt (N+n) ≤ 2 * Real.sqrt N := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · nlinarith
  have hp := mul_le_mul_of_nonneg_left (show
    Real.sqrt (N+n) + Real.sqrt N ≤ 3 * Real.sqrt N by linarith) (sub_nonneg.2 hab)
  apply (div_le_iff₀ (Real.sqrt_pos.2 hN)).2
  nlinarith

/-- For the logarithmic potential, flooring counts at H handles all low steps. -/
def capped (v : ℕ → ℕ) (H k : ℕ) : ℕ := max H (before v k)

theorem high_log_step {v : ℕ → ℕ} {H : ℕ} (hH : 0 < H)
    (hv : ∀ k, v k ≤ H) (k : ℕ) :
    (if H ≤ before v k then (v k : ℝ) / before v k else 0) ≤
      2 * (Real.log (capped v H (k+1)) - Real.log (capped v H k)) := by
  have hcpos : 0 < (capped v H k : ℝ) := by
    exact_mod_cast lt_of_lt_of_le hH (le_max_left H (before v k))
  have hmono : (capped v H k : ℝ) ≤ capped v H (k+1) := by
    exact_mod_cast max_le_max_left H (before_le_succ v k)
  by_cases hk : H ≤ before v k
  · rw [if_pos hk]
    have hk1 : H ≤ before v (k+1) := hk.trans (before_le_succ v k)
    simp only [capped, max_eq_right hk, max_eq_right hk1]
    rw [before_succ, Nat.cast_add]
    exact log_step (by exact_mod_cast lt_of_lt_of_le hH hk)
      (Nat.cast_nonneg _) (by exact_mod_cast (hv k).trans hk)
  · rw [if_neg hk]
    have hlog := Real.log_le_log hcpos hmono
    linarith

/-- Full-episode logarithmic telescoping for one row. -/
theorem high_log_charge_bound {v : ℕ → ℕ} {H : ℕ} (hH : 0 < H)
    (hv : ∀ k, v k ≤ H) {K : ℕ} (hK : 1 ≤ K) :
    highLogCharge v H K ≤ 2 * Real.log (Real.exp 1 * (K : ℝ) * H) := by
  have hpot : highLogCharge v H K ≤
      2 * (Real.log (capped v H K) - Real.log (capped v H 0)) := by
    unfold highLogCharge
    calc
      _ ≤ ∑ k ∈ Finset.range K, 2 *
          (Real.log (capped v H (k+1)) - Real.log (capped v H k)) :=
        Finset.sum_le_sum fun k _ => high_log_step hH hv k
      _ = _ := by rw [← Finset.mul_sum,
        Finset.sum_range_sub (fun k => Real.log (capped v H k)) K]
  have htotal := before_bound hv K
  have hcap : capped v H K ≤ K * H := max_le (by nlinarith) htotal
  have hH0 : (0 : ℝ) < H := by exact_mod_cast hH
  have hcap0 : 0 < (capped v H K : ℝ) := by
    exact_mod_cast lt_of_lt_of_le hH (le_max_left H (before v K))
  have hbound : (capped v H K : ℝ) ≤ Real.exp 1 * (K : ℝ) * H := by
    have hc : (capped v H K : ℝ) ≤ (K : ℝ) * H := by exact_mod_cast hcap
    have he : 1 ≤ Real.exp (1 : ℝ) := Real.one_le_exp_iff.2 (by norm_num)
    have hkh : 0 ≤ (K : ℝ) * H := by positivity
    nlinarith
  have hlog := Real.log_le_log hcap0 hbound
  have hlogH : 0 ≤ Real.log (H : ℝ) := Real.log_nonneg (by exact_mod_cast hH)
  have hpot' : highLogCharge v H K ≤
      2 * (Real.log (capped v H K) - Real.log (H : ℝ)) := by
    simpa [capped] using hpot
  linarith

/-- Full-episode square-root telescoping for one row. -/
theorem high_sqrt_charge_bound {v : ℕ → ℕ} {H : ℕ} (hH : 0 < H)
    (hv : ∀ k, v k ≤ H) (K : ℕ) :
    highSqrtCharge v H K ≤ 3 * Real.sqrt (before v K) := by
  have hstep : ∀ k : ℕ,
      (if H ≤ before v k then (v k : ℝ) / Real.sqrt (before v k) else 0) ≤
        3 * (Real.sqrt (before v (k+1)) - Real.sqrt (before v k)) := by
    intro k
    by_cases hk : H ≤ before v k
    · rw [if_pos hk, before_succ, Nat.cast_add]
      exact sqrt_step (by exact_mod_cast lt_of_lt_of_le hH hk)
        (Nat.cast_nonneg _) (by exact_mod_cast (hv k).trans hk)
    · rw [if_neg hk]
      have hm := Real.sqrt_le_sqrt (show (before v k : ℝ) ≤ before v (k+1) by
        exact_mod_cast before_le_succ v k)
      linarith
  unfold highSqrtCharge
  calc
    _ ≤ ∑ k ∈ Finset.range K, 3 *
        (Real.sqrt (before v (k+1)) - Real.sqrt (before v k)) :=
      Finset.sum_le_sum fun k _ => hstep k
    _ = _ := by
      rw [← Finset.mul_sum, Finset.sum_range_sub (fun k => Real.sqrt (before v k)) K]
      simp

section Rows
variable {ι : Type*} [DecidableEq ι] {rows : Finset ι} {v : ι → ℕ → ℕ} {H : ℕ}

theorem row_visit_bound (htotal : ∀ k, ∑ x ∈ rows, v x k ≤ H)
    {x : ι} (hx : x ∈ rows) (k : ℕ) : v x k ≤ H :=
  (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hx).trans (htotal k)

/-- Full low-count charge over all state-action rows, as used in (C.11). -/
theorem all_rows_low_charge (hrows : rows.Nonempty) (hH : 0 < H)
    (htotal : ∀ k, ∑ x ∈ rows, v x k ≤ H) (K : ℕ) :
    (∑ x ∈ rows, lowCharge (v x) H K) < 2 * rows.card * H := by
  have h := Finset.sum_lt_sum_of_nonempty hrows (fun x hx =>
    low_charge_lt hH (row_visit_bound htotal hx) K)
  simpa [mul_assoc, mul_left_comm, mul_comm] using h

/-- Full high-count logarithmic charge, with actual episode-start denominators. -/
theorem all_rows_log_charge (hH : 0 < H)
    (htotal : ∀ k, ∑ x ∈ rows, v x k ≤ H) {K : ℕ} (hK : 1 ≤ K) :
    (∑ x ∈ rows, highLogCharge (v x) H K) ≤
      2 * (rows.card : ℝ) * Real.log (Real.exp 1 * (K : ℝ) * H) := by
  calc
    _ ≤ ∑ _x ∈ rows, 2 * Real.log (Real.exp 1 * (K : ℝ) * H) :=
      Finset.sum_le_sum fun x hx => high_log_charge_bound hH (row_visit_bound htotal hx) hK
    _ = _ := by simp; ring

/-- The sum of row prefix counts is bounded by the actual total number of visits. -/
theorem total_before_bound (htotal : ∀ k, ∑ x ∈ rows, v x k ≤ H) (K : ℕ) :
    (∑ x ∈ rows, before (v x) K) ≤ K * H := by
  unfold before
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ _k ∈ Finset.range K, H := Finset.sum_le_sum fun k _ => htotal k
    _ = _ := by simp

/-- Cauchy--Schwarz in exactly the square-root form needed for the row sum. -/
theorem sum_sqrt_le (f : ι → ℝ) (hf : ∀ x ∈ rows, 0 ≤ f x) :
    (∑ x ∈ rows, Real.sqrt (f x)) ≤ Real.sqrt ((rows.card : ℝ) * ∑ x ∈ rows, f x) := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq rows (fun _ => (1 : ℝ))
    (fun x => Real.sqrt (f x))
  have hs : (∑ x ∈ rows, (Real.sqrt (f x))^2) = ∑ x ∈ rows, f x :=
    Finset.sum_congr rfl (fun x hx => Real.sq_sqrt (hf x hx))
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one, hs] at hcs
  exact Real.le_sqrt_of_sq_le hcs

/-- The reward proof's 3 sqrt(S A K H) charging bound (Appendix C). -/
theorem all_rows_sqrt_charge (hH : 0 < H)
    (htotal : ∀ k, ∑ x ∈ rows, v x k ≤ H) (K : ℕ) :
    (∑ x ∈ rows, highSqrtCharge (v x) H K) ≤
      3 * Real.sqrt ((rows.card : ℝ) * (K : ℝ) * H) := by
  have hsum := sum_sqrt_le (rows := rows) (fun x => (before (v x) K : ℝ))
    (fun _ _ => Nat.cast_nonneg _)
  have htotalN := total_before_bound htotal K
  have htotalR : (∑ x ∈ rows, (before (v x) K : ℝ)) ≤ (K : ℝ) * H := by
    exact_mod_cast htotalN
  have hroot := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left htotalR
    (Nat.cast_nonneg rows.card : (0 : ℝ) ≤ rows.card))
  calc
    _ ≤ ∑ x ∈ rows, 3 * Real.sqrt (before (v x) K) :=
      Finset.sum_le_sum fun x hx => high_sqrt_charge_bound hH (row_visit_bound htotal hx) K
    _ = 3 * ∑ x ∈ rows, Real.sqrt (before (v x) K) := by rw [Finset.mul_sum]
    _ ≤ 3 * Real.sqrt ((rows.card : ℝ) * ∑ x ∈ rows, (before (v x) K : ℝ)) := by linarith
    _ ≤ 3 * Real.sqrt ((rows.card : ℝ) * ((K : ℝ) * H)) := by linarith
    _ = _ := by congr 2; ring

/-- The per-episode high count charge is bounded by one, as needed for C.3. -/
theorem high_log_episode_le_one (hH : 0 < H)
    (htotal : ∀ k, ∑ x ∈ rows, v x k ≤ H) (k : ℕ) :
    0 ≤ (∑ x ∈ rows, if H ≤ before (v x) k then (v x k : ℝ) / before (v x) k else 0) ∧
    (∑ x ∈ rows, if H ≤ before (v x) k then (v x k : ℝ) / before (v x) k else 0) ≤ 1 := by
  have hH0 : (0 : ℝ) < H := by exact_mod_cast hH
  constructor
  · exact Finset.sum_nonneg fun _ _ => by split_ifs <;> positivity
  · calc
      _ ≤ ∑ x ∈ rows, (v x k : ℝ) / H := by
        apply Finset.sum_le_sum
        intro x hx
        split_ifs with hxhigh
        · apply div_le_div_of_nonneg_left (Nat.cast_nonneg _) hH0
          exact_mod_cast hxhigh
        · positivity
      _ = (∑ x ∈ rows, (v x k : ℝ)) / H := by simp_rw [div_eq_mul_inv]; rw [Finset.sum_mul]
      _ ≤ 1 := (div_le_one hH0).2 (by exact_mod_cast htotal k)

/-- The low-count episode charge has the H bound required by C.3. -/
theorem low_episode_bounds (htotal : ∀ k, ∑ x ∈ rows, v x k ≤ H) (k : ℕ) :
    0 ≤ (∑ x ∈ rows, if before (v x) k < H then (v x k : ℝ) else 0) ∧
    (∑ x ∈ rows, if before (v x) k < H then (v x k : ℝ) else 0) ≤ H := by
  constructor
  · exact Finset.sum_nonneg fun _ _ => by split_ifs <;> positivity
  · calc
      _ ≤ ∑ x ∈ rows, (v x k : ℝ) := by
        apply Finset.sum_le_sum
        intro x hx
        split_ifs
        · exact le_rfl
        · positivity
      _ ≤ (H : ℝ) := by exact_mod_cast htotal k

end Rows

end
end Paper36.Counts
