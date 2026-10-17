import P31.QueryProgram
import P31.Schedule

/-! Corollary5.2: an actual concatenation of restarted exact-oracle programs.
The base algorithm is an explicit input; the checkpoint composition, transcript
calls and geometric sum are proved here. No future target accuracy is an input
to `checkpointProgram`; it depends only on the scale M and phase index. -/
noncomputable section
namespace P31
open scoped BigOperators
open QueryProgram QueryProgram.Program
universe u v
variable {E : Type u} {G : Type v}

def checkpointProgram (family : ℝ → Program E G E) (x₀ : E) (M : ℝ) : ℕ → Program E G E
  | 0 => .pure x₀
  | n+1 => (checkpointProgram family x₀ M n).bind
      (fun _ => family (M / (2:ℝ)^(n+1)))

@[simp] theorem checkpoint_value_succ (family : ℝ → Program E G E) (x₀ : E) (M : ℝ)
    (n : ℕ) (o : E → G) :
    ((checkpointProgram family x₀ M (n+1)).run o).value =
      ((family (M/(2:ℝ)^(n+1))).run o).value := by simp [checkpointProgram]

/-- Each phase restarts the same base family and every query is charged. -/
theorem checkpoint_calls (family : ℝ → Program E G E) (x₀ : E) (M : ℝ)
    (n : ℕ) (o : E → G) :
    ((checkpointProgram family x₀ M n).run o).calls =
      ∑ k ∈ Finset.range n, ((family (M/(2:ℝ)^(k+1))).run o).calls := by
  induction n with
  | zero => simp [checkpointProgram]
  | succ n ih => simp [checkpointProgram, calls_bind, ih, Finset.sum_range_succ]

lemma growing_geometric_sum_le {t : ℝ} (ht : 1 < t) (n : ℕ) :
    (∑ k ∈ Finset.range n, t^(k+1)) ≤ t / (t-1) * t^n := by
  have hsum : (∑ k ∈ Finset.range n, t^k) * (t-1) = t^n-1 := geom_sum_mul t n
  have hnon : 0 ≤ t := by linarith
  have hden : 0 < t-1 := by linarith
  have he : (∑ k ∈ Finset.range n, t^(k+1)) = t * ∑ k ∈ Finset.range n, t^k := by
    simp_rw [pow_succ, mul_comm _ t]
    rw [Finset.mul_sum]
  rw [he]
  have hb : (∑ k ∈ Finset.range n, t^k) ≤ t^n/(t-1) := by
    apply (le_div_iff₀ hden).2
    linarith
  calc
    t * ∑ k ∈ Finset.range n, t^k ≤ t * (t^n/(t-1)) := mul_le_mul_of_nonneg_left hb hnon
    _ = t/(t-1)*t^n := by ring

/-- Complete phase-sum estimate; its constant depends only on the base
constant C and exponent b. -/
theorem checkpoint_cost_bound {M C b : ℝ} (hM : 0 < M) (hC : 0 ≤ C) (hb : 0 < b)
    (family : ℝ → Program E G E) (x₀ : E) (o : E → G)
    (hcost : ∀ ε, 0 < ε → (((family ε).run o).calls : ℝ) ≤ C*(1+(M/ε)^b))
    (n : ℕ) :
    (((checkpointProgram family x₀ M n).run o).calls : ℝ) ≤
      (2*C*(2:ℝ)^b/((2:ℝ)^b-1)) * (2:ℝ)^((n:ℝ)*b) := by
  let t : ℝ := (2:ℝ)^b
  have ht : 1 < t := Real.one_lt_rpow (by norm_num) hb
  have hphase (k : ℕ) : (((family (M/(2:ℝ)^(k+1))).run o).calls : ℝ) ≤ 2*C*t^(k+1) := by
    have hε : 0 < M/(2:ℝ)^(k+1) := div_pos hM (pow_pos (by norm_num) _)
    have hratio : M/(M/(2:ℝ)^(k+1)) = (2:ℝ)^(k+1) := by field_simp
    have hc := hcost _ hε
    rw [hratio, ← Real.rpow_pow_comm (by norm_num : (0:ℝ) ≤ 2)] at hc
    have hone : 1 ≤ t^(k+1) := one_le_pow₀ ht.le
    dsimp [t] at hone ⊢
    nlinarith [mul_nonneg hC (sub_nonneg.mpr hone)]
  rw [checkpoint_calls, Nat.cast_sum]
  calc
    _ ≤ ∑ k ∈ Finset.range n, 2*C*t^(k+1) := Finset.sum_le_sum (fun k _ => hphase k)
    _ = 2*C*∑ k ∈ Finset.range n, t^(k+1) := by rw [Finset.mul_sum]
    _ ≤ 2*C*(t/(t-1)*t^n) := mul_le_mul_of_nonneg_left (growing_geometric_sum_le ht n) (by positivity)
    _ = (2*C*(2:ℝ)^b/((2:ℝ)^b-1)) * (2:ℝ)^((n:ℝ)*b) := by
      rw [show t^n = (2:ℝ)^((n:ℝ)*b) by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
        congr 1; ring]
      dsimp [t]
      ring

/-- Accuracy and the full accumulated call bound of Corollary5.2. The family
is the already constructed base method; no prescribed epsilon is used by the
wrapper. The bound is for every n>=1 and the same infinite checkpoint family. -/
theorem accuracy_oblivious_checkpoints {M C b : ℝ} (hM : 0 < M) (hC : 0 ≤ C) (hb : 0 < b)
    (family : ℝ → Program E G E) (x₀ : E) (o : E → G) (gradientNorm : E → ℝ)
    (hbase : ∀ ε, 0 < ε →
      gradientNorm (((family ε).run o).value) ≤ ε ∧
      (((family ε).run o).calls : ℝ) ≤ C*(1+(M/ε)^b)) :
    ∀ n, 1 ≤ n →
      gradientNorm (((checkpointProgram family x₀ M n).run o).value) ≤ M/(2:ℝ)^n ∧
      (((checkpointProgram family x₀ M n).run o).calls : ℝ) ≤
        (2*C*(2:ℝ)^b/((2:ℝ)^b-1)) * (2:ℝ)^((n:ℝ)*b) := by
  intro n hn
  constructor
  · rcases n with _ | n
    · omega
    · rw [checkpoint_value_succ]
      exact (hbase _ (div_pos hM (pow_pos (by norm_num) _))).1
  · exact checkpoint_cost_bound hM hC hb family x₀ o (fun ε hε => (hbase ε hε).2) n

/-- Degenerate scale M=0 uses no queries, including at every checkpoint. -/
theorem zero_scale_checkpoints (x₀ : E) (o : E → G) (gradientNorm : E → ℝ)
    (hzero : gradientNorm x₀ = 0) :
    ∀ n : ℕ, gradientNorm (((Program.pure x₀ : Program E G E).run o).value) ≤
      (0:ℝ)/(2:ℝ)^n ∧ ((Program.pure x₀ : Program E G E).run o).calls = 0 := by
  intro n
  simp [hzero]

end P31
