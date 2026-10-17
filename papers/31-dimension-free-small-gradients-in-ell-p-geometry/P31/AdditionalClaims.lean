import P31.NormComparison
import P31.Schedule
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Exact exponent identities and the prefix-norm observation in §§7--9.
No trajectory-sensitive accelerated method is asserted as a new theorem. -/
noncomputable section
open scoped BigOperators
namespace P31

lemma query_exponent_inverse {p κ : ℝ} (hp : 2 ≤ p) (hκ : 1 < κ) :
    1 / Schedule.beta p κ = κ-1+κ/p := by
  have hp0 : p ≠ 0 := ne_of_gt (show 0 < p by linarith)
  have hd := ne_of_gt (Schedule.deltaDenom_pos hp hκ)
  unfold Schedule.beta Schedule.deltaDenom
  field_simp; ring

lemma smooth_query_exponent {p : ℝ} : Schedule.beta p 2 = p/(p+2) := by
  unfold Schedule.beta Schedule.deltaDenom
  congr 1
  ring

lemma hilbert_gradient_decay (κ : ℝ) : κ-1+κ/(2:ℝ) = (3*κ-2)/2 := by ring
lemma smooth_gradient_decay {p : ℝ} (hp : p ≠ 0) : 2-1+2/p = (p+2)/p := by field_simp; ring

/-- The exponent gain is strict outside the unique Hilbert smooth corner. -/
theorem one_shot_exponent_eq_iff {p κ : ℝ} (hp : 2 ≤ p) (hκ : 1 < κ) (hκhi : κ ≤ 2) :
    Schedule.gamma p κ = Schedule.beta p κ ↔ p=2 ∧ κ=2 := by
  have hgap := Schedule.gamma_sub_beta hp hκ
  have hden : (κ-1)*Schedule.deltaDenom p κ ≠ 0 :=
    ne_of_gt (mul_pos (sub_pos.mpr hκ) (Schedule.deltaDenom_pos hp hκ))
  constructor
  · intro heq
    rw [heq, sub_self] at hgap
    have hpk := (div_eq_zero_iff.mp hgap.symm).resolve_right hden
    constructor <;> linarith
  · rintro ⟨rfl,rfl⟩
    norm_num [Schedule.gamma, Schedule.beta, Schedule.deltaDenom]

/-- The real-p limit stated in §9; this is a limit of exponents, not a claim
that the hidden p-dependent complexity constants remain bounded. -/
theorem gradient_decay_limit (κ : ℝ) :
    Filter.Tendsto (fun p : ℝ => κ-1+κ/p) Filter.atTop (nhds (κ-1)) := by
  have hc : Filter.Tendsto (fun _ : ℝ => κ-1) Filter.atTop (nhds (κ-1)) := tendsto_const_nhds
  have hd : Filter.Tendsto (fun p : ℝ => κ/p) Filter.atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop Filter.tendsto_id
  simpa using hc.add hd

variable {ι : Type*} [Fintype ι]

lemma lpNorm_pos_of_ne_zero {p : ℝ} (hp : 0 < p) {v : ι → ℝ} (hv : v ≠ 0) : 0 < lpNorm p v := by
  classical
  have hex : ∃ i, v i ≠ 0 := by
    by_contra h
    push_neg at h
    apply hv
    funext i
    exact h i
  obtain ⟨i, hi⟩ := hex
  exact lt_of_lt_of_le (abs_pos.mpr hi) (abs_coordinate_le_lpNorm hp v i)

def prefixGain (q : ℝ) (g : ℕ → ι → ℝ) (n : ℕ) : ℝ :=
  (∑ j ∈ Finset.range n, lpNorm q (g (j+1))/lpNorm 2 (g (j+1))) / n

/-- The always-valid prefix bound Ghat=1 in §8 follows from actual lp norm
monotonicity on every nonzero-gradient prefix. -/
theorem prefixGain_ge_one {q : ℝ} (hq : 0 < q) (hq2 : q ≤ 2)
    (g : ℕ → ι → ℝ) (n : ℕ) (hn : 0 < n)
    (hnonzero : ∀ j, j < n → g (j+1) ≠ 0) : 1 ≤ prefixGain q g n := by
  have hcast : (0:ℝ) < n := Nat.cast_pos.mpr hn
  apply (le_div_iff₀ hcast).2
  have hs := Finset.sum_le_sum (s := Finset.range n) (fun j hj =>
    (one_le_div (lpNorm_pos_of_ne_zero (by norm_num) (hnonzero j (Finset.mem_range.mp hj)))).2
      (lpNorm_antitone_exponent hq hq2 (g (j+1))))
  simpa using hs

lemma lpNorm_single {p : ℝ} (hp : 0 < p) [DecidableEq ι] (i : ι) (t : ℝ) :
    lpNorm p (Pi.single i t) = |t| := by
  have hsum : lpPower p (Pi.single i t) = |t|^p := by
    unfold lpPower
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      simp [Pi.single_eq_of_ne hji, Real.zero_rpow hp.ne']
    · simp
  rw [lpNorm, hsum, ← Real.rpow_mul (abs_nonneg _), mul_one_div_cancel hp.ne', Real.rpow_one]

/-- The prefix norm ratio can remain exactly one in arbitrarily large
ambient dimension for coordinate-supported nonzero vectors. -/
theorem coordinate_supported_prefixGain {q : ℝ} (hq : 0 < q) [DecidableEq ι]
    (i : ι) (t : ℕ → ℝ) (n : ℕ) (hn : 0 < n)
    (ht : ∀ j, j < n → t (j+1) ≠ 0) :
    prefixGain q (fun j => Pi.single i (t j)) n = 1 := by
  unfold prefixGain
  have hs : (∑ j ∈ Finset.range n,
      lpNorm q (Pi.single i (t (j+1)))/lpNorm 2 (Pi.single i (t (j+1)))) = n := by
    calc
      _ = ∑ _j ∈ Finset.range n, (1:ℝ) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [lpNorm_single hq, lpNorm_single (by norm_num), div_self
          (abs_ne_zero.mpr (ht j (Finset.mem_range.mp hj)))]
      _ = _ := by simp
  rw [hs, div_self (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn))]

end P31
