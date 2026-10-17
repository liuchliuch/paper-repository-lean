import Paper09.IslandScale
import Paper09.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

open Real Filter
open scoped Topology
noncomputable section
namespace Paper09
namespace RareScale

/-- The lower-bound scale before the `d`th root. -/
def base (n : ℝ) : ℝ := log n / log (log n)

/-- The target size of a rare weak-field box. -/
def radius (γ : ℝ) (d : ℕ) (n : ℝ) : ℝ := (γ * base n) ^ (d : ℝ)⁻¹

theorem base_tendsto : Tendsto base atTop atTop := by
  have h := (tendsto_exp_div_rpow_atTop 1).comp tendsto_loglog_atTop
  apply h.congr'
  filter_upwards [eventually_ge_atTop (3 : ℝ)] with n hn
  dsimp [base]
  rw [Real.rpow_one, Real.exp_log (by linarith [one_lt_log_of_three_le hn])]

theorem radius_tendsto {γ : ℝ} (hγ : 0 < γ) {d : ℕ} (hd : 0 < d) :
    Tendsto (radius γ d) atTop atTop := by
  exact (tendsto_rpow_atTop (by positivity : 0 < (d : ℝ)⁻¹)).comp
    (base_tendsto.const_mul_atTop hγ)

/-- The radius has exactly the intended volume. -/
lemma radius_pow {γ n : ℝ} {d : ℕ} (hbase : 0 ≤ γ * base n) (hd : 0 < d) :
    radius γ d n ^ d = γ * base n := by
  exact Real.rpow_inv_natCast_pow hbase (by omega)

/-- The target radius is smaller than `log n` eventually. -/
theorem radius_le_log {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    {d : ℕ} (hd : 1 ≤ d) :
    ∀ᶠ n : ℝ in atTop, 0 < base n ∧ 1 ≤ radius γ d n ∧ radius γ d n ≤ log n := by
  have hrad := (radius_tendsto hγ (by omega : 0 < d)).eventually (eventually_ge_atTop 1)
  filter_upwards [eventually_ge_atTop (Real.exp (Real.exp 1)), hrad] with n hn hr
  have hnpos : 0 < n := (Real.exp_pos _).trans_le hn
  have hln : Real.exp 1 ≤ log n := (Real.le_log_iff_exp_le hnpos).mpr hn
  have hll : 1 ≤ log (log n) := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hln
  have hlnpos : 0 < log n := (Real.exp_pos 1).trans_le hln
  have hb : 0 < base n := div_pos hlnpos (by linarith)
  refine ⟨hb, hr, ?_⟩
  have hpow : radius γ d n ≤ radius γ d n ^ d := by
    simpa using pow_le_pow_right₀ hr hd
  rw [radius_pow (mul_nonneg hγ.le hb.le) (by omega)] at hpow
  have hbase : base n ≤ log n := div_le_self hlnpos.le hll
  exact hpow.trans ((mul_le_of_le_one_left hb.le hγ1).trans hbase)

/-- Logarithmic box sizes permit at least `sqrt n` packed positions in each
coordinate. The floor in the actual candidate definition is retained. -/
theorem packing_sqrt : ∀ᶠ n : ℕ in atTop, ∀ m : ℕ,
    (m : ℝ) ≤ log n → Real.sqrt n ≤ (n / (m + 2) : ℕ) := by
  have hlog : Tendsto (fun n : ℝ => log n / n ^ (1/2 : ℝ)) atTop (𝓝 0) :=
    (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1/2)).tendsto_div_nhds_zero
  have hc : Tendsto (fun n : ℝ => 2 / n ^ (1/2 : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1/2))
  have he : ∀ᶠ n : ℝ in atTop, (log n + 2) / Real.sqrt n ≤ 1/2 := by
    have hh := (hlog.add hc).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) + 0 < 1/2))
    filter_upwards [hh] with n hn
    simpa only [← add_div, Real.sqrt_eq_rpow] using hn.le
  filter_upwards [tendsto_natCast_atTop_atTop.eventually he, eventually_ge_atTop (1 : ℕ)] with n hn hn1
  intro m hm
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnpos
  have hs1 : 1 ≤ Real.sqrt n := (Real.le_sqrt (by norm_num) hnpos.le).mpr (by exact_mod_cast hn1)
  have hden : (m : ℝ) + 2 ≤ Real.sqrt n / 2 := by
    have hh := (div_le_iff₀ hs).mp hn
    linarith
  have hdiv : n < (n / (m+2) + 1) * (m+2) := by simpa [Nat.mul_comm] using Nat.lt_mul_div_succ n (show 0 < m+2 by omega)
  have hdiv' : (n : ℝ) < ((n / (m+2) : ℕ) + 1) * ((m : ℝ)+2) := by exact_mod_cast hdiv
  have hmul := mul_le_mul_of_nonneg_left hden
    (show 0 ≤ ((n / (m+2) : ℕ) : ℝ) + 1 by positivity)
  nlinarith [Real.sq_sqrt hnpos.le]

/-- A simple volume-and-log cost bound below the target radius. -/
lemma cost_le {γ C n : ℝ} {d m : ℕ} (hγ : 0 < γ) (hC : 0 ≤ C)
    (hd : 0 < d) (hm : 1 ≤ m) (hll : 0 < log (log n))
    (hb : 0 < base n) (hmr : (m : ℝ) ≤ radius γ d n)
    (hrlog : radius γ d n ≤ log n) :
    C * (m : ℝ) ^ d * log m ≤ C * γ * log n := by
  have hmreal : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hmp : (0 : ℝ) < m := by linarith
  have hvol := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ m) hmr d
  rw [radius_pow (mul_nonneg hγ.le hb.le) hd] at hvol
  have hlog : log m ≤ log (log n) := Real.log_le_log hmp (hmr.trans hrlog)
  have hlogpos : 0 ≤ log m := Real.log_nonneg hmreal
  have h1 := mul_le_mul hvol hlog hlogpos (mul_nonneg hγ.le hb.le)
  have h2 := mul_le_mul_of_nonneg_left h1 hC
  dsimp [base] at h2
  have heq : C * (γ * (log n / log (log n)) * log (log n)) = C * γ * log n := by
    field_simp
  convert h2 using 1 <;> nlinarith [heq]

/-- The surface barrier on a dense-sequence box retains the Griffiths power. -/
lemma barrier_le {γ n : ℝ} {d m : ℕ} (hγ : 0 < γ) (hd : 1 ≤ d)
    (hb : 0 < base n) (hmr : radius γ d n < 2 * m) :
    γ ^ exponentA d / 2 ^ (d-1) * (base n) ^ exponentA d ≤ (m : ℝ) ^ (d-1) := by
  have hr : 0 ≤ radius γ d n := by unfold radius; positivity
  have hm : 0 ≤ (m : ℝ) := by positivity
  have hle : radius γ d n / 2 ≤ (m : ℝ) := by linarith
  have hp := pow_le_pow_left₀ (div_nonneg hr (by norm_num)) hle (d-1)
  have hexp : (d : ℝ)⁻¹ * ((d-1 : ℕ) : ℝ) = exponentA d := by
    have hdreal : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
    rw [Nat.cast_sub hd, Nat.cast_one]
    unfold exponentA
    field_simp
  have hrpow : radius γ d n ^ (d-1) = γ ^ exponentA d * (base n) ^ exponentA d := by
    unfold radius
    rw [← Real.rpow_mul_natCast (mul_nonneg hγ.le hb.le), hexp,
      Real.mul_rpow hγ.le hb.le]
  rw [div_pow, hrpow] at hp
  convert hp using 1 <;> ring

/-- The explicit error bound used by the lower-bound event tends to zero. -/
theorem failure_tendsto (d : ℕ) (hd : 0 < d) :
    Tendsto (fun n : ℕ => exp (-exp ((d : ℝ)/4 * log n))) atTop (𝓝 0) := by
  have hlog := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hinner := Real.tendsto_exp_atTop.comp (hlog.const_mul_atTop (by positivity : 0 < (d : ℝ)/4))
  exact Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hinner)

end RareScale
end Paper09
