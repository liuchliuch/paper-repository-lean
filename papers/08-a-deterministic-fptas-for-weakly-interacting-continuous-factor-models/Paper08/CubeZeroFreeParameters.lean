import Paper08.FPTAS
import Paper08.ComplexSector

/-! # Original weak-interaction parameters for the finite-cube induction

These are only numerical consequences of the original parameter promises.
No nonvanishing or algorithmic conclusion is an input.
-/
namespace Paper08.CubeZeroFreeParameters

lemma denominator_pos (p : FPTAS.Params) :
    0 < 3*(p.c:ℝ)*Real.sqrt ((p.r:ℝ)-1)*p.q := by
  have hc : (0:ℝ) < p.c := by exact_mod_cast (show 0 < p.c by have := p.c_ge; omega)
  exact mul_pos (mul_pos (mul_pos (by norm_num) hc) (FPTAS.sqrt_r_sub_one_pos p)) p.q_pos

/-- The original closed β-disk satisfies the induction's coordinate budget. -/
lemma coordinate_budget (p : FPTAS.Params) {z : ℂ} (hz : ‖z‖ ≤ FPTAS.beta p) :
    (p.c:ℝ)*‖z‖*p.q ≤ 1/(3*Real.sqrt ((p.r:ℝ)-1)) := by
  have hd := denominator_pos p
  have hs := FPTAS.sqrt_r_sub_one_pos p
  have hb : ‖z‖*(3*(p.c:ℝ)*Real.sqrt ((p.r:ℝ)-1)*p.q) ≤ 1 :=
    (le_div_iff₀ hd).mp hz
  apply (le_div_iff₀ (mul_pos (by norm_num : (0:ℝ)<3) hs)).mpr
  convert hb using 1 <;> ring

lemma index_cast (p : FPTAS.Params) : ((p.r-1:ℕ):ℝ) = (p.r:ℝ)-1 := by
  rw [Nat.cast_sub (show 1 ≤ p.r by have := p.r_ge; omega)]
  norm_num

lemma sqrt_index_pos (p : FPTAS.Params) : 0 < Real.sqrt ((p.r-1:ℕ):ℝ) := by
  rw [index_cast]
  exact FPTAS.sqrt_r_sub_one_pos p

/-- The actual original closed disk leaves a strict one-third margin in the
phase-induction budget. -/
lemma induction_budget (p : FPTAS.Params) {z : ℂ} (hz : ‖z‖ ≤ FPTAS.beta p) :
    2*(p.c:ℝ)*‖z‖*p.q ≤ ComplexSector.angle (p.r-1) := by
  have hs := FPTAS.sqrt_r_sub_one_pos p
  have hb := (le_div_iff₀ (mul_pos (by norm_num : (0:ℝ)<3) hs)).mp (coordinate_budget p hz)
  unfold ComplexSector.angle
  rw [index_cast]
  apply (le_div_iff₀ hs).mpr
  have hn : 0 ≤ (p.c:ℝ)*‖z‖*p.q*Real.sqrt ((p.r:ℝ)-1) :=
    mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)) p.q_pos.le) hs.le
  nlinarith

end Paper08.CubeZeroFreeParameters
