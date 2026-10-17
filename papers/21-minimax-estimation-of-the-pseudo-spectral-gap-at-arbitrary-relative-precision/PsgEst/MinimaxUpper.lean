import PsgEst.GapsOfPowers
import PsgEst.LowerBound

/-!
# The minimax upper-bound reduction

This module proves the last paragraph of Section 4 from the uniform bound of
Theorem 1.  The uniform bound is an explicit hypothesis here; this module does
not assert or postulate the missing concentration theorem.
-/

open Matrix BigOperators Real Classical

namespace PsgEst

variable {d : ℕ} [NeZero d]

/-- The complete, fixed-constant statement of Theorem 1, for one chain. -/
def UniformEstimationBound (S : Stoch d) (st : Stationary S) : Prop :=
  ∀ (n : ℕ) (ε δ : ℝ), 0 < ε → ε < 1 / 2 → 0 < δ → δ < 1 →
    ∀ (mu0 : Fin d → ℝ), (∀ i, 0 ≤ mu0 i) → (∑ i, mu0 i = 1) →
      73728 / (Stationary.star st * gammaPS S st * ε ^ 2) *
        log (8 * (d : ℝ) / (δ * Stationary.star st * gammaPS S st)) ≤ (n : ℝ) →
      pathMeasure S.P mu0 (Finset.univ.filter fun X : Fin (n + 1) → Fin d =>
        ε * gammaPS S st < |gammaHat X - gammaPS S st|) ≤ δ

lemma stationary_star_le_one (S : Stoch d) (st : Stationary S) :
    Stationary.star st ≤ 1 := by
  let i : Fin d := ⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩
  have hi : st.mu i ≤ ∑ j, st.mu j :=
    Finset.single_le_sum (fun j _ => (st.pos j).le) (Finset.mem_univ i)
  exact (st.star_le i).trans (by simpa [st.sum_one] using hi)

omit [NeZero d] in
lemma gammaPS_le_one_of_stationary (S : Stoch d) (st : Stationary S) :
    gammaPS S st ≤ 1 := by
  rw [gammaPS_eq_gapGamma]
  exact gapGamma_le_one _ (fun t => (aK_mem S st t).2)

/-- The product and logarithm comparison used in Section 4. -/
lemma sample_requirement_mono (A x y ε : ℝ)
    (hx : 0 < x) (hxy : x ≤ y) (hy : y ≤ 1) (hA : 1 ≤ A)
    (hε : 0 < ε) :
    73728 / (y * ε ^ 2) * log (A / y) ≤
      73728 / (x * ε ^ 2) * log (A / x) := by
  have hy0 : 0 < y := hx.trans_le hxy
  have he : 0 < ε ^ 2 := sq_pos_of_pos hε
  have hlog0 : 0 ≤ log (A / y) := by
    apply Real.log_nonneg
    exact (le_div_iff₀ hy0).2 (by linarith)
  have hlog : log (A / y) ≤ log (A / x) := by
    apply Real.log_le_log (div_pos (by linarith) hy0)
    exact div_le_div_of_nonneg_left (by linarith) hx hxy
  have hdiv : 73728 / (y * ε ^ 2) ≤ 73728 / (x * ε ^ 2) :=
    div_le_div_of_nonneg_left (by norm_num) (mul_pos hx he)
      (mul_le_mul_of_nonneg_right hxy he.le)
  exact mul_le_mul hdiv hlog hlog0 (by positivity)

omit [NeZero d] in
lemma pathMeasure_success_of_failure {n : ℕ} (S : Stoch d)
    (mu0 : Fin d → ℝ) (hsum : ∑ i, mu0 i = 1)
    (est : (Fin (n + 1) → Fin d) → ℝ) (γ ε δ : ℝ)
    (hfail : pathMeasure S.P mu0
      (Finset.univ.filter fun X => ε * γ < |est X - γ|) ≤ δ) :
    1 - δ ≤ pathMeasure S.P mu0
      (Finset.univ.filter fun X => |est X - γ| ≤ ε * γ) := by
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (s := (Finset.univ : Finset (Fin (n + 1) → Fin d)))
    (p := fun X => |est X - γ| ≤ ε * γ) (f := pathProb S.P mu0)
  simp only [not_le] at hsplit
  change pathMeasure S.P mu0 _ + pathMeasure S.P mu0 _ = _ at hsplit
  rw [pathProb_sum S.P mu0 S.row_stoch, hsum] at hsplit
  linarith

/-- Uniform relative accuracy at the ceiling of the common sample requirement. -/
theorem exists_accurate_of_uniform (hd : 2 ≤ d) (p g ε : ℝ)
    (hp : 0 < p) (_hp' : p ≤ 1 / (d : ℝ)) (hg : 0 < g) (hg' : g ≤ 1 / 8)
    (hε : 0 < ε) (hε' : ε < 1 / 2)
    (hU : ∀ (S : Stoch d) (st : Stationary S),
      p ≤ Stationary.star st → g ≤ gammaPS S st → UniformEstimationBound S st) :
    relativelyAccurate
      (Nat.ceil (73728 / (p * g * ε ^ 2) * log (24 * (d : ℝ) / (p * g))))
      d gammaHat p g ε := by
  let N := Nat.ceil (73728 / (p * g * ε ^ 2) * log (24 * (d : ℝ) / (p * g)))
  intro S st hπ hγ x0
  let mu0 : Fin d → ℝ := fun i => if i = x0 then 1 else 0
  have hmu : ∀ i, 0 ≤ mu0 i := by intro i; dsimp [mu0]; split <;> norm_num
  have hsum : ∑ i, mu0 i = 1 := by simp [mu0]
  have hpγ : 0 < Stationary.star st * gammaPS S st :=
    mul_pos st.star_pos (hg.trans_le hγ)
  have hprod : p * g ≤ Stationary.star st * gammaPS S st :=
    mul_le_mul hπ hγ hg.le st.star_pos.le
  have hprod1 : Stationary.star st * gammaPS S st ≤ 1 := by
    calc
      _ ≤ 1 * 1 := mul_le_mul (stationary_star_le_one S st)
        (gammaPS_le_one_of_stationary S st) (hg.trans_le hγ).le (by norm_num)
      _ = 1 := by ring
  have hreq : 73728 / (Stationary.star st * gammaPS S st * ε ^ 2) *
        log (8 * (d : ℝ) / ((1 / 3 : ℝ) * Stationary.star st * gammaPS S st))
        ≤ (N : ℝ) := by
    have hm := sample_requirement_mono (24 * (d : ℝ)) (p * g)
      (Stationary.star st * gammaPS S st) ε (mul_pos hp hg) hprod hprod1
      (by
        have hdreal : (2 : ℝ) ≤ d := by exact_mod_cast hd
        linarith) hε
    have heq : 8 * (d : ℝ) / ((1 / 3 : ℝ) * Stationary.star st * gammaPS S st) =
        24 * (d : ℝ) / (Stationary.star st * gammaPS S st) := by ring
    rw [heq]
    exact hm.trans (Nat.le_ceil _)
  have hfail := hU S st hπ hγ N ε (1 / 3) hε hε'
    (by norm_num) (by norm_num) mu0 hmu hsum hreq
  have hs := pathMeasure_success_of_failure S mu0 hsum gammaHat
    (gammaPS S st) ε (1 / 3) hfail
  norm_num at hs ⊢
  exact hs

/-- Section 4's ceiling can be absorbed into the universal constant `73729`. -/
theorem minimax_upper_of_uniform (hd : 2 ≤ d) (p g ε : ℝ)
    (hp : 0 < p) (hp' : p ≤ 1 / (d : ℝ)) (hg : 0 < g) (hg' : g ≤ 1 / 8)
    (hε : 0 < ε) (hε' : ε < 1 / 2)
    (hU : ∀ (S : Stoch d) (st : Stationary S),
      p ≤ Stationary.star st → g ≤ gammaPS S st → UniformEstimationBound S st) :
    (nStar d p g ε : ℝ) ≤
      73729 / (p * g * ε ^ 2) * log (24 * (d : ℝ) / (p * g)) := by
  let B := 1 / (p * g * ε ^ 2) * log (24 * (d : ℝ) / (p * g))
  let N := Nat.ceil (73728 * B)
  have hAcc : relativelyAccurate N d gammaHat p g ε := by
    have ha := exists_accurate_of_uniform hd p g ε hp hp' hg hg' hε hε' hU
    convert ha using 1 <;> dsimp [N, B] <;> congr 1 <;> ring
  have hn : nStar d p g ε ≤ N := Nat.sInf_le ⟨gammaHat, hAcc⟩
  have hp1 : p ≤ 1 := by
    have hdpos : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (by omega : 1 ≤ d)
    exact hp'.trans ((div_le_iff₀ hdpos).2 (by linarith))
  have hpg : p * g ≤ 1 := by nlinarith
  have hpg0 : 0 < p * g := mul_pos hp hg
  have hlog : 1 ≤ log (24 * (d : ℝ) / (p * g)) := by
    have harg : 4 ≤ 24 * (d : ℝ) / (p * g) :=
      (le_div_iff₀ hpg0).2 (by
        have hdreal : (2 : ℝ) ≤ d := by exact_mod_cast hd
        nlinarith)
    have hl : 1 ≤ log (4 : ℝ) := by
      have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
      have he := Real.log_pow (2 : ℝ) 2
      norm_num at he
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num at hh ⊢
      linarith
    exact hl.trans (Real.log_le_log (by norm_num) harg)
  have hden : 0 < p * g * ε ^ 2 := mul_pos hpg0 (sq_pos_of_pos hε)
  have hden1 : p * g * ε ^ 2 ≤ 1 := by nlinarith [sq_nonneg ε]
  have hB : 1 ≤ B := by
    dsimp [B]
    have hi : 1 ≤ 1 / (p * g * ε ^ 2) := (le_div_iff₀ hden).2 (by linarith)
    nlinarith
  have hceil : (N : ℝ) ≤ 73728 * B + 1 := (Nat.ceil_lt_add_one (by
    positivity : 0 ≤ 73728 * B)).le
  have hncast : (nStar d p g ε : ℝ) ≤ (N : ℝ) := by exact_mod_cast hn
  calc
    _ ≤ (N : ℝ) := hncast
    _ ≤ 73728 * B + 1 := hceil
    _ ≤ 73729 * B := by linarith
    _ = _ := by dsimp [B]; ring

end PsgEst
