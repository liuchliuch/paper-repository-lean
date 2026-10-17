import PsgEst.NormIdentity
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Exponential contraction and entrywise mixing

Appendix A, equation (27), and the entrywise consequence used to choose the
thinning lag in Lemma 2. All bounds include time zero and the endpoint where a
maximizing singular-value deficit is one.
-/

open Matrix BigOperators Real

namespace PsgEst

variable {d : ℕ}

/-- Divide time into complete blocks of length `k0` and a final remainder. -/
theorem bNorm_sq_le_block_pow [DecidableEq (Fin d)] (S : Stoch d)
    (st : Stationary S) (k0 t : ℕ) :
    bNorm S st t ^ 2 ≤ (1 - aK S st k0) ^ (t / k0) := by
  let q := t / k0
  let r := t % k0
  have htime : q * k0 + r = t := by
    simpa only [q, r, Nat.mul_comm] using Nat.div_add_mod t k0
  have hb := bNorm_mul S st (q * k0) r
  rw [htime] at hb
  have hp : bNorm S st (q * k0) ≤ bNorm S st k0 ^ q :=
    gapB_pow (aK_gapAx S st) k0 q
  have hbp : bNorm S st t ≤ bNorm S st k0 ^ q := by
    calc
      _ ≤ bNorm S st (q * k0) * bNorm S st r := hb
      _ ≤ bNorm S st (q * k0) * 1 :=
        mul_le_mul_of_nonneg_left (bNorm_mem S st r).2 (bNorm_nonneg S st _)
      _ ≤ bNorm S st k0 ^ q := by simpa only [mul_one] using hp
  have hsq := (sq_le_sq₀ (bNorm_nonneg S st t)
    (pow_nonneg (bNorm_nonneg S st k0) q)).2 hbp
  have hbase : bNorm S st k0 ^ 2 = 1 - aK S st k0 :=
    gapB_sq (aK_gapAx S st).le_one k0
  calc
    _ ≤ (bNorm S st k0 ^ q) ^ 2 := hsq
    _ = (bNorm S st k0 ^ 2) ^ q := by rw [← pow_mul, ← pow_mul, Nat.mul_comm q 2]
    _ = _ := by rw [hbase]

/-- Equation (27): a maximizing lag gives a uniform exponential contraction. -/
theorem bNorm_sq_le_exp [DecidableEq (Fin d)] (S : Stoch d)
    (st : Stationary S) (hgap : 0 < gammaPS S st) (t : ℕ) :
    bNorm S st t ^ 2 ≤ exp (1 - gammaPS S st * (t : ℝ)) := by
  obtain ⟨k0, hk0, hmax, _⟩ := exists_max_lag S st hgap
  have hkreal : (k0 : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk0)
  have ha : aK S st k0 = gammaPS S st * (k0 : ℝ) :=
    (div_eq_iff hkreal).mp hmax
  have hfloor : (t : ℝ) ≤ ((t / k0 : ℕ) : ℝ) * (k0 : ℝ) + (k0 : ℝ) := by
    have hnat : t ≤ (t / k0) * k0 + k0 := by
      have hm := Nat.mod_lt t hk0
      have he : (t / k0) * k0 + t % k0 = t := by
        simpa only [Nat.mul_comm] using Nat.div_add_mod t k0
      omega
    exact_mod_cast hnat
  have hexp : ((t / k0 : ℕ) : ℝ) * (-aK S st k0) ≤
      1 - gammaPS S st * (t : ℝ) := by
    have ht := mul_le_mul_of_nonneg_left hfloor hgap.le
    have he : gammaPS S st * (((t / k0 : ℕ) : ℝ) * (k0 : ℝ) + (k0 : ℝ)) =
        ((t / k0 : ℕ) : ℝ) * aK S st k0 + aK S st k0 := by rw [ha]; ring
    rw [he] at ht
    linarith [(aK_mem S st k0).2]
  calc
    _ ≤ (1 - aK S st k0) ^ (t / k0) := bNorm_sq_le_block_pow S st k0 t
    _ ≤ exp (-aK S st k0) ^ (t / k0) :=
      pow_le_pow_left₀ (sub_nonneg.mpr (aK_mem S st k0).2)
        (Real.one_sub_le_exp_neg _) _
    _ = exp (((t / k0 : ℕ) : ℝ) * (-aK S st k0)) := (Real.exp_nat_mul _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr hexp

/-- The unsquared form of equation (27). -/
theorem bNorm_le_exp_half [DecidableEq (Fin d)] (S : Stoch d)
    (st : Stationary S) (hgap : 0 < gammaPS S st) (t : ℕ) :
    bNorm S st t ≤ exp ((1 - gammaPS S st * (t : ℝ)) / 2) := by
  apply (sq_le_sq₀ (bNorm_nonneg S st t) (Real.exp_pos _).le).mp
  have he : exp ((1 - gammaPS S st * (t : ℝ)) / 2) ^ 2 =
      exp (1 - gammaPS S st * (t : ℝ)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [he]
  exact bNorm_sq_le_exp S st hgap t

/-- The first inequality in equation (27), expressed with the paper's actual
weighted operator norm of `P^t - Π`. -/
theorem weighted_centered_norm_sq_le_block_pow [DecidableEq (Fin d)]
    (S : Stoch d) (st : Stationary S) (k0 t : ℕ) :
    weightedOperatorNorm st.mu ((S.pow t).P - piMat st.mu) ^ 2 ≤
      (1 - aK S st k0) ^ (t / k0) := by
  rw [← bNorm_eq_weightedOperatorNorm]
  exact bNorm_sq_le_block_pow S st k0 t

/-- The exponential conclusion of equation (27) for the actual centered
transition operator, including time zero. -/
theorem weighted_centered_norm_sq_le_exp [DecidableEq (Fin d)]
    (S : Stoch d) (st : Stationary S) (hgap : 0 < gammaPS S st) (t : ℕ) :
    weightedOperatorNorm st.mu ((S.pow t).P - piMat st.mu) ^ 2 ≤
      exp (1 - gammaPS S st * (t : ℝ)) := by
  rw [← bNorm_eq_weightedOperatorNorm]
  exact bNorm_sq_le_exp S st hgap t

/-- The centered entry is the relative transition error multiplied by the two
stationary square roots. `S.pow` is the actual matrix power from `Basic`. -/
theorem LkSub_entry_factor [DecidableEq (Fin d)] (S : Stoch d)
    (st : Stationary S) (t : ℕ) (i j : Fin d) :
    LkSub S st t i j = (stVec st i * stVec st j) *
      ((S.pow t).P i j / st.mu j - 1) := by
  simp only [LkSub, Matrix.sub_apply, Lk, simil, Matrix.mul_diagonal,
    Matrix.diagonal_mul, piProj]
  rw [Real.rpow_neg (st.pos j).le]
  change stVec st i * (S.pow t).P i j * (stVec st j)⁻¹ -
    stVec st i * stVec st j = _
  have hj : st.mu j = (stVec st j) ^ 2 := by
    simpa only [pow_two] using (stVec_sq st j).symm
  rw [hj]
  field_simp [ne_of_gt (stVec_pos st j)]

/-- Uniform relative-entry bound from the centered operator norm. -/
theorem relative_entry_abs_le_bNorm [DecidableEq (Fin d)] [NeZero d]
    (S : Stoch d) (st : Stationary S) (t : ℕ) (i j : Fin d) :
    |(S.pow t).P i j / st.mu j - 1| ≤ (Stationary.star st)⁻¹ * bNorm S st t := by
  have hp := Stationary.star_pos st
  have hprod : 0 ≤ stVec st i * stVec st j :=
    mul_nonneg (stVec_nonneg st i) (stVec_nonneg st j)
  have hroot : Stationary.star st ≤ stVec st i * stVec st j := by
    apply (sq_le_sq₀ hp.le hprod).mp
    calc
      _ = Stationary.star st * Stationary.star st := pow_two _
      _ ≤ st.mu i * st.mu j :=
        mul_le_mul (Stationary.star_le st i) (Stationary.star_le st j) hp.le (st.pos i).le
      _ = (stVec st i * stVec st i) * (stVec st j * stVec st j) := by
        rw [stVec_sq, stVec_sq]
      _ = _ := by ring
  have hh := LkSub_entry_abs_le_bNorm S st t i j
  rw [LkSub_entry_factor, abs_mul, abs_of_nonneg hprod] at hh
  have hs : |(S.pow t).P i j / st.mu j - 1| * Stationary.star st ≤ bNorm S st t := by
    calc
      _ ≤ |(S.pow t).P i j / st.mu j - 1| * (stVec st i * stVec st j) :=
        mul_le_mul_of_nonneg_left hroot (abs_nonneg _)
      _ ≤ _ := by simpa only [mul_comm] using hh
  have hd := (le_div_iff₀ hp).mpr hs
  simpa only [div_eq_mul_inv, mul_comm] using hd

/-- Appendix A's entrywise exponential estimate, valid from time zero. -/
theorem relative_entry_abs_le_exp [DecidableEq (Fin d)] [NeZero d]
    (S : Stoch d) (st : Stationary S) (hgap : 0 < gammaPS S st)
    (t : ℕ) (i j : Fin d) :
    |(S.pow t).P i j / st.mu j - 1| ≤
      (Stationary.star st)⁻¹ * exp ((1 - gammaPS S st * (t : ℝ)) / 2) := by
  exact (relative_entry_abs_le_bNorm S st t i j).trans
    (mul_le_mul_of_nonneg_left (bNorm_le_exp_half S st hgap t)
      (inv_nonneg.mpr (Stationary.star_pos st).le))

/-- The explicit thinning lag in Appendix A. -/
noncomputable def mixingLag [DecidableEq (Fin d)] [NeZero d]
    (S : Stoch d) (st : Stationary S) (η : ℝ) : ℕ :=
  ⌈(1 + 2 * log (4 / (η * Stationary.star st))) / gammaPS S st⌉₊

/-- The ceiling in the thinning lag makes its exponential error at most `η/4`. -/
theorem mixingLag_exp_bound [DecidableEq (Fin d)] [NeZero d]
    (S : Stoch d) (st : Stationary S) (hgap : 0 < gammaPS S st)
    (η : ℝ) (hη : 0 < η) :
    (Stationary.star st)⁻¹ *
      exp ((1 - gammaPS S st * (mixingLag S st η : ℝ)) / 2) ≤ η / 4 := by
  have hp := Stationary.star_pos st
  have hceil : (1 + 2 * log (4 / (η * Stationary.star st))) / gammaPS S st ≤
      (mixingLag S st η : ℝ) := Nat.le_ceil _
  have htime := (div_le_iff₀ hgap).mp hceil
  have harg : 0 < 4 / (η * Stationary.star st) := div_pos (by norm_num) (mul_pos hη hp)
  have he : exp ((1 - gammaPS S st * (mixingLag S st η : ℝ)) / 2) ≤
      η * Stationary.star st / 4 := by
    calc
      _ ≤ exp (-log (4 / (η * Stationary.star st))) :=
        Real.exp_le_exp.mpr (by linarith)
      _ = _ := by
        rw [Real.exp_neg, Real.exp_log harg, inv_div]
  calc
    _ ≤ (Stationary.star st)⁻¹ * (η * Stationary.star st / 4) :=
      mul_le_mul_of_nonneg_left he (inv_nonneg.mpr hp.le)
    _ = _ := by field_simp

/-- Every entry of the thinned transition kernel lies within relative `η/4`
of its stationary mass. The estimate itself holds for every `η > 0`. -/
theorem mixingLag_entry_bounds [DecidableEq (Fin d)] [NeZero d]
    (S : Stoch d) (st : Stationary S) (hgap : 0 < gammaPS S st)
    (η : ℝ) (hη : 0 < η) (i j : Fin d) :
    (1 - η / 4) * st.mu j ≤ (S.pow (mixingLag S st η)).P i j ∧
      (S.pow (mixingLag S st η)).P i j ≤ (1 + η / 4) * st.mu j := by
  have he := (relative_entry_abs_le_exp S st hgap (mixingLag S st η) i j).trans
    (mixingLag_exp_bound S st hgap η hη)
  have hh := abs_le.mp he
  constructor
  · apply (le_div_iff₀ (st.pos j)).mp
    linarith [hh.1]
  · apply (div_le_iff₀ (st.pos j)).mp
    linarith [hh.2]

private lemma mixing_star_le_one [NeZero d] (S : Stoch d) (st : Stationary S) :
    Stationary.star st ≤ 1 := by
  let i : Fin d := ⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩
  have hi : st.mu i ≤ ∑ j, st.mu j :=
    Finset.single_le_sum (fun j _ => (st.pos j).le) (Finset.mem_univ i)
  exact (st.star_le i).trans (by simpa only [st.sum_one] using hi)

/-- In the parameter range of Lemma 2 the thinning lag is positive. -/
theorem mixingLag_pos [DecidableEq (Fin d)] [NeZero d]
    (S : Stoch d) (st : Stationary S) (hgap : 0 < gammaPS S st)
    (η : ℝ) (hη : 0 < η) (hη' : η ≤ 1 / 4) :
    0 < mixingLag S st η := by
  have hp := Stationary.star_pos st
  have hηp : η * Stationary.star st ≤ 1 / 4 := by
    have hh := mul_le_mul_of_nonneg_left (mixing_star_le_one S st) hη.le
    linarith
  have harg : 1 ≤ 4 / (η * Stationary.star st) := by
    apply (le_div_iff₀ (mul_pos hη hp)).mpr
    linarith
  have hlog := Real.log_nonneg harg
  apply Nat.ceil_pos.mpr
  exact div_pos (by linarith) hgap

end PsgEst
