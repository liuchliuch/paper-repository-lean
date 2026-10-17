import PsgEst.NormIdentity
import PsgEst.Concentration
import PsgEst.ExponentialRemainder

/-!
# Finite-dimensional tilted-operator estimate for corrected Paulin Bernstein

The proof uses the Gram contraction on the complement of the stationary vector
and a finite rank-one Schur bound. It does not assume an MGF or Bernstein bound.
-/

open Matrix BigOperators Real Finset
namespace PsgEst

/-- Multiplication by the actual exponential tilt. -/
noncomputable def paulinTilt {d : ℕ} (f : Fin d → ℝ) (θ : ℝ) :
    Matrix (Fin d) (Fin d) ℝ := diagonal (fun i => exp (θ * f i))

private lemma paulin_projection_sum_sq {ι : Type*} [Fintype ι]
    (v x : ι → ℝ) (c : ℝ) (hv : ∑ i, v i * v i = 1)
    (hc : ∑ i, x i * v i = c) :
    ∑ i, (x i - c * v i) ^ 2 = (∑ i, x i ^ 2) - c ^ 2 := by
  calc
    _ = (∑ i, x i ^ 2) - 2 * c * (∑ i, x i * v i) +
        c ^ 2 * ∑ i, v i * v i := by
      simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by rw [hc, hv]; ring

/-- The actual Gram operator is bounded by `(1-g)I + g vvᵀ`, with
`g = aK S st k` and the original sorted singular-value definition. -/
theorem paulin_gram_projection_bound {d : ℕ} [DecidableEq (Fin d)]
    (S : Stoch d) (st : Stationary S) (k : ℕ) (hd : 1 < d) (x : Fin d → ℝ) :
    ∑ i, (Lk S st k *ᵥ x) i ^ 2 ≤
      (1 - aK S st k) * ∑ i, x i ^ 2 +
        aK S st k * (∑ i, stVec st i * x i) ^ 2 := by
  classical
  let c : ℝ := ∑ i, stVec st i * x i
  let y : Fin d → ℝ := x - c • stVec st
  have hxy : ∑ i, x i * stVec st i = c := by
    dsimp [c]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hyorth : ∑ i, y i * stVec st i = 0 := by
    calc
      _ = (∑ i, x i * stVec st i) - c * ∑ i, stVec st i * stVec st i := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i _
        simp only [y, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        ring
      _ = 0 := by rw [hxy, stVec_sq_sum]; ring
  have hynorm : ∑ i, y i ^ 2 = (∑ i, x i ^ 2) - c ^ 2 :=
    paulin_projection_sum_sq (stVec st) x c (stVec_sq_sum st) hxy
  have hdotL : ∑ i, (Lk S st k *ᵥ x) i * stVec st i = c := by
    change (Lk S st k *ᵥ x) ⬝ᵥ stVec st = c
    rw [dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose,
      Lk_transpose_mulVec_stVec]
    rfl
  have hLy : Lk S st k *ᵥ y = Lk S st k *ᵥ x - c • stVec st := by
    dsimp only [y]
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul, Lk_mulVec_stVec]
  have hLnorm : ∑ i, (Lk S st k *ᵥ y) i ^ 2 =
      (∑ i, (Lk S st k *ᵥ x) i ^ 2) - c ^ 2 := by
    rw [hLy]
    exact paulin_projection_sum_sq (stVec st) (Lk S st k *ᵥ x) c
      (stVec_sq_sum st) hdotL
  have hb := sigma2_bound_fixed (Lk S st k) (stVec st) hd (stVec_sq_sum st)
    (Lk_mulVec_stVec S st k) (Lk_transpose_mulVec_stVec S st k)
    (Lk_contraction S st k) y hyorth
  rw [hynorm, hLnorm] at hb
  calc
    _ ≤ sigma2 (Lk S st k) ^ 2 * ((∑ i, x i ^ 2) - c ^ 2) + c ^ 2 := by
      linarith
    _ = _ := by dsimp [c, aK, aOf]; ring

/-- Rank-one Schur-complement quadratic bound. The resolvent condition is the
only additional scalar condition; there is no assumption on an operator norm. -/
theorem paulin_rankOne_schur_bound {ι : Type*} [Fintype ι]
    (g R : ℝ) (diag v x : ι → ℝ)
    (hg0 : 0 ≤ g) (_hg1 : g ≤ 1) (_hR : 0 < R)
    (hpos : ∀ i, 0 < R - (1 - g) * diag i ^ 2)
    (hres : g * (∑ i, (v i ^ 2 * diag i ^ 2) /
      (R - (1 - g) * diag i ^ 2)) ≤ 1) :
    (1 - g) * (∑ i, (diag i * x i) ^ 2) +
      g * (∑ i, v i * diag i * x i) ^ 2 ≤ R * ∑ i, x i ^ 2 := by
  classical
  let h : ι → ℝ := fun i => R - (1 - g) * diag i ^ 2
  have hhpos (i : ι) : 0 < h i := hpos i
  have hH : 0 ≤ ∑ i, h i * x i ^ 2 :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hhpos i).le (sq_nonneg _)
  have hcs : (∑ i, v i * diag i * x i) ^ 2 ≤
      (∑ i, (v i ^ 2 * diag i ^ 2) / h i) * ∑ i, h i * x i ^ 2 := by
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul
      (Finset.univ : Finset ι)
    · intro i _
      exact div_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (hhpos i).le
    · intro i _
      exact mul_nonneg (hhpos i).le (sq_nonneg _)
    · intro i _
      have hz : h i ≠ 0 := ne_of_gt (hhpos i)
      field_simp [hz]
  have hcross : g * (∑ i, v i * diag i * x i) ^ 2 ≤ ∑ i, h i * x i ^ 2 := by
    calc
      _ ≤ g * ((∑ i, (v i ^ 2 * diag i ^ 2) / h i) * ∑ i, h i * x i ^ 2) :=
        mul_le_mul_of_nonneg_left hcs hg0
      _ = (g * ∑ i, (v i ^ 2 * diag i ^ 2) / h i) * ∑ i, h i * x i ^ 2 := by ring
      _ ≤ 1 * ∑ i, h i * x i ^ 2 := mul_le_mul_of_nonneg_right hres hH
      _ = _ := one_mul _
  have hsum : ∑ i, h i * x i ^ 2 =
      R * (∑ i, x i ^ 2) - (1 - g) * ∑ i, (diag i * x i) ^ 2 := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [h]
    ring
  rw [hsum] at hcross
  linarith


/-- Scalar rank-one resolvent test, with its two moments and support radius
explicit. The moment hypotheses will be proved for the actual exponential tilt. -/
theorem paulin_resolvent_moments {ι : Type*} [Fintype ι]
    (p e : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (g δ U M1 M2 : ℝ) (hg : 0 < g) (hg1 : g ≤ 1)
    (hδ : 0 ≤ δ) (hU : 0 ≤ U) (hUg : U < g)
    (he : ∀ i, e i ≤ U) (hM1 : 0 ≤ M1) (hM2 : 0 ≤ M2)
    (hm1 : ∑ i, p i * e i ≤ M1) (hm2 : ∑ i, p i * e i ^ 2 ≤ M2)
    (hbudget : M1 + (1 - g) * M2 / (g - U) ≤ δ) :
    g * (∑ i, p i * (1 + e i) / (g + δ - (1 - g) * e i)) ≤ 1 := by
  classical
  let D := g + δ
  let H := g * (1 + δ) / D
  let F : ι → ℝ := fun i => e i + (1 - g) * e i ^ 2 / (g + δ - (1 - g) * e i)
  have hlam : 0 ≤ 1 - g := sub_nonneg.mpr hg1
  have hD : 0 < D := by dsimp [D]; linarith
  have hmin : 0 < g - U := sub_pos.mpr hUg
  have hden (i : ι) : g - U ≤ g + δ - (1 - g) * e i := by
    have h1 := mul_le_mul_of_nonneg_left (he i) hlam
    have h2 : (1 - g) * U ≤ U := by nlinarith
    linarith
  have hdenpos (i : ι) : 0 < g + δ - (1 - g) * e i := hmin.trans_le (hden i)
  have hH0 : 0 ≤ H := div_nonneg (mul_nonneg hg.le (by linarith)) hD.le
  have hH1 : H ≤ 1 := by
    apply (div_le_one hD).mpr
    have hh := mul_le_mul_of_nonneg_right hg1 hδ
    dsimp [D]
    nlinarith
  have hm2' : (∑ i, p i * (e i ^ 2 / (g + δ - (1 - g) * e i))) ≤ M2 / (g - U) := by
    calc
      _ ≤ ∑ i, p i * (e i ^ 2 / (g - U)) := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_left (sq_nonneg _) hmin (hden i)) (hp i)
      _ = (∑ i, p i * e i ^ 2) / (g - U) := by
        simp only [mul_div_assoc, Finset.sum_div]
      _ ≤ _ := div_le_div_of_nonneg_right hm2 hmin.le
  have hm : ∑ i, p i * F i ≤ M1 + (1 - g) * M2 / (g - U) := by
    have hf : (∑ i, p i * F i) =
        (∑ i, p i * e i) + (1 - g) * ∑ i, p i * (e i ^ 2 / (g + δ - (1 - g) * e i)) := by
      simp only [F, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hf]
    have hh := add_le_add hm1 (mul_le_mul_of_nonneg_left hm2' hlam)
    simpa only [mul_div_assoc] using hh
  have hB : 0 ≤ M1 + (1 - g) * M2 / (g - U) :=
    add_nonneg hM1 (div_nonneg (mul_nonneg hlam hM2) hmin.le)
  have hHm : H * (∑ i, p i * F i) ≤ δ := by
    calc
      _ ≤ H * (M1 + (1 - g) * M2 / (g - U)) := mul_le_mul_of_nonneg_left hm hH0
      _ ≤ 1 * (M1 + (1 - g) * M2 / (g - U)) := mul_le_mul_of_nonneg_right hH1 hB
      _ ≤ _ := by simpa only [one_mul] using hbudget
  have hi (i : ι) : g * (p i * (1 + e i) / (g + δ - (1 - g) * e i)) =
      p i + p i * (-δ + H * F i) / D := by
    dsimp [H, F, D]
    generalize hA : g + δ - (1 - g) * e i = A
    have hA0 : A ≠ 0 := by rw [← hA]; exact (hdenpos i).ne'
    have hD0 : g + δ ≠ 0 := by linarith
    field_simp [hA0, hD0]
    rw [← hA]
    ring

  rw [Finset.mul_sum]
  simp_rw [hi, Finset.sum_add_distrib]
  rw [hsum]
  have hh : (∑ i, p i * (-δ + H * F i) / D) = (-δ + H * ∑ i, p i * F i) / D := by
    rw [← Finset.sum_div]
    congr 1
    calc
      _ = -δ * (∑ i, p i) + H * ∑ i, p i * F i := by
        simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
        congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;> ring
      _ = _ := by rw [hsum]; ring
  rw [hh]
  have hn : (-δ + H * ∑ i, p i * F i) / D ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) hD.le
  linarith

/-- The numerical rational budget behind the constant `10` in the tilted bound. -/
theorem paulin_rational_budget (g θ V : ℝ) (hg : 0 < g) (hg1 : g ≤ 1)
    (hθ : 0 ≤ θ) (hsmall : 10 * θ < g) (hV : 0 ≤ V) :
    let U := 2 * θ / (1 - 2 * θ)
    U < g ∧
      2 * V * θ ^ 2 / (1 - 2 * θ) +
        (1 - g) * (4 * V * θ ^ 2 / (1 - 2 * θ) ^ 2) / (g - U) ≤
        4 * V * θ ^ 2 / (g - 10 * θ) := by
  intro U
  have hD : 0 < 1 - 2 * θ := by linarith
  have hG : 0 < g - 10 * θ := by linarith
  have hUg : U < g := by
    apply (div_lt_iff₀ hD).mpr
    have hmul := mul_le_mul_of_nonneg_left hg1 hθ
    nlinarith
  have hH : 0 < g * (1 - 2 * θ) - 2 * θ := by
    have hh := (div_lt_iff₀ hD).mp hUg
    linarith
  have hs : (10 * θ) ^ 2 ≤ g ^ 2 :=
    (sq_le_sq₀ (by positivity) hg.le).mpr hsmall.le
  have hmul : 24 * (g + 1) * θ ^ 2 ≤ 48 * θ ^ 2 :=
    mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg θ)
  have hA : 0 ≤ 2 * g ^ 2 - 24 * (g + 1) * θ ^ 2 := by nlinarith
  have hB : 0 ≤ (4 * g ^ 2 - 32 * g + 32) * θ := by
    apply mul_nonneg _ hθ
    nlinarith [sq_nonneg g]
  have hpoly : 0 ≤ 2 * g ^ 2 + (4 * g ^ 2 - 32 * g + 32) * θ -
      24 * (g + 1) * θ ^ 2 := by linarith
  have hcoeff : 2 / (1 - 2 * θ) +
      (1 - g) * (4 / (1 - 2 * θ) ^ 2) / (g - U) ≤ 4 / (g - 10 * θ) := by
    have he : 2 / (1 - 2 * θ) + (1 - g) * (4 / (1 - 2 * θ) ^ 2) / (g - U) =
        (4 - 2 * g - 4 * θ * (g + 1)) /
          ((1 - 2 * θ) * (g * (1 - 2 * θ) - 2 * θ)) := by
      dsimp [U]
      field_simp
      have hn' : g + (-(g * θ * 2) - θ * 2) ≠ 0 := by nlinarith [hH]
      field_simp [hn']
      ring
    rw [he]
    apply (div_le_div_iff₀ (mul_pos hD hH) hG).mpr
    nlinarith only [hpoly]
  refine ⟨hUg, ?_⟩
  have hh := mul_le_mul_of_nonneg_left hcoeff (mul_nonneg hV (sq_nonneg θ))
  convert hh using 1 <;> ring

/-- First and second moments of the actual centered exponential increment. -/
theorem paulin_exp_moments {ι : Type*} [Fintype ι]
    (p f : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hmean : ∑ i, p i * f i = 0) (hf : ∀ i, |f i| ≤ 1)
    (θ : ℝ) (hθ : 0 ≤ θ) (hsmall : 2 * θ < 1) :
    let V := ∑ i, p i * f i ^ 2
    let e := fun i => exp (2 * θ * f i) - 1
    (∀ i, e i ≤ 2 * θ / (1 - 2 * θ)) ∧
    (∑ i, p i * e i) ≤ 2 * V * θ ^ 2 / (1 - 2 * θ) ∧
    (∑ i, p i * e i ^ 2) ≤ 4 * V * θ ^ 2 / (1 - 2 * θ) ^ 2 := by
  classical
  intro V e
  have hD : 0 < 1 - 2 * θ := by linarith
  have hx (i : ι) : |2 * θ * f i| ≤ 2 * θ := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * θ)]
    simpa using mul_le_mul_of_nonneg_left (hf i) (by positivity : 0 ≤ 2 * θ)
  have hpoint (i : ι) : e i ≤ 2 * θ * f i + (2 * θ * f i) ^ 2 / (2 * (1 - 2 * θ)) := by
    have hh := exp_le_one_add_add_sq_uniform (2 * θ * f i) (2 * θ)
      ((le_abs_self _).trans (hx i)) (by linarith)
    have hr : (2 * θ * f i) ^ 2 / (2 * (1 - 2 * θ / 3)) ≤
        (2 * θ * f i) ^ 2 / (2 * (1 - 2 * θ)) := by
      apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
      linarith
    dsimp [e]
    linarith
  have habs (i : ι) : |e i| ≤ |2 * θ * f i| / (1 - 2 * θ) := by
    apply abs_le.mpr
    constructor
    · have hh := Real.add_one_le_exp (2 * θ * f i)
      have hab : -|2 * θ * f i| ≤ 2 * θ * f i := neg_abs_le _
      have hquot : |2 * θ * f i| ≤ |2 * θ * f i| / (1 - 2 * θ) := by
        apply (le_div_iff₀ hD).mpr
        nlinarith [abs_nonneg (2 * θ * f i)]
      dsimp [e]
      linarith
    · apply (le_div_iff₀ hD).mpr
      have hh := (le_div_iff₀ (mul_pos (by norm_num : (0:ℝ)<2) hD)).mp
        (show e i - 2 * θ * f i ≤ (2 * θ * f i) ^ 2 / (2 * (1 - 2 * θ)) by
          linarith [hpoint i])
      have hsq : (2 * θ * f i) ^ 2 ≤ 2 * θ * |2 * θ * f i| := by
        nlinarith [mul_le_mul_of_nonneg_right (hx i) (abs_nonneg (2 * θ * f i)),
          sq_abs (2 * θ * f i)]
      nlinarith [le_abs_self (2 * θ * f i), abs_nonneg (2 * θ * f i)]
  refine ⟨?_, ?_, ?_⟩
  · intro i
    exact (le_abs_self _).trans ((habs i).trans
      (div_le_div_of_nonneg_right (hx i) hD.le))
  · calc
      _ ≤ ∑ i, p i * (2 * θ * f i + (2 * θ * f i) ^ 2 / (2 * (1 - 2 * θ))) :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hpoint i) (hp i)
      _ = 2 * θ * (∑ i, p i * f i) + 2 * (∑ i, p i * f i ^ 2) * θ ^ 2 / (1 - 2 * θ) := by
        simp only [Finset.mul_sum, Finset.sum_mul, Finset.sum_div, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        field_simp
      _ = _ := by rw [hmean]; dsimp [V]; ring
  · have hsq (i : ι) : e i ^ 2 ≤ 4 * θ ^ 2 * f i ^ 2 / (1 - 2 * θ) ^ 2 := by
      have hh := (sq_le_sq₀ (abs_nonneg (e i))
        (div_nonneg (abs_nonneg _) hD.le)).mpr (habs i)
      norm_num only [sq_abs, div_pow, mul_pow, show (2 : ℝ) ^ 2 = 4 by norm_num] at hh
      exact hh
    calc
      _ ≤ ∑ i, p i * (4 * θ ^ 2 * f i ^ 2 / (1 - 2 * θ) ^ 2) :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hsq i) (hp i)
      _ = _ := by
        dsimp [V]
        simp only [Finset.mul_sum, Finset.sum_mul, Finset.sum_div]
        apply Finset.sum_congr rfl
        intro i _
        ring

/-- Quadratic bound for the actual tilted transition operator. -/
theorem paulin_tilted_quadratic {d : ℕ} [DecidableEq (Fin d)]
    (hd : 1 < d) (S : Stoch d) (st : Stationary S) (k : ℕ)
    (f : Fin d → ℝ) (hmean : stationaryMean st.mu f = 0)
    (hf : ∀ i, |f i| ≤ 1) (hg : 0 < aK S st k)
    (θ : ℝ) (hθ : 0 ≤ θ) (hsmall : 10 * θ < aK S st k)
    (x : Fin d → ℝ) :
    ∑ i, ((Lk S st k * paulinTilt f θ) *ᵥ x) i ^ 2 ≤
      (1 + 4 * stationaryVariance st.mu f * θ ^ 2 / (aK S st k - 10 * θ)) *
        ∑ i, x i ^ 2 := by
  classical
  let g := aK S st k
  let V := stationaryVariance st.mu f
  let δ := 4 * V * θ ^ 2 / (g - 10 * θ)
  let U := 2 * θ / (1 - 2 * θ)
  let e := fun i => exp (2 * θ * f i) - 1
  let diag := fun i => exp (θ * f i)
  have hg1 : g ≤ 1 := (aK_mem S st k).2
  have hg0 : 0 < g := hg
  have hG : 0 < g - 10 * θ := by linarith
  have hD : 0 < 1 - 2 * θ := by linarith
  have hV : 0 ≤ V := Finset.sum_nonneg fun i _ =>
    mul_nonneg (st.pos i).le (sq_nonneg _)
  have hδ : 0 ≤ δ := div_nonneg (by positivity) hG.le
  have hvar : (∑ i, st.mu i * f i ^ 2) = V := by
    dsimp [V, stationaryVariance]
    rw [hmean]
    simp
  have hmom := paulin_exp_moments st.mu f (fun i => (st.pos i).le)
    hmean hf θ hθ (by linarith)
  rw [hvar] at hmom
  have hbudget := paulin_rational_budget g θ V hg0 hg1 hθ hsmall hV
  have hUg : U < g := hbudget.1
  have hres := paulin_resolvent_moments st.mu e (fun i => (st.pos i).le)
    st.sum_one g δ U (2 * V * θ ^ 2 / (1 - 2 * θ))
      (4 * V * θ ^ 2 / (1 - 2 * θ) ^ 2) hg0 hg1 hδ
      (by dsimp [U]; positivity) hUg hmom.1 (by positivity) (by positivity)
      hmom.2.1 hmom.2.2 hbudget.2
  have hdiag (i : Fin d) : diag i ^ 2 = 1 + e i := by
    dsimp [diag, e]
    rw [pow_two, ← Real.exp_add]
    have he : θ * f i + θ * f i = 2 * θ * f i := by ring
    rw [he]
    ring
  have hden (i : Fin d) : 0 < 1 + δ - (1 - g) * diag i ^ 2 := by
    rw [hdiag]
    have h1 := mul_le_mul_of_nonneg_left (hmom.1 i) (sub_nonneg.mpr hg1)
    have h2 : (1 - g) * U ≤ U := by
      have hU : 0 ≤ U := by dsimp [U]; positivity
      nlinarith
    nlinarith
  have hres' : g * (∑ i, (stVec st i ^ 2 * diag i ^ 2) /
      (1 + δ - (1 - g) * diag i ^ 2)) ≤ 1 := by
    convert hres using 1
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    have hv : stVec st i ^ 2 = st.mu i := by simpa only [pow_two] using stVec_sq st i
    rw [hv, hdiag]
    congr 1
    ring
  have hschur := paulin_rankOne_schur_bound g (1 + δ) diag (stVec st) x
    hg0.le hg1 (by linarith) hden hres'
  have hgram := paulin_gram_projection_bound S st k hd (fun i => diag i * x i)
  have ht : paulinTilt f θ *ᵥ x = fun i => diag i * x i := by
    ext i
    simp [paulinTilt, Matrix.mulVec, dotProduct, diagonal, diag]
  rw [← ht] at hgram
  rw [Matrix.mulVec_mulVec] at hgram
  exact hgram.trans (by simpa only [g, δ, V, mul_assoc] using hschur)

private theorem paulin_real_euclidean_norm_sq {d : ℕ}
    (x : EuclideanSpace ℝ (Fin d)) : ‖x‖ ^ 2 = ∑ i, x i ^ 2 := by
  simpa only [Real.norm_eq_abs, sq_abs] using EuclideanSpace.norm_sq_eq x

/-- Corrected Paulin tilted-operator bound, proved from the actual sorted
singular-value deficit, centering, and a bounded observable. -/
theorem paulin_tilted_operator_norm {d : ℕ} [DecidableEq (Fin d)]
    (hd : 1 < d) (S : Stoch d) (st : Stationary S) (k : ℕ)
    (f : Fin d → ℝ) (hmean : stationaryMean st.mu f = 0)
    (hf : ∀ i, |f i| ≤ 1) (hg : 0 < aK S st k)
    (θ : ℝ) (hθ : 0 ≤ θ) (hsmall : 10 * θ < aK S st k) :
    ‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ)
      (Lk S st k * paulinTilt f θ)‖ ≤
      exp (2 * stationaryVariance st.mu f * θ ^ 2 / (aK S st k - 10 * θ)) := by
  classical
  let B := 2 * stationaryVariance st.mu f * θ ^ 2 / (aK S st k - 10 * θ)
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.exp_nonneg B)
  intro x
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (exp_nonneg _) (norm_nonneg _))).mp
  change ‖WithLp.toLp 2 ((Lk S st k * paulinTilt f θ) *ᵥ WithLp.ofLp x)‖ ^ 2 ≤ _
  rw [mul_pow, paulin_real_euclidean_norm_sq, paulin_real_euclidean_norm_sq]
  have hq := paulin_tilted_quadratic hd S st k f hmean hf hg θ hθ hsmall (WithLp.ofLp x)
  have he : 1 + 4 * stationaryVariance st.mu f * θ ^ 2 / (aK S st k - 10 * θ) ≤
      exp B ^ 2 := by
    rw [show exp B ^ 2 = exp (B + B) by rw [pow_two, ← Real.exp_add]]
    have hh := Real.add_one_le_exp (B + B)
    have hb : B + B = 4 * stationaryVariance st.mu f * θ ^ 2 / (aK S st k - 10 * θ) := by
      dsimp [B]
      ring
    rw [hb] at hh ⊢
    linarith
  exact hq.trans (mul_le_mul_of_nonneg_right he (Finset.sum_nonneg fun i _ => sq_nonneg _))

end PsgEst
