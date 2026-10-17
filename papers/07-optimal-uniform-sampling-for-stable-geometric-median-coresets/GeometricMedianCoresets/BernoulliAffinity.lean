import GeometricMedianCoresets.FiniteLaw

/-! The quantitative bias estimate (19) on the underlying Bernoulli product laws. -/
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace GeometricMedianCoresets.FiniteLaw

/-- Independent Bernoulli outcomes, with no assumed distributional estimates. -/
def bern (p : ℝ) (b : Bool) : ℝ := if b then p else 1 - p
def bernProduct (m : ℕ) (p : ℝ) (w : Fin m → Bool) : ℝ := ∏ i, bern p (w i)

lemma bern_nonneg {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) (b : Bool) : 0 ≤ bern p b := by
  cases b <;> simp [bern] <;> linarith

lemma bernProduct_nonneg {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) (m : ℕ) (w : Fin m → Bool) :
    0 ≤ bernProduct m p w := Finset.prod_nonneg fun i _ => bern_nonneg hp hp' (w i)

lemma bernProduct_sum (m : ℕ) (p : ℝ) : ∑ w, bernProduct m p w = 1 := by
  unfold bernProduct
  have heq := (Fintype.prod_sum (fun _ : Fin m => bern p)).symm
  calc _ = ∏ _i : Fin m, ∑ b : Bool, bern p b := heq
    _ = 1 := by simp [bern]

lemma sqrt_prod_nonneg {ι : Type*} (s : Finset ι) (f : ι → ℝ) (hf : ∀ i ∈ s, 0 ≤ f i) :
    Real.sqrt (∏ i ∈ s, f i) = ∏ i ∈ s, Real.sqrt (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s his ih =>
    rw [Finset.prod_insert his, Finset.prod_insert his, Real.sqrt_mul (hf i (by simp))]
    rw [ih (fun j hj => hf j (by simp [hj]))]

/-- Affinity factors across the independent coordinates. -/
theorem affinity_bernProduct (m : ℕ) {p q : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1)
    (hq : 0 ≤ q) (hq' : q ≤ 1) :
    affinity (bernProduct m p) (bernProduct m q) =
      (Real.sqrt p * Real.sqrt q + Real.sqrt (1 - p) * Real.sqrt (1 - q)) ^ m := by
  unfold affinity bernProduct
  simp_rw [sqrt_prod_nonneg Finset.univ _ (fun i _ => bern_nonneg hp hp' _),
    sqrt_prod_nonneg Finset.univ _ (fun i _ => bern_nonneg hq hq' _),
    ← Finset.prod_mul_distrib]
  have hfactor := (Fintype.prod_sum (fun _ : Fin m => fun b : Bool =>
    Real.sqrt (bern p b) * Real.sqrt (bern q b))).symm
  rw [hfactor]
  have hsum : (∑ b : Bool, Real.sqrt (bern p b) * Real.sqrt (bern q b)) =
      Real.sqrt p * Real.sqrt q + Real.sqrt (1 - p) * Real.sqrt (1 - q) := by
    simp [bern, add_comm]
  simp_rw [hsum]
  simp

/-- The exact one-coordinate affinity square in the paper. -/
theorem bern_affinity_sq {θ : ℝ} (hθ : 0 ≤ θ) (hθ' : θ ≤ 1) :
    (Real.sqrt ((1 - θ) / 2) * Real.sqrt (1/2) +
      Real.sqrt (1 - (1 - θ) / 2) * Real.sqrt (1 - 1/2)) ^ 2 =
      (1 + Real.sqrt (1 - θ ^ 2)) / 2 := by
  have hp : 0 ≤ (1 - θ) / 2 := by linarith
  have hq : 0 ≤ 1 - (1 - θ) / 2 := by linarith
  have hr : 0 ≤ 1 - θ ^ 2 := by nlinarith
  have hhalf : (1 - (1/2:ℝ)) = 1/2 := by norm_num
  rw [hhalf]
  have hmul : (2 * (Real.sqrt ((1 - θ) / 2) * Real.sqrt (1 - (1 - θ) / 2))) ^ 2 =
      1 - θ ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hp, Real.sq_sqrt hq]
    ring
  have hs : 2 * (Real.sqrt ((1 - θ) / 2) * Real.sqrt (1 - (1 - θ) / 2)) =
      Real.sqrt (1 - θ ^ 2) := by
    apply (sq_eq_sq₀ (by positivity) (Real.sqrt_nonneg _)).1
    rw [hmul, Real.sq_sqrt hr]
  have ht : Real.sqrt (1/2:ℝ) ^ 2 = 1/2 := Real.sq_sqrt (by norm_num)
  have ha : (Real.sqrt ((1 - θ) / 2) * Real.sqrt (1/2:ℝ)) ^ 2 = ((1 - θ) / 2) / 2 := by
    rw [mul_pow, Real.sq_sqrt hp, ht]; ring
  have hb : (Real.sqrt (1 - (1 - θ) / 2) * Real.sqrt (1/2:ℝ)) ^ 2 = (1 - (1 - θ) / 2) / 2 := by
    rw [mul_pow, Real.sq_sqrt hq, ht]; ring
  have hc : 2 * (Real.sqrt ((1 - θ) / 2) * Real.sqrt (1/2:ℝ)) *
      (Real.sqrt (1 - (1 - θ) / 2) * Real.sqrt (1/2:ℝ)) =
      Real.sqrt ((1 - θ) / 2) * Real.sqrt (1 - (1 - θ) / 2) := by
    calc _ = (Real.sqrt ((1 - θ) / 2) * Real.sqrt (1 - (1 - θ) / 2)) *
        (2 * Real.sqrt (1/2:ℝ) ^ 2) := by ring
      _ = _ := by rw [ht]; ring
  nlinarith [ha, hb, hc, hs]

/-- The elementary Bernoulli inequality in the form used in (19). -/
lemma one_sub_pow_le (m : ℕ) {u : ℝ} (hu : 0 ≤ u) (hu' : u ≤ 1) :
    1 - u ^ m ≤ m * (1 - u) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hpow : 0 ≤ u ^ m := pow_nonneg hu _
    have hpow' : u ^ m ≤ 1 := pow_le_one₀ hu hu'
    rw [pow_succ, Nat.cast_add, Nat.cast_one]
    nlinarith [mul_nonneg (sub_nonneg.2 hu') (sub_nonneg.2 hpow')]

/-- Equation (19), directly on the full outcome space, hence on every counting event. -/
theorem bernProduct_tv_bound (m : ℕ) {θ : ℝ} (hθ : 0 ≤ θ) (hθ' : θ ≤ 1) :
    tv (bernProduct m ((1 - θ) / 2)) (bernProduct m (1/2)) ≤
      Real.sqrt ((m:ℝ) * θ ^ 2 / 2) := by
  have hp : 0 ≤ (1 - θ) / 2 := by linarith
  have hp' : (1 - θ) / 2 ≤ 1 := by linarith
  have htv := tv_le_sqrt_affinity _ _ (bernProduct_nonneg hp hp' m)
    (bernProduct_nonneg (p := (1/2:ℝ)) (by norm_num) (by norm_num) m)
    (bernProduct_sum m _) (bernProduct_sum m _)
  rw [affinity_bernProduct m hp hp' (by norm_num) (by norm_num), ← pow_mul, mul_comm m 2,
    pow_mul, bern_affinity_sq hθ hθ'] at htv
  apply htv.trans
  apply Real.sqrt_le_sqrt
  have hr : 0 ≤ 1 - θ ^ 2 := by nlinarith
  have hsr : Real.sqrt (1 - θ ^ 2) ≤ 1 := (Real.sqrt_le_one).2 (by nlinarith)
  have hsr' := Real.sqrt_nonneg (1 - θ ^ 2)
  have hsq := Real.sq_sqrt hr
  have hnum : 1 - Real.sqrt (1 - θ ^ 2) ≤ θ ^ 2 := by nlinarith
  have hb := one_sub_pow_le m (by positivity : 0 ≤ (1 + Real.sqrt (1 - θ ^ 2)) / 2)
    (by linarith : (1 + Real.sqrt (1 - θ ^ 2)) / 2 ≤ 1)
  have hm := Nat.cast_nonneg (α := ℝ) m
  nlinarith [mul_le_mul_of_nonneg_left hnum hm]

end GeometricMedianCoresets.FiniteLaw
