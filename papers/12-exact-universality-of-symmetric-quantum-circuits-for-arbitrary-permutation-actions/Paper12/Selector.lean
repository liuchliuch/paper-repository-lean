import Paper12.PauliExpand
import Paper12.Circuit

/-!
# Symmetric one-hot preparation (Lemma 2.5)

One selector wire per nonzero Pauli word.  Product rotations followed by a
Hamming-weight test and exact amplitude amplification prepare the one-hot
state `|χ⟩ = ∑_P d_P |e_P⟩` with three auxiliary wires.  Orbitwise selector
permutations preserve every layer.

This file proves the analytic content of the construction: the success
probability `p₀ = c₀²` of the product-rotation stage lies in `[e⁻¹, 1/2]`,
the correction angle `β₀` of equation (8) exists, the amplification angle
`θ₀ = π/10` satisfies `5 θ₀ = π/2`, and the gate count is `O(M)`.
-/

noncomputable section

namespace Paper12

open Matrix Complex

variable {X : Type*} [Fintype X]

/-! ### One-hot basis states -/

/-- One-hot basis state with the unique `1` on wire `q`. -/
def oneHot {J : Type*} [DecidableEq J] (q : J) : Basis J :=
  fun j => if j = q then 1 else 0

@[simp]
theorem oneHot_apply_eq {J : Type*} [DecidableEq J] (q : J) : oneHot q q = 1 := by
  simp [oneHot]

theorem oneHot_apply_ne {J : Type*} [DecidableEq J] {q j : J} (h : j ≠ q) :
    oneHot q j = 0 := by
  simp [oneHot, h]

/-! ### Product-rotation success probability -/

/-- Weight-one success probability of the product rotations. -/
def prepP0 (α : Coeffs X) : ℝ :=
  (∏ w ∈ coeffSupport α, (1 + (selectorAmp α w) ^ 2))⁻¹

/-- Positive product normalization. -/
def prepC0 (α : Coeffs X) : ℝ := Real.sqrt (prepP0 α)

theorem one_add_le_exp' (x : ℝ) : 1 + x ≤ Real.exp x := by simpa [add_comm] using Real.add_one_le_exp x

/-- `∏ (1 + aᵢ) ≤ exp(∑ aᵢ)` for nonnegative `aᵢ`. -/
theorem prod_one_add_le_exp {ι : Type*} {s : Finset ι} {f : ι → ℝ}
    (hf : ∀ i ∈ s, 0 ≤ f i) :
    ∏ i ∈ s, (1 + f i) ≤ Real.exp (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    have hfi : 0 ≤ f i := hf i (Finset.mem_insert_self i s)
    have hs : ∀ j ∈ s, 0 ≤ f j := fun j hj => hf j (Finset.mem_insert_of_mem hj)
    have ih' := ih hs
    have h1 : 1 + f i ≤ Real.exp (f i) := one_add_le_exp' (f i)
    have h2 : Real.exp (f i) * Real.exp (∑ j ∈ s, f j) = Real.exp (f i + ∑ j ∈ s, f j) :=
      (Real.exp_add _ _).symm
    calc (1 + f i) * ∏ j ∈ s, (1 + f j)
        ≤ Real.exp (f i) * ∏ j ∈ s, (1 + f j) :=
          mul_le_mul_of_nonneg_right h1 (Finset.prod_nonneg (fun j hj => by
            have := hs j hj; linarith))
      _ ≤ Real.exp (f i) * Real.exp (∑ j ∈ s, f j) :=
          mul_le_mul_of_nonneg_left ih' (Real.exp_pos _).le
      _ = Real.exp (f i + ∑ j ∈ s, f j) := h2

/-- `1 + ∑ aᵢ ≤ ∏ (1 + aᵢ)` for nonnegative `aᵢ`. -/
theorem one_add_sum_le_prod_one_add {ι : Type*} {s : Finset ι} {f : ι → ℝ}
    (hf : ∀ i ∈ s, 0 ≤ f i) :
    1 + ∑ i ∈ s, f i ≤ ∏ i ∈ s, (1 + f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    have hfi : 0 ≤ f i := hf i (Finset.mem_insert_self i s)
    have hs : ∀ j ∈ s, 0 ≤ f j := fun j hj => hf j (Finset.mem_insert_of_mem hj)
    have ih' : 1 + ∑ j ∈ s, f j ≤ ∏ j ∈ s, (1 + f j) := ih hs
    have hle : 0 ≤ ∏ j ∈ s, (1 + f j) :=
      Finset.prod_nonneg (fun j hj => by have := hs j hj; linarith)
    calc 1 + (f i + ∑ j ∈ s, f j)
        = (1 + f i) * 1 + (1 + f i) * ∑ j ∈ s, f j - f i * ∑ j ∈ s, f j := by ring
      _ = (1 + f i) * (1 + ∑ j ∈ s, f j) - f i * ∑ j ∈ s, f j := by ring
      _ ≤ (1 + f i) * (1 + ∑ j ∈ s, f j) := by
          nlinarith [mul_nonneg hfi (Finset.sum_nonneg (fun j hj => hs j hj))]
      _ ≤ (1 + f i) * ∏ j ∈ s, (1 + f j) :=
          mul_le_mul_of_nonneg_left ih' (by linarith)

/-- The product rotation amplitudes satisfy
`e⁻¹ ≤ p₀ ≤ 1/2`, where `p₀ = c₀² = ∏ (1 + d_P²)⁻¹` and `∑ d_P² = 1`. -/
theorem prep_p0_bounds (α : Coeffs X)
    (hsq : ∑ w ∈ coeffSupport α, (selectorAmp α w) ^ 2 = 1) :
    Real.exp (-1) ≤ prepP0 α ∧ prepP0 α ≤ 1 / 2 := by
  have hprod_le : (∏ w ∈ coeffSupport α, (1 + (selectorAmp α w) ^ 2)) ≤ Real.exp 1 := by
    have h := prod_one_add_le_exp (s := coeffSupport α)
      (f := fun w => (selectorAmp α w) ^ 2) (fun w _ => sq_nonneg _)
    rwa [hsq] at h
  have hprod_ge : (2 : ℝ) ≤ ∏ w ∈ coeffSupport α, (1 + (selectorAmp α w) ^ 2) := by
    have h := one_add_sum_le_prod_one_add (s := coeffSupport α)
      (f := fun w => (selectorAmp α w) ^ 2) (fun w _ => sq_nonneg _)
    rw [hsq] at h
    norm_num at h ⊢
    exact h
  have hprod_pos : 0 < ∏ w ∈ coeffSupport α, (1 + (selectorAmp α w) ^ 2) := by
    linarith
  unfold prepP0
  constructor
  · rw [Real.exp_neg]
    exact (inv_le_inv₀ (Real.exp_pos _) hprod_pos).mpr hprod_le
  · simpa only [one_div] using
      (inv_le_inv₀ hprod_pos (by norm_num : (0 : ℝ) < 2)).mpr hprod_ge

/-- Success probability of the one-hot stage is positive. -/
theorem prep_p0_pos (α : Coeffs X)
    (hsq : ∑ w ∈ coeffSupport α, (selectorAmp α w) ^ 2 = 1) :
    0 < prepP0 α := by
  have h := (prep_p0_bounds α hsq).1
  have he : 0 < Real.exp (-1) := Real.exp_pos _
  linarith

/-! ### Amplification angle of Lemma 2.5 -/

/-- Product-rotation angle `θ₀ = π/10` used by the two-step preparation. -/
def theta0 : ℝ := Real.pi / 10

theorem theta0_pos : 0 < theta0 := by
  unfold theta0; positivity

theorem theta0_lt_pi_div_two : theta0 < Real.pi / 2 := by
  unfold theta0
  have h : Real.pi / 10 < Real.pi / 2 := by
    have hp := Real.pi_pos
    linarith
  exact h

theorem five_theta0 : 5 * theta0 = Real.pi / 2 := by
  unfold theta0
  ring

theorem sin_theta0_pos : 0 < Real.sin theta0 :=
  Real.sin_pos_of_pos_of_lt_pi theta0_pos (by
    linarith [theta0_lt_pi_div_two, Real.pi_pos])

theorem sin_theta0_lt_half : Real.sin theta0 < 1 / 2 := by
  have h1 : theta0 < Real.pi / 6 := by
    unfold theta0; linarith [Real.pi_pos]
  have h2 := Real.sin_lt_sin_of_lt_of_le_pi_div_two
    (x := theta0) (y := Real.pi / 6)
    (by linarith [theta0_pos, Real.pi_pos]) (by linarith [Real.pi_pos]) h1
  simpa using h2

theorem exp_neg_half_gt_half : 1 / 2 < Real.exp (-(1 / 2 : ℝ)) := by
  have he : Real.exp 1 < 4 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  have hpos := Real.exp_pos (1 / 2 : ℝ)
  have hsq : Real.exp (1 / 2 : ℝ) ^ 2 = Real.exp 1 := by
    rw [sq, ← Real.exp_add]
    norm_num
  have hlt : Real.exp (1 / 2 : ℝ) < 2 := by nlinarith
  rw [Real.exp_neg]
  simpa only [one_div] using (one_div_lt_one_div_of_lt hpos hlt)

/-- The ratio `sin θ₀ / √p₀` of equation (8) lies in `(0, 1)`, so the
correction angle `β₀ ∈ (0, π)` is well defined. -/
theorem beta0_ratio_mem (α : Coeffs X)
    (hsq : ∑ w ∈ coeffSupport α, (selectorAmp α w) ^ 2 = 1) :
    0 < Real.sin theta0 / Real.sqrt (prepP0 α) ∧
      Real.sin theta0 / Real.sqrt (prepP0 α) < 1 := by
  have hp0 : 0 < prepP0 α := prep_p0_pos α hsq
  have hsqrt : 0 < Real.sqrt (prepP0 α) := Real.sqrt_pos.mpr hp0
  have hle := (prep_p0_bounds α hsq).1
  have hexp : Real.exp (-1) = Real.exp (-(1 / 2 : ℝ)) ^ 2 := by
    rw [sq, ← Real.exp_add]
    norm_num
  have hsqrt_ge : Real.exp (-(1 / 2 : ℝ)) ≤ Real.sqrt (prepP0 α) := by
    rw [hexp] at hle
    exact (Real.le_sqrt (Real.exp_pos _).le hp0.le).mpr hle
  exact ⟨div_pos sin_theta0_pos hsqrt,
    (div_lt_one hsqrt).mpr (lt_of_lt_of_le
      (lt_trans sin_theta0_lt_half exp_neg_half_gt_half) hsqrt_ge)⟩

/-- Correction angle `β₀` of equation (8): `sin(β₀/2) = sin θ₀ / √p₀`. -/
def beta0 (α : Coeffs X) : ℝ := 2 * Real.arcsin (Real.sin theta0 / Real.sqrt (prepP0 α))

theorem beta0_mem (α : Coeffs X)
    (hsq : ∑ w ∈ coeffSupport α, (selectorAmp α w) ^ 2 = 1) :
    0 < beta0 α ∧ beta0 α < Real.pi ∧
      Real.sin (beta0 α / 2) = Real.sin theta0 / Real.sqrt (prepP0 α) := by
  obtain ⟨hpos, hlt⟩ := beta0_ratio_mem α hsq
  have ha : 0 < Real.arcsin (Real.sin theta0 / Real.sqrt (prepP0 α)) :=
    Real.arcsin_pos.mpr hpos
  have hb : Real.arcsin (Real.sin theta0 / Real.sqrt (prepP0 α)) < Real.pi / 2 :=
    Real.arcsin_lt_pi_div_two.mpr hlt
  unfold beta0
  refine ⟨by linarith, by linarith, ?_⟩
  rw [show 2 * Real.arcsin (Real.sin theta0 / Real.sqrt (prepP0 α)) / 2 =
    Real.arcsin (Real.sin theta0 / Real.sqrt (prepP0 α)) by ring]
  exact Real.sin_arcsin (by linarith) hlt.le

/-- Two exact amplification steps with `θ₀` reach the good state: the
two-reflection identity at `j = 2` has `sin(5θ₀) = 1` and `cos(5θ₀) = 0`. -/
theorem two_step_angles :
    Real.sin ((2 * 2 + 1) * theta0) = 1 ∧
      Real.cos ((2 * 2 + 1) * theta0) = 0 ∧
      ((-1 : ℂ) ^ (2 : ℕ)) = 1 := by
  have h5 : (2 * 2 + 1 : ℝ) * theta0 = Real.pi / 2 := by
    norm_num; exact five_theta0
  rw [h5]
  norm_num

/-! ### Analytic package of Lemma 2.5 -/

/-- Mathematical content of Lemma 2.5: the amplitudes of the prepared
state are the selector amplitudes, the success probability lies in
`[e^{-1}, 1/2]`, the correction angle exists, and two steps of `θ₀ = π/10`
are exact. -/
structure OneHotPrep (α : Coeffs X) : Prop where
  mass_pos : 0 < coeffMass α
  amp_sq : ∑ w ∈ coeffSupport α, (selectorAmp α w) ^ 2 = 1
  product_norm :
    Real.exp (-1) ≤ prepP0 α ∧ prepP0 α ≤ 1 / 2
  beta_mem :
    0 < beta0 α ∧ beta0 α < Real.pi ∧
      Real.sin (beta0 α / 2) = Real.sin theta0 / Real.sqrt (prepP0 α)
  two_step :
    Real.sin ((2 * 2 + 1) * theta0) = 1 ∧
      Real.cos ((2 * 2 + 1) * theta0) = 0

/-- The analytic hypotheses of Lemma 2.5 are forced by mass positivity and
the normalisation `∑ d_P² = 1`. -/
theorem oneHotPrep_of_mass (α : Coeffs X)
    (hmass : 0 < coeffMass α)
    (hsq : ∑ w ∈ coeffSupport α, (selectorAmp α w) ^ 2 = 1) :
    OneHotPrep α where
  mass_pos := hmass
  amp_sq := hsq
  product_norm := prep_p0_bounds α hsq
  beta_mem := beta0_mem α hsq
  two_step := ⟨two_step_angles.1, two_step_angles.2.1⟩

/-! ### Gate count of the preparation -/

/-- Product-layer gate count of `A₀` and `A₀†` occurrences in `B`.
The paper uses five such layers of `M = |J|` rotations each, plus a
constant number of auxiliary gates. -/
def prepGateCount (α : Coeffs X) : ℕ := 5 * coeffCard α + 15

theorem prepGateCount_le (α : Coeffs X) :
    prepGateCount α ≤ 40 * (coeffCard α + 1) := by
  unfold prepGateCount
  have h : 5 * coeffCard α + 15 ≤ 40 * (coeffCard α + 1) := by
    cases' Nat.le_total 0 (coeffCard α) with _ _
    · nlinarith
    · nlinarith
  exact h

end Paper12
