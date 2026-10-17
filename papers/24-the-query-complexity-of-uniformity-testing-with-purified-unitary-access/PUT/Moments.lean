import PUT.Basic

/-!
# Dirichlet moments and normalized radial weights

Paper 24, equation (6) and the identities used in Section 3:
`m_k = ∏(a)_{k_i}/(ad)_K`, `w_k(p) = ∏ p_i^{k_i/2}/√m_k`,
and the exact creation/erasure coefficient identities (10)–(11).
-/

noncomputable section
namespace PUT

theorem dirMoment_def (a : ℝ) {d : ℕ} (k : Fin d → ℕ) :
    dirMoment a k = (∏ i, risingFactorial a (k i)) / risingFactorial (a * d) (degK k) := rfl

/-! ## Rising factorial identities -/

/-- Rising factorial recurrence used by the moment ratios. -/
theorem risingFactorial_succ_coe (x : ℝ) (r : ℕ) :
    risingFactorial x (r + 1) = risingFactorial x r * (x + r) := by
  induction r generalizing x with
  | zero => simp [risingFactorial_succ]
  | succ r ih =>
    calc risingFactorial x (r + 2) = x * risingFactorial (x + 1) (r + 1) := rfl
      _ = x * (risingFactorial (x + 1) r * (x + 1 + r)) := by rw [ih]
      _ = risingFactorial x (r + 1) * (x + (r + 1 : ℕ)) := by
        rw [risingFactorial_succ]
        push_cast
        ring

theorem risingFactorial_add_one (x : ℝ) (r : ℕ) :
    risingFactorial x (r + 1) = risingFactorial x r * (x + r) :=
  risingFactorial_succ_coe x r

/-- Rising factorials of a positive base are strictly positive. -/
theorem risingFactorial_pos (x : ℝ) (hx : 0 < x) : ∀ r : ℕ, 0 < risingFactorial x r
  | 0 => by simp
  | r + 1 => by
    rw [risingFactorial_succ]
    exact mul_pos hx (risingFactorial_pos (x + 1) (by linarith) r)

theorem risingFactorial_ne_zero (x : ℝ) (hx : 0 < x) (r : ℕ) : risingFactorial x r ≠ 0 :=
  (risingFactorial_pos x hx r).ne'

theorem risingFactorial_nonneg (x : ℝ) (hx : 0 < x) (r : ℕ) : 0 ≤ risingFactorial x r :=
  (risingFactorial_pos x hx r).le

/-- If `1 ≤ x` then `(x)_r ≥ 1`. -/
theorem one_le_risingFactorial (x : ℝ) (hx : 1 ≤ x) (r : ℕ) : 1 ≤ risingFactorial x r := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [risingFactorial_succ_coe]
    have h1 : (1 : ℝ) ≤ x + r := by
      have : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
      linarith
    have hnn : 0 ≤ risingFactorial x r :=
      risingFactorial_nonneg x (by linarith : (0 : ℝ) < x) r
    nlinarith

/-! ## Degree of updated vectors -/

theorem degK_degUp {d : ℕ} (k : Fin d → ℕ) (i : Fin d) :
    degK (degUp k i) = degK k + 1 := by
  have h : degUp k i = Function.update k i (k i + 1) := rfl
  unfold degK
  rw [h, Finset.sum_update_of_mem (Finset.mem_univ i)]
  have hsplit : (∑ j : Fin d, k j)
      = ∑ j ∈ (Finset.univ : Finset (Fin d)) \ {i}, k j + k i :=
    Finset.sum_eq_sum_diff_singleton_add (Finset.mem_univ i) _
  omega

theorem degK_degDown {d : ℕ} (k : Fin d → ℕ) (i : Fin d) (hi : 0 < k i) :
    degK (degDown k i) = degK k - 1 := by
  have h : degDown k i = Function.update k i (k i - 1) := rfl
  unfold degK
  rw [h, Finset.sum_update_of_mem (Finset.mem_univ i)]
  have hsplit : (∑ j : Fin d, k j)
      = ∑ j ∈ (Finset.univ : Finset (Fin d)) \ {i}, k j + k i :=
    Finset.sum_eq_sum_diff_singleton_add (Finset.mem_univ i) _
  omega

theorem one_le_degK_of_pos {d : ℕ} {k : Fin d → ℕ} {i : Fin d} (hi : 0 < k i) :
    1 ≤ degK k := by
  unfold degK
  have hle : k i ≤ ∑ j : Fin d, k j :=
    Finset.single_le_sum (fun j _ => Nat.zero_le (k j)) (Finset.mem_univ i)
  have : 1 ≤ k i := Nat.succ_le_of_lt hi
  omega

/-! ## Products of rising factorials under `degUp` / `degDown` -/

theorem prod_risingFactorial_degUp {d : ℕ} (a : ℝ) (k : Fin d → ℕ) (i : Fin d) :
    (∏ j, risingFactorial a (degUp k i j)) = (a + k i) * ∏ j, risingFactorial a (k j) := by
  have hupd : (fun j => risingFactorial a (degUp k i j))
      = Function.update (fun j => risingFactorial a (k j)) i (risingFactorial a (k i + 1)) := by
    funext j
    by_cases hj : j = i
    · subst hj
      simp [degUp, Function.update]
    · simp [degUp, Function.update, hj]
  rw [hupd, Finset.prod_update_of_mem (Finset.mem_univ i)]
  rw [risingFactorial_succ_coe]
  have hsplit : (∏ j : Fin d, risingFactorial a (k j))
      = risingFactorial a (k i)
        * ∏ j ∈ (Finset.univ : Finset (Fin d)) \ {i}, risingFactorial a (k j) :=
    Finset.prod_eq_mul_prod_diff_singleton (Finset.mem_univ i) _
  rw [hsplit]
  ring

theorem prod_risingFactorial_degDown {d : ℕ} (a : ℝ) (k : Fin d → ℕ) (i : Fin d)
    (hi : 0 < k i) :
    (∏ j, risingFactorial a (k j))
      = (a + k i - 1) * ∏ j, risingFactorial a (degDown k i j) := by
  have hupd : (fun j => risingFactorial a (degDown k i j))
      = Function.update (fun j => risingFactorial a (k j)) i (risingFactorial a (k i - 1)) := by
    funext j
    by_cases hj : j = i
    · subst hj
      simp [degDown, Function.update]
    · simp [degDown, Function.update, hj]
  have hprod : (∏ j, risingFactorial a (degDown k i j))
      = risingFactorial a (k i - 1)
        * ∏ j ∈ (Finset.univ : Finset (Fin d)) \ {i}, risingFactorial a (k j) := by
    rw [hupd, Finset.prod_update_of_mem (Finset.mem_univ i)]
  have hsplit : (∏ j : Fin d, risingFactorial a (k j))
      = risingFactorial a (k i)
        * ∏ j ∈ (Finset.univ : Finset (Fin d)) \ {i}, risingFactorial a (k j) :=
    Finset.prod_eq_mul_prod_diff_singleton (Finset.mem_univ i) _
  rw [hsplit]
  have hk : k i = (k i - 1) + 1 := by omega
  conv_lhs =>
    enter [1]
    rw [hk, risingFactorial_succ_coe]
  have hcast : ((k i - 1 : ℕ) : ℝ) = (k i : ℝ) - 1 := by
    have : 1 ≤ k i := Nat.succ_le_of_lt hi
    rw [Nat.cast_sub this, Nat.cast_one]
  rw [hcast, hprod]
  ring

/-! ## Moment ratio identities (6) -/

/-- Creation moment ratio: `m_{k+e_i} = ((a+k_i)/S) · m_k`. -/
theorem dirMoment_degUp (a : ℝ) {d : ℕ} (k : Fin d → ℕ) (i : Fin d) :
    dirMoment a (degUp k i) = ((a + k i) / postTotal a k) * dirMoment a k := by
  unfold dirMoment postTotal
  rw [prod_risingFactorial_degUp, degK_degUp, risingFactorial_succ_coe]
  conv_rhs => rw [div_mul_div_comm]
  rw [mul_comm (risingFactorial (a * ↑d) (degK k)) (a * ↑d + ↑(degK k))]

/-- Erasure moment ratio: `m_k = ((a+k_i-1)/(S-1)) · m_{k-e_i}`. -/
theorem dirMoment_degDown (a : ℝ) {d : ℕ} (k : Fin d → ℕ) (i : Fin d) (hi : 0 < k i) :
    dirMoment a k = ((a + k i - 1) / (postTotal a k - 1)) * dirMoment a (degDown k i) := by
  unfold dirMoment postTotal
  rw [prod_risingFactorial_degDown a k i hi, degK_degDown k i hi]
  have hK : 1 ≤ degK k := one_le_degK_of_pos hi
  have hexp : degK k = (degK k - 1) + 1 := by omega
  conv_lhs =>
    enter [2]
    rw [hexp, risingFactorial_succ_coe]
  have hcast : ((degK k - 1 : ℕ) : ℝ) = (degK k : ℝ) - 1 := by
    rw [Nat.cast_sub hK, Nat.cast_one]
  rw [hcast]
  have hS : a * ↑d + (↑(degK k) - 1) = a * ↑d + ↑(degK k) - 1 := by ring
  rw [hS]
  conv_rhs => rw [div_mul_div_comm]
  rw [mul_comm (risingFactorial (a * ↑d) (degK k - 1)) (a * ↑d + ↑(degK k) - 1)]

/-! ## Positivity of moments -/

theorem dirMoment_pos (a : ℝ) {d : ℕ} (k : Fin d → ℕ) (ha : 0 < a) :
    0 < dirMoment a k := by
  unfold dirMoment
  have hnum : 0 < ∏ i, risingFactorial a (k i) :=
    Finset.prod_pos fun i _ => risingFactorial_pos a ha (k i)
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    have hK : degK k = 0 := by
      unfold degK
      simp
    rw [hK, risingFactorial_zero]
    simp
  · have hden : 0 < risingFactorial (a * d) (degK k) :=
      risingFactorial_pos _ (mul_pos ha (by exact_mod_cast hd)) _
    exact div_pos hnum hden

theorem dirMoment_ne_zero (a : ℝ) {d : ℕ} (k : Fin d → ℕ) (ha : 0 < a) :
    dirMoment a k ≠ 0 :=
  (dirMoment_pos a k ha).ne'

/-! ## Products of powers under `degUp` / `degDown` -/

theorem prod_pow_degUp {d : ℕ} (p : Fin d → ℝ) (k : Fin d → ℕ) (i : Fin d)
    (hp : ∀ j, 0 < p j) :
    (∏ j, (p j) ^ ((degUp k i j : ℝ) / 2))
      = Real.sqrt (p i) * ∏ j, (p j) ^ ((k j : ℝ) / 2) := by
  have hupd : (fun j => (p j) ^ ((degUp k i j : ℝ) / 2))
      = Function.update (fun j => (p j) ^ ((k j : ℝ) / 2)) i
          ((p i) ^ (((k i + 1 : ℕ) : ℝ) / 2)) := by
    funext j
    by_cases hj : j = i
    · subst hj
      simp [degUp, Function.update]
    · simp [degUp, Function.update, hj]
  rw [hupd, Finset.prod_update_of_mem (Finset.mem_univ i)]
  have hsplit : (∏ j : Fin d, (p j) ^ ((k j : ℝ) / 2))
      = (p i) ^ ((k i : ℝ) / 2)
        * ∏ j ∈ (Finset.univ : Finset (Fin d)) \ {i}, (p j) ^ ((k j : ℝ) / 2) :=
    Finset.prod_eq_mul_prod_diff_singleton (Finset.mem_univ i) _
  rw [hsplit]
  have hcast : (((k i + 1 : ℕ) : ℝ) / 2) = (k i : ℝ) / 2 + 1 / 2 := by
    push_cast
    ring
  have hsplitpow : (p i) ^ (((k i + 1 : ℕ) : ℝ) / 2)
      = (p i) ^ ((k i : ℝ) / 2) * Real.sqrt (p i) := by
    rw [hcast, Real.rpow_add (hp i), Real.sqrt_eq_rpow]
  rw [hsplitpow]
  ring

theorem prod_pow_degDown {d : ℕ} (p : Fin d → ℝ) (k : Fin d → ℕ) (i : Fin d)
    (hp : ∀ j, 0 < p j) (hi : 0 < k i) :
    (∏ j, (p j) ^ ((k j : ℝ) / 2))
      = Real.sqrt (p i) * ∏ j, (p j) ^ ((degDown k i j : ℝ) / 2) := by
  have hupd : (fun j => (p j) ^ ((degDown k i j : ℝ) / 2))
      = Function.update (fun j => (p j) ^ ((k j : ℝ) / 2)) i
          ((p i) ^ (((k i - 1 : ℕ) : ℝ) / 2)) := by
    funext j
    by_cases hj : j = i
    · subst hj
      simp [degDown, Function.update]
    · simp [degDown, Function.update, hj]
  have hprod : (∏ j, (p j) ^ ((degDown k i j : ℝ) / 2))
      = (p i) ^ (((k i - 1 : ℕ) : ℝ) / 2)
        * ∏ j ∈ (Finset.univ : Finset (Fin d)) \ {i}, (p j) ^ ((k j : ℝ) / 2) := by
    rw [hupd, Finset.prod_update_of_mem (Finset.mem_univ i)]
  have hsplit : (∏ j : Fin d, (p j) ^ ((k j : ℝ) / 2))
      = (p i) ^ ((k i : ℝ) / 2)
        * ∏ j ∈ (Finset.univ : Finset (Fin d)) \ {i}, (p j) ^ ((k j : ℝ) / 2) :=
    Finset.prod_eq_mul_prod_diff_singleton (Finset.mem_univ i) _
  have hcast : ((k i : ℝ) / 2) = (((k i - 1 : ℕ) : ℝ) / 2 + 1 / 2) := by
    have hsub : ((k i - 1 : ℕ) : ℝ) = (k i : ℝ) - 1 := by
      have : 1 ≤ k i := Nat.succ_le_of_lt hi
      rw [Nat.cast_sub this, Nat.cast_one]
    rw [hsub]
    ring
  have hsplitpow : (p i) ^ ((k i : ℝ) / 2)
      = (p i) ^ (((k i - 1 : ℕ) : ℝ) / 2) * Real.sqrt (p i) := by
    rw [hcast, Real.rpow_add (hp i), Real.sqrt_eq_rpow]
  rw [hsplit, hsplitpow, hprod]
  ring

/-! ## Creation and erasure weight identities (10)–(11) -/

private theorem mul_cancel_sq {x y z : ℝ} (hx : x ≠ 0) : x * (y / (x * z)) = y / z := by
  rw [mul_div_assoc']
  field_simp [hx]

/-- Creation identity (10): `√p_i · w_k = b_i · w_{k+e_i}`. -/
theorem create_weight_id (a : ℝ) {d : ℕ} (k : Fin d → ℕ) (i : Fin d)
    (p : Fin d → ℝ) (hp : ∀ j, 0 < p j) (ha : 0 < a) :
    (Real.sqrt (p i)) * weight a k p
      = createCoeff a k i * weight a (degUp k i) p := by
  unfold weight createCoeff
  rw [prod_pow_degUp p k i hp]
  have hd : 0 < d := by have := i.isLt; omega
  have hspos : 0 < postTotal a k := by
    unfold postTotal
    have h1 : (0 : ℝ) < a * d := mul_pos ha (by exact_mod_cast hd)
    have h2 : (0 : ℝ) ≤ degK k := Nat.cast_nonneg _
    linarith
  have hqpos : 0 < (a + k i) / postTotal a k := by
    have : (0 : ℝ) < a + k i := by
      have : (0 : ℝ) ≤ k i := Nat.cast_nonneg _
      linarith
    exact div_pos this hspos
  have hqne : Real.sqrt ((a + k i) / postTotal a k) ≠ 0 :=
    (Real.sqrt_pos.mpr hqpos).ne'
  have hsqrt : Real.sqrt (dirMoment a (degUp k i))
      = Real.sqrt ((a + k i) / postTotal a k) * Real.sqrt (dirMoment a k) := by
    have hratio := dirMoment_degUp a k i
    rw [hratio, Real.sqrt_mul (le_of_lt hqpos)]
  have hL : Real.sqrt (p i)
        * ((∏ j, (p j) ^ ((k j : ℝ) / 2)) / Real.sqrt (dirMoment a k))
      = (Real.sqrt (p i) * ∏ j, (p j) ^ ((k j : ℝ) / 2))
        / Real.sqrt (dirMoment a k) :=
    mul_div_assoc' _ _ _
  have hR : Real.sqrt ((a + k i) / postTotal a k)
        * ((Real.sqrt (p i) * ∏ j, (p j) ^ ((k j : ℝ) / 2))
            / Real.sqrt (dirMoment a (degUp k i)))
      = (Real.sqrt (p i) * ∏ j, (p j) ^ ((k j : ℝ) / 2))
        / Real.sqrt (dirMoment a k) := by
    rw [hsqrt]
    exact mul_cancel_sq hqne
  rw [hL, hR]

/-- Erasure identity (11): `√p_i · w_{k-e_i} = b_i⁻ · w_k`. -/
theorem erase_weight_id (a : ℝ) {d : ℕ} (k : Fin d → ℕ) (i : Fin d)
    (p : Fin d → ℝ) (hp : ∀ j, 0 < p j) (ha : 0 < a) (hk : 0 < k i) :
    (Real.sqrt (p i)) * weight a (degDown k i) p
      = eraseCoeff a k i * weight a k p := by
  unfold weight eraseCoeff
  rw [prod_pow_degDown p k i hp hk]
  have hd : 0 < d := by have := i.isLt; omega
  have hK : 1 ≤ degK k := one_le_degK_of_pos hk
  have hspos : 0 < postTotal a k - 1 := by
    unfold postTotal
    have h1 : (0 : ℝ) < a * d := mul_pos ha (by exact_mod_cast hd)
    have h2 : (1 : ℝ) ≤ degK k := by exact_mod_cast hK
    linarith
  have hnum : 0 < (a + k i - 1 : ℝ) := by
    have : (1 : ℝ) ≤ k i := by exact_mod_cast (Nat.succ_le_of_lt hk)
    have : (0 : ℝ) < a := ha
    linarith
  have hqpos : 0 < (a + k i - 1) / (postTotal a k - 1) :=
    div_pos hnum hspos
  have hqne : Real.sqrt ((a + k i - 1) / (postTotal a k - 1)) ≠ 0 :=
    (Real.sqrt_pos.mpr hqpos).ne'
  have hsqrt : Real.sqrt (dirMoment a k)
      = Real.sqrt ((a + k i - 1) / (postTotal a k - 1))
        * Real.sqrt (dirMoment a (degDown k i)) := by
    have hratio := dirMoment_degDown a k i hk
    rw [hratio, Real.sqrt_mul (le_of_lt hqpos)]
  have hL : Real.sqrt (p i)
        * ((∏ j, (p j) ^ ((degDown k i j : ℝ) / 2))
            / Real.sqrt (dirMoment a (degDown k i)))
      = (Real.sqrt (p i) * ∏ j, (p j) ^ ((degDown k i j : ℝ) / 2))
        / Real.sqrt (dirMoment a (degDown k i)) :=
    mul_div_assoc' _ _ _
  have hR : Real.sqrt ((a + k i - 1) / (postTotal a k - 1))
        * ((Real.sqrt (p i) * ∏ j, (p j) ^ ((degDown k i j : ℝ) / 2))
            / Real.sqrt (dirMoment a k))
      = (Real.sqrt (p i) * ∏ j, (p j) ^ ((degDown k i j : ℝ) / 2))
        / Real.sqrt (dirMoment a (degDown k i)) := by
    rw [hsqrt]
    -- goal: c * (Y / (c * M)) = Y / M
    exact mul_cancel_sq hqne
  rw [hL, hR]

end PUT
