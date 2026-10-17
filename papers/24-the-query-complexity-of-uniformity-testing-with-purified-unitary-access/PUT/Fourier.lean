import PUT.Basic

/-!
# Fourier multi-indices, degree vectors, and the quadratic cutoff

Degree bookkeeping for paper 24: `degK k = ∑ k_i` is controlled by
`degR k = ∑ k_i²`, and the quadratic cutoff `α(k) = (A - R(k))₊` is
1-Lipschitz in each degree coordinate.
-/

noncomputable section
namespace PUT

/-! ## Degree sums -/

theorem degK_le_degR {d : ℕ} (k : Fin d → ℕ) : degK k ≤ degR k := by
  classical
  unfold degK degR
  refine Finset.sum_le_sum fun i _ => ?_
  rcases Nat.eq_zero_or_pos (k i) with h | h
  · rw [h]
    simp
  · have h1 : 1 ≤ k i := h
    calc k i = k i * 1 := by rw [mul_one]
      _ ≤ k i * k i := Nat.mul_le_mul_left _ h1
      _ = (k i) ^ 2 := by rw [sq]

theorem degK_sq_le {d : ℕ} (k : Fin d → ℕ) :
    (degK k : ℝ) ^ 2 ≤ d * ∑ i, (k i : ℝ) ^ 2 := by
  have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin d)))
    (f := fun i : Fin d => (k i : ℝ))
  rw [degK_coe]
  simpa [Finset.card_fin] using h

/-! ## Degree updates: sum of squares -/

/-- Squared degree after a creation step: `R(k+e_i) = R(k) + 2 k_i + 1`. -/
theorem sum_sq_degUp {d : ℕ} (k : Fin d → ℕ) (i : Fin d) :
    ∑ j, ((degUp k i j : ℕ) : ℝ) ^ 2
      = ∑ j, (k j : ℝ) ^ 2 + 2 * (k i : ℝ) + 1 := by
  have heq : (fun j : Fin d => ((degUp k i j : ℕ) : ℝ) ^ 2)
      = Function.update (fun j : Fin d => (k j : ℝ) ^ 2) i
          (((k i + 1 : ℕ) : ℝ) ^ 2) := by
    funext j
    by_cases hj : j = i
    · subst hj
      simp [degUp, Function.update]
    · simp [degUp, Function.update, hj]
  rw [heq, Finset.sum_update_of_mem (Finset.mem_univ i)]
  rw [Finset.sum_eq_sum_diff_singleton_add (Finset.mem_univ i) (fun j => (k j : ℝ) ^ 2)]
  have hcast : (((k i + 1 : ℕ) : ℝ) ^ 2) = ((k i : ℝ) + 1) ^ 2 := by norm_cast
  rw [hcast]
  ring

/-- Squared degree after an erasure step: `R(k-e_i) = R(k) - 2 k_i + 1` when `k_i > 0`. -/
theorem sum_sq_degDown {d : ℕ} (k : Fin d → ℕ) (i : Fin d) (hi : 0 < k i) :
    ∑ j, ((degDown k i j : ℕ) : ℝ) ^ 2
      = ∑ j, (k j : ℝ) ^ 2 - 2 * (k i : ℝ) + 1 := by
  have hcast : ((k i - 1 : ℕ) : ℝ) = (k i : ℝ) - 1 := by
    have h1 : 1 ≤ k i := hi
    rw [Nat.cast_sub h1, Nat.cast_one]
  have heq : (fun j : Fin d => ((degDown k i j : ℕ) : ℝ) ^ 2)
      = Function.update (fun j : Fin d => (k j : ℝ) ^ 2) i
          (((k i - 1 : ℕ) : ℝ) ^ 2) := by
    funext j
    by_cases hj : j = i
    · subst hj
      simp [degDown, Function.update]
    · simp [degDown, Function.update, hj]
  rw [heq, Finset.sum_update_of_mem (Finset.mem_univ i)]
  rw [Finset.sum_eq_sum_diff_singleton_add (Finset.mem_univ i) (fun j => (k j : ℝ) ^ 2)]
  rw [hcast]
  ring

/-! ## Quadratic cutoff -/

theorem cutoff_pos_iff {d : ℕ} (A : ℝ) (k : Fin d → ℕ) :
    0 < cutoff A k ↔ (∑ i, (k i : ℝ) ^ 2) < A := by
  unfold cutoff
  constructor
  · intro h
    rcases lt_or_ge (∑ i, (k i : ℝ) ^ 2) A with hlt | hle
    · exact hlt
    · exfalso
      have hz : max (A - ∑ i, (k i : ℝ) ^ 2) 0 = 0 := by
        apply max_eq_right
        linarith
      linarith
  · intro h
    have : A - ∑ i, (k i : ℝ) ^ 2 > 0 := by linarith
    have : max (A - ∑ i, (k i : ℝ) ^ 2) 0 = A - ∑ i, (k i : ℝ) ^ 2 :=
      max_eq_left (le_of_lt this)
    linarith

theorem cutoff_le_of_nonneg {d : ℕ} {A : ℝ} (hA : 0 ≤ A) (k : Fin d → ℕ) :
    cutoff A k ≤ A := by
  unfold cutoff
  apply max_le
  · have : (0 : ℝ) ≤ ∑ i, (k i : ℝ) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    linarith
  · exact hA

/-- Positive part is 1-Lipschitz: `|max x 0 - max y 0| ≤ |x - y|`. -/
theorem abs_max_zero_sub_le {x y : ℝ} : |max x 0 - max y 0| ≤ |x - y| :=
  abs_max_sub_max_le_abs x y 0

theorem cutoff_succ_le {d : ℕ} (A : ℝ) (k : Fin d → ℕ) (i : Fin d) :
    |cutoff A (degUp k i) - cutoff A k| ≤ 2 * (k i : ℝ) + 1 := by
  have hsum : ∑ j, ((degUp k i j : ℕ) : ℝ) ^ 2
      = ∑ j, (k j : ℝ) ^ 2 + 2 * (k i : ℝ) + 1 := sum_sq_degUp k i
  unfold cutoff
  rw [hsum]
  have hshift : A - (∑ j, (k j : ℝ) ^ 2 + 2 * (k i : ℝ) + 1)
      = (A - ∑ j, (k j : ℝ) ^ 2) - (2 * (k i : ℝ) + 1) := by ring
  rw [hshift]
  have hle := abs_max_zero_sub_le (x := (A - ∑ j, (k j : ℝ) ^ 2) - (2 * (k i : ℝ) + 1))
    (y := A - ∑ j, (k j : ℝ) ^ 2)
  refine le_trans hle ?_
  have habs : |((A - ∑ j, (k j : ℝ) ^ 2) - (2 * (k i : ℝ) + 1)) - (A - ∑ j, (k j : ℝ) ^ 2)|
      = 2 * (k i : ℝ) + 1 := by
    rw [sub_sub_cancel_left, abs_neg]
    exact abs_of_nonneg (by positivity)
  rw [habs]

theorem cutoff_pred_le {d : ℕ} (A : ℝ) (k : Fin d → ℕ) (i : Fin d) (hi : 0 < k i) :
    |cutoff A (degDown k i) - cutoff A k| ≤ 2 * (k i : ℝ) - 1 := by
  have hsum : ∑ j, ((degDown k i j : ℕ) : ℝ) ^ 2
      = ∑ j, (k j : ℝ) ^ 2 - 2 * (k i : ℝ) + 1 := sum_sq_degDown k i hi
  unfold cutoff
  rw [hsum]
  have hshift : A - (∑ j, (k j : ℝ) ^ 2 - 2 * (k i : ℝ) + 1)
      = (A - ∑ j, (k j : ℝ) ^ 2) + (2 * (k i : ℝ) - 1) := by ring
  rw [hshift]
  have hle := abs_max_zero_sub_le
    (x := (A - ∑ j, (k j : ℝ) ^ 2) + (2 * (k i : ℝ) - 1))
    (y := A - ∑ j, (k j : ℝ) ^ 2)
  refine le_trans hle ?_
  have habs : |((A - ∑ j, (k j : ℝ) ^ 2) + (2 * (k i : ℝ) - 1)) - (A - ∑ j, (k j : ℝ) ^ 2)|
      = 2 * (k i : ℝ) - 1 := by
    rw [add_sub_cancel_left]
    exact abs_of_nonneg (by
      have h1 : (1:ℝ) ≤ k i := by exact_mod_cast hi
      linarith)
  rw [habs]

/-! ## The `g` term -/

/-- Bound `g = √(1+4(K+R)/d) ≤ √(1+8A/d)` when `R < A` and `K ≤ R`. -/
theorem g_bound {d : ℕ} (k : Fin d → ℕ) (A : ℝ) (hR : (degR k : ℝ) < A)
    (hK : degK k ≤ degR k) :
    Real.sqrt (1 + 4 * ((degK k : ℝ) + degR k) / d)
      ≤ Real.sqrt (1 + 8 * A / d) := by
  have hcastK : ((degK k : ℝ) + degR k) = ((degK k + degR k : ℕ) : ℝ) := by
    norm_cast
  have hKle : (degK k : ℝ) ≤ degR k := by exact_mod_cast hK
  have hKR : (degK k : ℝ) + degR k ≤ 2 * A := by
    have : (degR k : ℝ) + degR k ≤ 2 * A := by nlinarith
    nlinarith
  have h4 : 4 * ((degK k : ℝ) + degR k) ≤ 8 * A := by nlinarith
  have hdiv : 4 * ((degK k : ℝ) + degR k) / d ≤ 8 * A / d := by
    rcases Nat.eq_zero_or_pos d with hd | hd
    · rw [show (d : ℝ) = 0 from by exact_mod_cast hd]
      simp
    · have hd' : (0:ℝ) < d := by exact_mod_cast hd
      exact div_le_div_of_nonneg_right h4 (le_of_lt hd')
  have hle : 1 + 4 * ((degK k : ℝ) + degR k) / d ≤ 1 + 8 * A / d := by
    linarith
  exact Real.sqrt_le_sqrt hle

end PUT
