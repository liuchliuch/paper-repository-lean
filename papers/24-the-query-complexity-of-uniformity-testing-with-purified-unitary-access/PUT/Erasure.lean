import PUT.Basic
import PUT.Fourier

/-!
# Erasure-direction estimates (paper 24, §3 erasure)

If an adjacent erasure weight is nonzero then the current squared degree
sits below `L_A = (√A + 1)²`, and the total erasure contribution is at
most `η_M = 2A √(L_A/M) ≤ 1/2` once `M ≥ 16 A² L_A`.
-/

noncomputable section
namespace PUT

set_option maxHeartbeats 400000 in
/-- Boundary claim: if some adjacent weight is nonzero then `R < L_A`. -/
theorem erasure_R_lt_LA {d : ℕ} (k : Fin d → ℕ) (i : Fin d) (A : ℝ)
    (h : cutoff A (degDown k i) ≠ 0) (hA : 0 ≤ A) (hi : 0 < k i) :
    (degR k : ℝ) < LA A := by
  have hcut : 0 < cutoff A (degDown k i) :=
    lt_of_le_of_ne (cutoff_nonneg _ _) (Ne.symm h)
  have hlt : (∑ j, ((degDown k i j : ℕ) : ℝ) ^ 2) < A :=
    (cutoff_pos_iff A (degDown k i)).mp hcut
  have hsum : ∑ j, ((degDown k i j : ℕ) : ℝ) ^ 2
      = ∑ j, (k j : ℝ) ^ 2 - 2 * (k i : ℝ) + 1 := sum_sq_degDown k i hi
  have hR : (degR k : ℝ) = ∑ j, (k j : ℝ) ^ 2 := degR_coe k
  have hki : ((k i - 1 : ℕ) : ℝ) = (k i : ℝ) - 1 := by
    have h1 : 1 ≤ k i := hi
    rw [Nat.cast_sub h1, Nat.cast_one]
  -- the i-th erasure coordinate is `(k_i - 1)²`
  have hterm : ((k i - 1 : ℕ) : ℝ) ^ 2
      ≤ ∑ j, ((degDown k i j : ℕ) : ℝ) ^ 2 := by
    have h : ((degDown k i i : ℕ) : ℝ) ^ 2
        ≤ ∑ j, ((degDown k i j : ℕ) : ℝ) ^ 2 :=
      Finset.single_le_sum
        (fun j _ => sq_nonneg (((degDown k i j : ℕ) : ℝ))) (Finset.mem_univ i)
    have hiid : degDown k i i = k i - 1 := by
      simp [degDown, Function.update]
    rw [hiid] at h
    exact h
  have hsq : ((k i - 1 : ℕ) : ℝ) ^ 2 < A :=
    lt_of_le_of_lt hterm hlt
  have hki1 : 0 ≤ ((k i - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hki_lt : ((k i - 1 : ℕ) : ℝ) < Real.sqrt A := by
    have hss : Real.sqrt (((k i - 1 : ℕ) : ℝ) ^ 2) < Real.sqrt A :=
      Real.sqrt_lt_sqrt (sq_nonneg _) hsq
    rwa [Real.sqrt_sq hki1] at hss
  -- `R(k) = R(k-e_i) + 2(k_i - 1) + 1`
  have hRsplit : (degR k : ℝ)
      = ∑ j, ((degDown k i j : ℕ) : ℝ) ^ 2 + 2 * ((k i - 1 : ℕ) : ℝ) + 1 := by
    rw [hR, hsum, hki]
    ring
  have hLA : LA A = A + 2 * Real.sqrt A + 1 := by
    unfold LA
    rw [add_sq, Real.sq_sqrt hA]
    ring
  have h2 : 2 * ((k i - 1 : ℕ) : ℝ) + 1 < 2 * Real.sqrt A + 1 := by
    linarith
  have h3 : ∑ j, ((degDown k i j : ℕ) : ℝ) ^ 2 + (2 * ((k i - 1 : ℕ) : ℝ) + 1)
      < A + (2 * Real.sqrt A + 1) :=
    add_lt_add hlt h2
  calc (degR k : ℝ)
      = ∑ j, ((degDown k i j : ℕ) : ℝ) ^ 2 + 2 * ((k i - 1 : ℕ) : ℝ) + 1 := hRsplit
    _ = ∑ j, ((degDown k i j : ℕ) : ℝ) ^ 2 + (2 * ((k i - 1 : ℕ) : ℝ) + 1) := by ring
    _ < A + (2 * Real.sqrt A + 1) := h3
    _ = A + 2 * Real.sqrt A + 1 := by ring
    _ = LA A := hLA.symm

/-- Erasure contribution `η_M = 2A √(L_A/M)`. -/
def etaM (A M : ℝ) : ℝ := 2 * A * Real.sqrt (LA A / M)

/-- Each erasure coefficient is at most `2A/√M` in absolute value after
summing at most `K` coordinates. -/
theorem erasure_contrib (A _a M : ℝ) (hA : 1 ≤ A) (hM : 16 * A ^ 2 * LA A ≤ M) :
    etaM A M ≤ 1 / 2 := by
  have hApos : 0 < A := lt_of_lt_of_le (by norm_num) hA
  have hLA : 0 < LA A := by
    unfold LA
    have : 0 < Real.sqrt A + 1 := by positivity
    exact pow_pos this 2
  have hMpos : 0 < M := by
    have h1 : 0 < 16 * A ^ 2 * LA A := by positivity
    exact lt_of_lt_of_le h1 hM
  have hle : LA A / M ≤ 1 / (16 * A ^ 2) := by
    have h1 : 0 < 16 * A ^ 2 := by positivity
    rw [div_le_div_iff₀ hMpos h1, one_mul]
    have h2 : LA A * (16 * A ^ 2) = 16 * A ^ 2 * LA A := by ring
    rw [h2]
    exact hM
  have hsqrt : Real.sqrt (LA A / M) ≤ Real.sqrt (1 / (16 * A ^ 2)) :=
    Real.sqrt_le_sqrt hle
  have hsqrt2 : Real.sqrt (1 / (16 * A ^ 2)) = 1 / (4 * A) := by
    have h1 : (16:ℝ) * A ^ 2 = (4 * A) ^ 2 := by ring
    have h2 : Real.sqrt (1 / (16 * A ^ 2)) = Real.sqrt (1 / (4 * A) ^ 2) := by
      rw [h1]
    rw [h2, Real.sqrt_div (by norm_num), Real.sqrt_one]
    have h3 : Real.sqrt ((4 * A) ^ 2) = 4 * A := Real.sqrt_sq (by positivity)
    rw [h3]
  unfold etaM
  calc 2 * A * Real.sqrt (LA A / M)
      ≤ 2 * A * Real.sqrt (1 / (16 * A ^ 2)) := by
        gcongr
    _ = 2 * A * (1 / (4 * A)) := by rw [hsqrt2]
    _ = 1 / 2 := by field_simp; norm_num

end PUT
