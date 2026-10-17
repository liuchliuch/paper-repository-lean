import PsgEst.Basic

/-!
# Empirical lagged estimator

Section 2 of the paper: transition counts of the `k`-skipped chain,
incoming/outgoing degree normalization, empirical singular-value deficit
`â_k`, and the estimator `γ̂_n = max_k â_k / k`.

Main facts (paper (6)–(8)):
* `lhat_contraction`: `L̂` is a Euclidean contraction on every sample path.
* `lhat_sigma1_one`: `L̂ √c = √r` and `‖√c‖₂ = ‖√r‖₂`.
* `aHat_mem`: `0 ≤ â ≤ 1` for every data set.
* `lag_bound`: lag `k` contributes at most `1/k` to `γ̂_n`.
-/

open Matrix BigOperators Real Finset

namespace PsgEst

variable {d : ℕ}

/-! ## Transition counts -/

/-- Transition count matrix of a path `Y : Fin (m+1) → Fin d` (`m` transitions). -/
def countMat {m : ℕ} (Y : Fin (m + 1) → Fin d) : Matrix (Fin d) (Fin d) ℕ :=
  fun i j => ∑ t : Fin m, if Y t.castSucc = i ∧ Y t.succ = j then 1 else 0

/-- Outgoing degrees `r_i = ∑_j C_{ij}`. -/
def outDeg {m : ℕ} (Y : Fin (m + 1) → Fin d) : Fin d → ℕ := fun i =>
  ∑ j, countMat Y i j

/-- Incoming degrees `c_j = ∑_i C_{ij}`. -/
def inDeg {m : ℕ} (Y : Fin (m + 1) → Fin d) : Fin d → ℕ := fun j =>
  ∑ i, countMat Y i j

lemma countMat_apply {m : ℕ} (Y : Fin (m + 1) → Fin d) (i j : Fin d) :
    countMat Y i j = ∑ t : Fin m, if Y t.castSucc = i ∧ Y t.succ = j then 1 else 0 := rfl

lemma outDeg_eq {m : ℕ} (Y : Fin (m + 1) → Fin d) (i : Fin d) :
    outDeg Y i = ∑ j, countMat Y i j := rfl

lemma inDeg_eq {m : ℕ} (Y : Fin (m + 1) → Fin d) (j : Fin d) :
    inDeg Y j = ∑ i, countMat Y i j := rfl

lemma countMat_nonneg {m : ℕ} (Y : Fin (m + 1) → Fin d) (i j : Fin d) :
    0 ≤ (countMat Y i j : ℝ) :=
  Nat.cast_nonneg _

/-- Each of the `m` transitions is counted exactly once, so total counts equal `m`. -/
lemma sum_sum_countMat {m : ℕ} (Y : Fin (m + 1) → Fin d) :
    ∑ i, ∑ j, countMat Y i j = m := by
  have h2 : ∀ (t : Fin m) (i j : Fin d),
      (if Y t.castSucc = i ∧ Y t.succ = j then (1:ℕ) else 0)
        = if (i, j) = (Y t.castSucc, Y t.succ) then 1 else 0 := by
    intro t i j
    by_cases hp : (i, j) = (Y t.castSucc, Y t.succ)
    · obtain ⟨hi, hj⟩ := Prod.mk.inj hp
      simp [hi, hj]
    · have hneg : ¬(Y t.castSucc = i ∧ Y t.succ = j) := by
        rintro ⟨ha, hb⟩
        apply hp
        exact Prod.ext ha.symm hb.symm
      simp [hneg, hp]
  have h3 : ∑ i, ∑ j, countMat Y i j
      = ∑ i, ∑ j, ∑ t : Fin m, (if Y t.castSucc = i ∧ Y t.succ = j then (1:ℕ) else 0) := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rfl
  rw [h3]
  have h4 : ∀ i j, (∑ t : Fin m, (if Y t.castSucc = i ∧ Y t.succ = j then (1:ℕ) else 0))
      = ∑ t : Fin m, (if (i, j) = (Y t.castSucc, Y t.succ) then (1:ℕ) else 0) := by
    intro i j
    apply Finset.sum_congr rfl
    intro t _
    exact h2 t i j
  have h5 : ∑ i, ∑ j, ∑ t : Fin m, (if Y t.castSucc = i ∧ Y t.succ = j then (1:ℕ) else 0)
      = ∑ i, ∑ j, ∑ t : Fin m, (if (i, j) = (Y t.castSucc, Y t.succ) then (1:ℕ) else 0) := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    exact h4 i j
  rw [h5]
  have h6 : ∑ i, ∑ j, ∑ t : Fin m, (if (i, j) = (Y t.castSucc, Y t.succ) then (1:ℕ) else 0)
      = ∑ t : Fin m, ∑ i, ∑ j, (if (i, j) = (Y t.castSucc, Y t.succ) then (1:ℕ) else 0) := by
    rw [Finset.sum_comm]
    rw [show (∑ j, ∑ i, ∑ t : Fin m, (if (i, j) = (Y t.castSucc, Y t.succ) then (1:ℕ) else 0))
        = ∑ j, ∑ t : Fin m, ∑ i, (if (i, j) = (Y t.castSucc, Y t.succ) then (1:ℕ) else 0) by
      apply Finset.sum_congr rfl
      intro j _
      exact Finset.sum_comm]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro t _
    rw [Finset.sum_comm]
  rw [h6]
  have h7 : ∀ t : Fin m,
      ∑ i, ∑ j, (if (i, j) = (Y t.castSucc, Y t.succ) then (1:ℕ) else 0) = 1 := by
    intro t
    have h7a : ∑ i, ∑ j, (if (i, j) = (Y t.castSucc, Y t.succ) then (1:ℕ) else 0)
        = ∑ p : Fin d × Fin d, (if p = (Y t.castSucc, Y t.succ) then (1:ℕ) else 0) := by
      rw [← Finset.sum_product']
      rfl
    rw [h7a, Finset.sum_ite_eq']
    simp
  rw [Finset.sum_congr rfl (fun t _ => h7 t)]
  simp

lemma sum_outDeg {m : ℕ} (Y : Fin (m + 1) → Fin d) : ∑ i, outDeg Y i = m := by
  have : ∑ i, outDeg Y i = ∑ i, ∑ j, countMat Y i j :=
    Finset.sum_congr rfl (fun _ _ => rfl)
  rw [this, sum_sum_countMat]

lemma sum_inDeg {m : ℕ} (Y : Fin (m + 1) → Fin d) : ∑ j, inDeg Y j = m := by
  have : ∑ j, inDeg Y j = ∑ j, ∑ i, countMat Y i j :=
    Finset.sum_congr rfl (fun _ _ => rfl)
  rw [this, Finset.sum_comm, sum_sum_countMat]

lemma sum_outDeg_eq_sum_inDeg {m : ℕ} (Y : Fin (m + 1) → Fin d) :
    ∑ i, outDeg Y i = ∑ j, inDeg Y j := by rw [sum_outDeg, sum_inDeg]

/-- Real cast of `outDeg` equals the real row sums of the count matrix. -/
lemma outDeg_cast {m : ℕ} (Y : Fin (m + 1) → Fin d) (i : Fin d) :
    (outDeg Y i : ℝ) = ∑ j, ((countMat Y i j : ℕ) : ℝ) := by
  rw [outDeg_eq, Nat.cast_sum]

/-- Real cast of `inDeg` equals the real column sums of the count matrix. -/
lemma inDeg_cast {m : ℕ} (Y : Fin (m + 1) → Fin d) (j : Fin d) :
    (inDeg Y j : ℝ) = ∑ i, ((countMat Y i j : ℕ) : ℝ) := by
  rw [inDeg_eq, Nat.cast_sum]

/-! ## Skipped path -/

/-- Skipped path `Y_t = X_{t k}` for `t ≤ m` where `m = n / k`. -/
def skipPath {n : ℕ} (X : Fin (n + 1) → Fin d) (k : ℕ) : Fin (n / k + 1) → Fin d :=
  fun t => X ⟨t.val * k, by
    have ht : (t : ℕ) < n / k + 1 := t.isLt
    have hmul : (t : ℕ) * k ≤ n / k * k :=
      Nat.mul_le_mul_right k (Nat.le_of_lt_succ ht)
    have hle : n / k * k ≤ n := by
      rw [Nat.mul_comm]; exact Nat.mul_div_le n k
    omega⟩

/-! ## Normalized operator `L̂` -/

/-- All degrees positive. -/
def degPos {m : ℕ} (Y : Fin (m + 1) → Fin d) : Prop :=
  ∀ i, 0 < outDeg Y i ∧ 0 < inDeg Y i

lemma degPos_iff {m : ℕ} (Y : Fin (m + 1) → Fin d) :
    degPos Y ↔ ∀ i, 0 < outDeg Y i ∧ 0 < inDeg Y i := Iff.rfl

/-- Real count matrix used inside `L̂`. -/
abbrev countMatR {m : ℕ} (Y : Fin (m + 1) → Fin d) : Matrix (Fin d) (Fin d) ℝ :=
  (countMat Y).map (Nat.cast : ℕ → ℝ)

lemma countMatR_apply {m : ℕ} (Y : Fin (m + 1) → Fin d) (i j : Fin d) :
    countMatR Y i j = (countMat Y i j : ℝ) := rfl

lemma countMatR_nonneg {m : ℕ} (Y : Fin (m + 1) → Fin d) (i j : Fin d) :
    0 ≤ countMatR Y i j :=
  countMat_nonneg Y i j

lemma countMatR_row_sum {m : ℕ} (Y : Fin (m + 1) → Fin d) (i : Fin d) :
    ∑ j, countMatR Y i j = (outDeg Y i : ℝ) := by
  have h : ∑ j, countMatR Y i j = ∑ j, ((countMat Y i j : ℕ) : ℝ) :=
    Finset.sum_congr rfl (fun j _ => rfl)
  rw [h, outDeg_cast]

lemma countMatR_col_sum {m : ℕ} (Y : Fin (m + 1) → Fin d) (j : Fin d) :
    ∑ i, countMatR Y i j = (inDeg Y j : ℝ) := by
  have h : ∑ i, countMatR Y i j = ∑ i, ((countMat Y i j : ℕ) : ℝ) :=
    Finset.sum_congr rfl (fun i _ => rfl)
  rw [h, inDeg_cast]

/-- Empirical normalized operator `L̂ = diag(r)^{-1/2} C diag(c)^{-1/2}` (real entries).
Defined as the zero matrix when some degree is zero. -/
noncomputable def lHat {m : ℕ} (Y : Fin (m + 1) → Fin d) : Matrix (Fin d) (Fin d) ℝ :=
  if _h : ∀ i, 0 < outDeg Y i ∧ 0 < inDeg Y i then
    diagonal (fun i => ((outDeg Y i : ℝ)) ^ (-(1 / 2 : ℝ)))
      * (countMatR Y)
      * diagonal (fun j => ((inDeg Y j : ℝ)) ^ (-(1 / 2 : ℝ)))
  else 0

/-- When all degrees are positive, `L̂` is the real matrix formula. -/
lemma lHat_eq_of_degPos {m : ℕ} (Y : Fin (m + 1) → Fin d) (h : degPos Y) :
    lHat Y =
      diagonal (fun i => ((outDeg Y i : ℝ)) ^ (-(1 / 2 : ℝ)))
        * (countMatR Y)
        * diagonal (fun j => ((inDeg Y j : ℝ)) ^ (-(1 / 2 : ℝ))) := by
  have h' : ∀ i, 0 < outDeg Y i ∧ 0 < inDeg Y i := h
  show (if _ : _ then _ else _) = _
  rw [dif_pos h']

lemma lHat_eq_zero_of_not_degPos {m : ℕ} (Y : Fin (m + 1) → Fin d) (h : ¬degPos Y) :
    lHat Y = 0 := by
  have h' : ¬ ∀ i, 0 < outDeg Y i ∧ 0 < inDeg Y i := h
  show (if _ : _ then _ else _) = _
  rw [dif_neg h']

/-! ## Empirical deficit `â` and estimator `γ̂` -/

open Classical in
/-- Empirical singular-value deficit `â = 1 - σ_2(L̂)^2`, or `0` if some degree vanishes. -/
noncomputable def aHat {m : ℕ} (Y : Fin (m + 1) → Fin d) : ℝ :=
  if degPos Y then aOf (lHat Y) else 0

lemma aHat_eq_of_degPos {m : ℕ} (Y : Fin (m + 1) → Fin d) (h : degPos Y) :
    aHat Y = aOf (lHat Y) := by
  simp [aHat, h]

lemma aHat_eq_zero_of_not_degPos {m : ℕ} (Y : Fin (m + 1) → Fin d) (h : ¬degPos Y) :
    aHat Y = 0 := by
  simp [aHat, h]

/-- Estimator `γ̂_n = max_{1 ≤ k ≤ n} â_k / k` (and `γ̂_0 = 0`). -/
noncomputable def gammaHat {n : ℕ} (X : Fin (n + 1) → Fin d) : ℝ :=
  match n with
  | 0 => 0
  | n+1 =>
    ((List.range (n+2)).map (fun k =>
      if 0 < k then aHat (skipPath X k) / k else 0)).foldl max 0

/-! ## Weighted Cauchy–Schwarz and `rpow` helpers -/

/-- Weighted Cauchy–Schwarz: for `a_j ≥ 0`,
`(∑ j, a j * v j) ^ 2 ≤ (∑ j, a j) * ∑ j, a j * v j ^ 2`. -/
theorem weighted_cauchy {ι : Type*} [Fintype ι] {a v : ι → ℝ}
    (ha : ∀ j, 0 ≤ a j) :
    (∑ j, a j * v j) ^ 2 ≤ (∑ j, a j) * ∑ j, a j * v j ^ 2 := by
  classical
  exact Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul (Finset.univ)
    (fun j _ => ha j) (fun j _ => mul_nonneg (ha j) (sq_nonneg (v j)))
    (fun j _ => by ring)

lemma rpow_neg_half_sq (x : ℝ) (hx : 0 < x) :
    x ^ (-(1 / 2 : ℝ)) * x ^ (-(1 / 2 : ℝ)) = x ^ (-1 : ℝ) := by
  rw [← Real.rpow_add hx]
  ring_nf

lemma rpow_neg_half_mul (x : ℝ) (hx : 0 < x) :
    x ^ (-(1 / 2 : ℝ)) * x = x ^ ((1:ℝ) / 2) := by
  calc x ^ (-(1 / 2 : ℝ)) * x
      = x ^ (-(1 / 2 : ℝ)) * x ^ (1 : ℝ) := by rw [Real.rpow_one]
    _ = x ^ ((1:ℝ) / 2) := by rw [← Real.rpow_add hx]; ring_nf

lemma rpow_neg_half_cancel (x : ℝ) (hx : 0 < x) :
    x ^ (-(1 / 2 : ℝ)) * x ^ ((1:ℝ) / 2) = 1 := by
  rw [← Real.rpow_add hx]
  ring_nf
  rw [Real.rpow_zero]

lemma rpow_half_sq (x : ℝ) (hx : 0 < x) :
    x ^ ((1:ℝ) / 2) * x ^ ((1:ℝ) / 2) = x := by
  rw [← Real.rpow_add hx]
  ring_nf
  rw [Real.rpow_one]

/-! ## Contractivity of `L̂` -/

/-- Vector formula for `L̂ *ᵥ u`. -/
lemma lHat_vec {m : ℕ} (Y : Fin (m + 1) → Fin d) (hpos : degPos Y) (u : Fin d → ℝ) (i : Fin d) :
    (lHat Y *ᵥ u) i = (outDeg Y i : ℝ) ^ (-(1 / 2 : ℝ))
        * ∑ j, countMatR Y i j * ((inDeg Y j : ℝ) ^ (-(1 / 2 : ℝ)) * u j) := by
  rw [lHat_eq_of_degPos Y hpos]
  have h1 : ((diagonal (fun i => (outDeg Y i : ℝ) ^ (-(1 / 2 : ℝ)))
      * countMatR Y * diagonal (fun j => (inDeg Y j : ℝ) ^ (-(1 / 2 : ℝ)))) *ᵥ u)
      = diagonal (fun i => (outDeg Y i : ℝ) ^ (-(1 / 2 : ℝ)))
          *ᵥ (countMatR Y *ᵥ (diagonal (fun j => (inDeg Y j : ℝ) ^ (-(1 / 2 : ℝ))) *ᵥ u)) := by
    rw [mulVec_mulVec, mulVec_mulVec]
  rw [h1]
  simp only [mulVec_diagonal]
  -- (countMatR Y *ᵥ w) i = ∑ j, countMatR Y i j * w j
  have hmv : ∀ (M : Matrix (Fin d) (Fin d) ℝ) (w : Fin d → ℝ) (i : Fin d),
      (M *ᵥ w) i = ∑ j, M i j * w j := fun _ _ _ => rfl
  rw [hmv]
  simp only [mulVec_diagonal, Finset.mul_sum]

/-- Per-row bound from weighted Cauchy–Schwarz. -/
lemma row_bound {m : ℕ} (Y : Fin (m + 1) → Fin d) (hpos : degPos Y) (u : Fin d → ℝ) (i : Fin d) :
    ((outDeg Y i : ℝ) ^ (-(1 / 2 : ℝ))
        * ∑ j, countMatR Y i j * ((inDeg Y j : ℝ) ^ (-(1 / 2 : ℝ)) * u j)) ^ 2
      ≤ ∑ j, countMatR Y i j * u j ^ 2 / (inDeg Y j : ℝ) := by
  have hr : 0 < (outDeg Y i : ℝ) := Nat.cast_pos.mpr (hpos i).1
  have hc : ∀ j, 0 < (inDeg Y j : ℝ) := fun j => Nat.cast_pos.mpr (hpos j).2
  have hC : ∀ j, 0 ≤ countMatR Y i j := fun j => Nat.cast_nonneg _
  have hwc : (∑ j, countMatR Y i j * ((inDeg Y j : ℝ) ^ (-(1 / 2 : ℝ)) * u j)) ^ 2
      ≤ (∑ j, countMatR Y i j) * ∑ j, countMatR Y i j * ((inDeg Y j : ℝ) ^ (-(1 / 2 : ℝ)) * u j) ^ 2 :=
    Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul _
      (fun j _ => hC j)
      (fun j _ => mul_nonneg (hC j) (sq_nonneg _))
      (fun j _ => by ring)
  have hrow : ∑ j, countMatR Y i j = (outDeg Y i : ℝ) := countMatR_row_sum Y i
  rw [hrow] at hwc
  have hpow : (outDeg Y i : ℝ) ^ (-(1 / 2 : ℝ)) * (outDeg Y i : ℝ) ^ (-(1 / 2 : ℝ))
      = (outDeg Y i : ℝ) ^ (-1 : ℝ) := rpow_neg_half_sq _ hr
  have hsq : ((outDeg Y i : ℝ) ^ (-(1 / 2 : ℝ))
      * ∑ j, countMatR Y i j * ((inDeg Y j : ℝ) ^ (-(1 / 2 : ℝ)) * u j)) ^ 2
      = (outDeg Y i : ℝ) ^ (-1 : ℝ)
          * (∑ j, countMatR Y i j * ((inDeg Y j : ℝ) ^ (-(1 / 2 : ℝ)) * u j)) ^ 2 := by
    calc ((outDeg Y i : ℝ) ^ (-(1 / 2 : ℝ))
        * ∑ j, countMatR Y i j * ((inDeg Y j : ℝ) ^ (-(1 / 2 : ℝ)) * u j)) ^ 2
        = ((outDeg Y i : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2
            * (∑ j, countMatR Y i j * ((inDeg Y j : ℝ) ^ (-(1 / 2 : ℝ)) * u j)) ^ 2 :=
          mul_pow _ _ _
      _ = ((outDeg Y i : ℝ) ^ (-(1 / 2 : ℝ)) * (outDeg Y i : ℝ) ^ (-(1 / 2 : ℝ)))
            * (∑ j, countMatR Y i j * ((inDeg Y j : ℝ) ^ (-(1 / 2 : ℝ)) * u j)) ^ 2 := by
          rw [pow_two]
      _ = (outDeg Y i : ℝ) ^ (-1 : ℝ)
            * (∑ j, countMatR Y i j * ((inDeg Y j : ℝ) ^ (-(1 / 2 : ℝ)) * u j)) ^ 2 := by
          rw [hpow]
  rw [hsq]
  have hneg : 0 < (outDeg Y i : ℝ) ^ (-1 : ℝ) := by
    rw [Real.rpow_neg_one]; exact inv_pos.mpr hr
  have hmul : (outDeg Y i : ℝ) ^ (-1 : ℝ)
      * (∑ j, countMatR Y i j * ((inDeg Y j : ℝ) ^ (-(1 / 2 : ℝ)) * u j)) ^ 2
      ≤ (outDeg Y i : ℝ) ^ (-1 : ℝ)
          * ((outDeg Y i : ℝ) * ∑ j, countMatR Y i j * ((inDeg Y j : ℝ) ^ (-(1 / 2 : ℝ)) * u j) ^ 2) :=
    mul_le_mul_of_nonneg_left hwc (le_of_lt hneg)
  have hcancel : (outDeg Y i : ℝ) ^ (-1 : ℝ)
      * ((outDeg Y i : ℝ) * ∑ j, countMatR Y i j * ((inDeg Y j : ℝ) ^ (-(1 / 2 : ℝ)) * u j) ^ 2)
      = ∑ j, countMatR Y i j * ((inDeg Y j : ℝ) ^ (-(1 / 2 : ℝ)) * u j) ^ 2 := by
    rw [← mul_assoc]
    have : (outDeg Y i : ℝ) ^ (-1 : ℝ) * (outDeg Y i : ℝ) = 1 := by
      have h1 : (outDeg Y i : ℝ) ^ (-1 : ℝ) * (outDeg Y i : ℝ)
          = (outDeg Y i : ℝ) ^ (-1 : ℝ) * (outDeg Y i : ℝ) ^ (1 : ℝ) := by
        rw [Real.rpow_one]
      rw [h1, ← Real.rpow_add hr]
      ring_nf
      rw [Real.rpow_zero]
    rw [this, one_mul]
  rw [hcancel] at hmul
  have hv : ∀ j, ((inDeg Y j : ℝ) ^ (-(1 / 2 : ℝ)) * u j) ^ 2
      = u j ^ 2 / (inDeg Y j : ℝ) := by
    intro j
    have hj : 0 < (inDeg Y j : ℝ) := hc j
    have h1 : (inDeg Y j : ℝ) ^ (-(1 / 2 : ℝ)) * (inDeg Y j : ℝ) ^ (-(1 / 2 : ℝ))
        = (inDeg Y j : ℝ) ^ (-1 : ℝ) := rpow_neg_half_sq _ hj
    calc ((inDeg Y j : ℝ) ^ (-(1 / 2 : ℝ)) * u j) ^ 2
        = ((inDeg Y j : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 * u j ^ 2 := mul_pow _ _ _
      _ = ((inDeg Y j : ℝ) ^ (-(1 / 2 : ℝ)) * (inDeg Y j : ℝ) ^ (-(1 / 2 : ℝ))) * u j ^ 2 := by
          rw [pow_two]
      _ = (inDeg Y j : ℝ) ^ (-1 : ℝ) * u j ^ 2 := by rw [h1]
      _ = u j ^ 2 / (inDeg Y j : ℝ) := by rw [Real.rpow_neg_one]; ring
  refine hmul.trans_eq (Finset.sum_congr rfl fun j _ => ?_)
  rw [hv]
  ring

/-- Contractivity: for nonnegative `C` with positive row sums `r` and column sums `c`,
`L = diag(r)^{-1/2} C diag(c)^{-1/2}` satisfies `‖L u‖₂ ≤ ‖u‖₂`. -/
theorem lhat_contraction {m : ℕ} (Y : Fin (m + 1) → Fin d)
    (hpos : degPos Y) (u : Fin d → ℝ) :
    (∑ i, (lHat Y *ᵥ u) i ^ 2) ≤ ∑ i, u i ^ 2 := by
  classical
  have hstep : ∀ i, (lHat Y *ᵥ u) i ^ 2
      ≤ ∑ j, countMatR Y i j * u j ^ 2 / (inDeg Y j : ℝ) := by
    intro i
    rw [lHat_vec Y hpos u i]
    exact row_bound Y hpos u i
  have hsum : ∑ i, (lHat Y *ᵥ u) i ^ 2
      ≤ ∑ i, ∑ j, countMatR Y i j * u j ^ 2 / (inDeg Y j : ℝ) :=
    Finset.sum_le_sum (fun i _ => hstep i)
  have htotal : ∑ i, ∑ j, countMatR Y i j * u j ^ 2 / (inDeg Y j : ℝ) = ∑ j, u j ^ 2 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    -- ∑ i, (C i j * u j^2) / c j = (∑ i, C i j * u j^2) / c j
    rw [← Finset.sum_div]
    -- = (c j * u j^2) / c j = u j^2
    have h1 : ∑ i, countMatR Y i j * u j ^ 2 = (inDeg Y j : ℝ) * u j ^ 2 := by
      rw [← Finset.sum_mul, countMatR_col_sum Y j]
    rw [h1]
    have hcj : 0 < (inDeg Y j : ℝ) := Nat.cast_pos.mpr (hpos j).2
    rw [div_eq_mul_inv, mul_comm (inDeg Y j : ℝ), mul_assoc,
      mul_inv_cancel₀ (ne_of_gt hcj), mul_one]
  calc ∑ i, (lHat Y *ᵥ u) i ^ 2
      ≤ ∑ i, ∑ j, countMatR Y i j * u j ^ 2 / (inDeg Y j : ℝ) := hsum
    _ = ∑ j, u j ^ 2 := htotal

/-! ## Singular value one -/

/-- `L̂ √c = √r` and `‖√c‖₂ = ‖√r‖₂`, hence `σ_1(L̂) = 1`. -/
theorem lhat_sigma1_one {m : ℕ} (Y : Fin (m + 1) → Fin d) (hpos : degPos Y) :
    (lHat Y *ᵥ fun j => ((inDeg Y j : ℝ)) ^ ((1:ℝ) / 2))
      = (fun i => ((outDeg Y i : ℝ)) ^ ((1:ℝ) / 2))
    ∧ (∑ i, (((inDeg Y i : ℝ)) ^ ((1:ℝ) / 2)) ^ 2)
        = ∑ i, (((outDeg Y i : ℝ)) ^ ((1:ℝ) / 2)) ^ 2 := by
  classical
  have hr : ∀ i, 0 < (outDeg Y i : ℝ) := fun i =>
    Nat.cast_pos.mpr (hpos i).1
  have hc : ∀ j, 0 < (inDeg Y j : ℝ) := fun j =>
    Nat.cast_pos.mpr (hpos j).2
  -- First conjunct: L̂ √c = √r
  have hvec : lHat Y *ᵥ (fun j => (inDeg Y j : ℝ) ^ ((1:ℝ) / 2))
      = fun i => (outDeg Y i : ℝ) ^ ((1:ℝ) / 2) := by
    ext i
    rw [lHat_vec Y hpos _ i]
    have hinner : ∀ j, (inDeg Y j : ℝ) ^ (-(1 / 2 : ℝ))
        * (inDeg Y j : ℝ) ^ ((1:ℝ) / 2) = 1 := fun j =>
      rpow_neg_half_cancel _ (hc j)
    have hsum : ∑ j, countMatR Y i j * ((inDeg Y j : ℝ) ^ (-(1 / 2 : ℝ))
        * (inDeg Y j : ℝ) ^ ((1:ℝ) / 2)) = ∑ j, countMatR Y i j := by
      apply Finset.sum_congr rfl
      intro j _
      rw [hinner, mul_one]
    rw [hsum, countMatR_row_sum Y i]
    exact rpow_neg_half_mul _ (hr i)
  -- Second conjunct: ‖√c‖² = ‖√r‖²
  have hnorm : (∑ i, ((inDeg Y i : ℝ) ^ ((1:ℝ) / 2)) ^ 2)
      = ∑ i, ((outDeg Y i : ℝ) ^ ((1:ℝ) / 2)) ^ 2 := by
    have hcj : ∀ j, ((inDeg Y j : ℝ) ^ ((1:ℝ) / 2)) ^ 2 = (inDeg Y j : ℝ) := by
      intro j
      rw [pow_two, rpow_half_sq _ (hc j)]
    have hri : ∀ i, ((outDeg Y i : ℝ) ^ ((1:ℝ) / 2)) ^ 2 = (outDeg Y i : ℝ) := by
      intro i
      rw [pow_two, rpow_half_sq _ (hr i)]
    rw [Finset.sum_congr rfl (fun j _ => hcj j),
      Finset.sum_congr rfl (fun i _ => hri i)]
    have hcc : ∑ j, (inDeg Y j : ℝ) = ∑ i, (outDeg Y i : ℝ) := by
      have h3 : ∑ j, (inDeg Y j : ℝ) = ∑ j, ∑ i, countMatR Y i j := by
        apply Finset.sum_congr rfl; intro j _; exact (countMatR_col_sum Y j).symm
      have h4 : ∑ i, (outDeg Y i : ℝ) = ∑ i, ∑ j, countMatR Y i j := by
        apply Finset.sum_congr rfl; intro i _; exact (countMatR_row_sum Y i).symm
      rw [h3, h4, Finset.sum_comm]
    exact hcc
  exact ⟨hvec, hnorm⟩

/-! ## Deterministic range `0 ≤ â ≤ 1` -/

/-- `v · (Lᵀ L v) = ‖L v‖²` for real vectors. -/
private lemma dotProduct_gram {d : ℕ} (L : Matrix (Fin d) (Fin d) ℝ) (v : Fin d → ℝ) :
    ∑ i, v i * ((L.transpose * L) *ᵥ v) i = ∑ i, (L *ᵥ v) i ^ 2 := by
  have hvec : (L.transpose * L) *ᵥ v = L.transpose *ᵥ (L *ᵥ v) := by
    rw [mulVec_mulVec]
  have hT : ∀ w : Fin d → ℝ, ∀ i, (L.transpose *ᵥ w) i = ∑ k, w k * L k i := by
    intro w i
    rw [mulVec_transpose]
    rfl
  rw [hvec]
  have hstep : ∀ i, v i * (L.transpose *ᵥ (L *ᵥ v)) i
      = v i * ∑ k, (L *ᵥ v) k * L k i := by
    intro i
    rw [hT]
  rw [Finset.sum_congr rfl (fun i _ => hstep i)]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  have hmv : (L *ᵥ v) k = ∑ i, L k i * v i := rfl
  calc ∑ i, v i * ((L *ᵥ v) k * L k i)
      = ∑ i, (L *ᵥ v) k * (L k i * v i) := by
        apply Finset.sum_congr rfl; intro i _; ring
    _ = (L *ᵥ v) k * ∑ i, L k i * v i := by rw [Finset.mul_sum]
    _ = (L *ᵥ v) k * (L *ᵥ v) k := by rw [← hmv]
    _ = (L *ᵥ v) k ^ 2 := by ring

/-- Eigenvector basis of `Lᵀ L` has unit Euclidean norm. -/
private lemma eigvec_norm {d : ℕ} [DecidableEq (Fin d)]
    (L : Matrix (Fin d) (Fin d) ℝ) (j : Fin d) :
    ∑ i, ((gram_isHermitian L).eigenvectorBasis j i) ^ 2 = 1 := by
  have hA := gram_isHermitian L
  have hone := hA.eigenvectorBasis.orthonormal.1 j
  have hL2 : ‖(hA.eigenvectorBasis j : EuclideanSpace ℝ (Fin d))‖ ^ 2
      = ∑ i, ‖((hA.eigenvectorBasis j : EuclideanSpace ℝ (Fin d)) i)‖ ^ 2 :=
    PiLp.norm_sq_eq_of_L2 _ _
  have hsq : ‖(hA.eigenvectorBasis j : EuclideanSpace ℝ (Fin d))‖ ^ 2 = 1 := by
    rw [hone]; ring
  have hconv : ∀ i, ‖((hA.eigenvectorBasis j : EuclideanSpace ℝ (Fin d)) i)‖ ^ 2
      = (((hA.eigenvectorBasis j : EuclideanSpace ℝ (Fin d)) i) : ℝ) ^ 2 := by
    intro i
    rw [Real.norm_eq_abs, sq_abs]
  have hL2' : ‖(hA.eigenvectorBasis j : EuclideanSpace ℝ (Fin d))‖ ^ 2
      = ∑ i, (((hA.eigenvectorBasis j : EuclideanSpace ℝ (Fin d)) i) : ℝ) ^ 2 := by
    rw [hL2]
    exact Finset.sum_congr rfl (fun i _ => hconv i)
  rw [← hL2', hsq]

/-- Eigenvalues of `Lᵀ L` are at most `1` when `L` is a Euclidean contraction. -/
theorem gramEig_le_one {d : ℕ} [DecidableEq (Fin d)]
    (L : Matrix (Fin d) (Fin d) ℝ)
    (h : ∀ u : Fin d → ℝ, (∑ i, (L *ᵥ u) i ^ 2) ≤ ∑ i, u i ^ 2)
    (j : Fin d) :
    gramEig L j ≤ 1 := by
  classical
  have hA : (gram L).IsHermitian := gram_isHermitian L
  set v : Fin d → ℝ := fun i => ((hA.eigenvectorBasis j) i)
  have hmul : (gram L) *ᵥ v = (gramEig L j) • v := by
    have := hA.mulVec_eigenvectorBasis j
    ext i
    simp only [Pi.smul_apply, smul_eq_mul]
    have := congrFun this i
    simpa [v] using this
  have hnorm : ∑ i, v i ^ 2 = 1 := eigvec_norm L j
  have hray : (gramEig L j) * (∑ i, v i ^ 2) = ∑ i, (L *ᵥ v) i ^ 2 := by
    have hAapp : ∀ i, ((gram L) *ᵥ v) i = (gramEig L j) * v i := by
      intro i
      rw [hmul, Pi.smul_apply]
      simp [smul_eq_mul]
    have hleft : ∑ i, v i * ((gram L) *ᵥ v) i = (gramEig L j) * ∑ i, v i ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [hAapp]
      ring
    have hgram : gram L = L.transpose * L := rfl
    rw [← hleft, hgram]
    exact dotProduct_gram L v
  have hle : ∑ i, (L *ᵥ v) i ^ 2 ≤ ∑ i, v i ^ 2 := h v
  rw [← hray] at hle
  have hn0 : (0 : ℝ) < ∑ i, v i ^ 2 := by rw [hnorm]; norm_num
  have hle' : (∑ i, v i ^ 2) * gramEig L j ≤ ∑ i, v i ^ 2 := by
    rw [mul_comm]; exact hle
  exact (mul_le_iff_le_one_right hn0).mp hle'

/-- All singular values of `L` lie in `[0, 1]` when `L` is a Euclidean contraction. -/
theorem sval_mem_of_contraction {d : ℕ} [DecidableEq (Fin d)]
    (L : Matrix (Fin d) (Fin d) ℝ)
    (h : ∀ u : Fin d → ℝ, (∑ i, (L *ᵥ u) i ^ 2) ≤ ∑ i, u i ^ 2)
    (j : Fin d) :
    0 ≤ sval L j ∧ sval L j ≤ 1 := by
  have hge : 0 ≤ gramEig L j := by
    have hstar : (L : Matrix (Fin d) (Fin d) ℝ)ᴴ = L.transpose := by
      ext i j; simp [Matrix.conjTranspose]
    have hpsd' : Matrix.PosSemidef (L.transpose * L) := by
      rw [← hstar]
      exact posSemidef_conjTranspose_mul_self L
    have := hpsd'.eigenvalues_nonneg j
    simpa [gramEig, gram] using this
  have hle := gramEig_le_one L h j
  have hmax : max 0 (gramEig L j) ≤ 1 := max_le (by norm_num) hle
  refine ⟨Real.sqrt_nonneg _, ?_⟩
  unfold sval
  rw [← Real.sqrt_one]
  exact Real.sqrt_le_sqrt hmax

/-- Sorted Gram eigenvalue at `j` coincides with `gramEig` at the corresponding index. -/
lemma gramEig₀_eq_gramEig {d : ℕ} [DecidableEq (Fin d)]
    (L : Matrix (Fin d) (Fin d) ℝ) (j : Fin (Fintype.card (Fin d))) :
    gramEig₀ L j
      = gramEig L (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin d))) j) := by
  have hdef : ∀ i : Fin d,
      (gram_isHermitian L).eigenvalues i
        = (gram_isHermitian L).eigenvalues₀
            ((Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin d)))).symm i) :=
    fun i => rfl
  show (gram_isHermitian L).eigenvalues₀ j
    = (gram_isHermitian L).eigenvalues (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin d))) j)
  rw [hdef]
  congr 1
  exact (Equiv.symm_apply_apply
    (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin d)))) j).symm

/-- Sorted Gram eigenvalue is at most `1` under contraction. -/
lemma gramEig₀_le_one {d : ℕ} [DecidableEq (Fin d)]
    (L : Matrix (Fin d) (Fin d) ℝ)
    (h : ∀ u : Fin d → ℝ, (∑ i, (L *ᵥ u) i ^ 2) ≤ ∑ i, u i ^ 2)
    (j : Fin (Fintype.card (Fin d))) :
    gramEig₀ L j ≤ 1 := by
  rw [gramEig₀_eq_gramEig L j]
  exact gramEig_le_one L h (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin d))) j)

/-- Sorted Gram eigenvalue is nonnegative (PSD Gram). -/
lemma gramEig₀_nonneg {d : ℕ} [DecidableEq (Fin d)]
    (L : Matrix (Fin d) (Fin d) ℝ) (j : Fin (Fintype.card (Fin d))) :
    0 ≤ gramEig₀ L j := by
  rw [gramEig₀_eq_gramEig L j]
  have hstar : (L : Matrix (Fin d) (Fin d) ℝ)ᴴ = L.transpose := by
    ext i j; simp [Matrix.conjTranspose]
  have hpsd' : Matrix.PosSemidef (L.transpose * L) := by
    rw [← hstar]
    exact posSemidef_conjTranspose_mul_self L
  have := hpsd'.eigenvalues_nonneg
    (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin d))) j)
  simpa [gramEig, gram] using this

/-- `σ_2` lies in `[0, 1]` under contraction. -/
theorem sigma2_mem_of_contraction {d : ℕ} [DecidableEq (Fin d)]
    (L : Matrix (Fin d) (Fin d) ℝ)
    (h : ∀ u : Fin d → ℝ, (∑ i, (L *ᵥ u) i ^ 2) ≤ ∑ i, u i ^ 2) :
    0 ≤ sigma2 L ∧ sigma2 L ≤ 1 := by
  unfold sigma2
  by_cases hd : 1 < d
  · rw [dif_pos hd]
    have hle := gramEig₀_le_one L h ⟨1, by rw [Fintype.card_fin]; exact hd⟩
    have hge := gramEig₀_nonneg L ⟨1, by rw [Fintype.card_fin]; exact hd⟩
    have hmax : max 0 (gramEig₀ L ⟨1, by rw [Fintype.card_fin]; exact hd⟩) ≤ 1 :=
      max_le (by norm_num) hle
    exact ⟨Real.sqrt_nonneg _, by
      rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hmax⟩
  · rw [dif_neg hd]; norm_num

/-- Deterministic range: `0 ≤ â ≤ 1` for every data set. -/
theorem aHat_mem {m : ℕ} (Y : Fin (m + 1) → Fin d) : 0 ≤ aHat Y ∧ aHat Y ≤ 1 := by
  classical
  by_cases h : degPos Y
  · rw [aHat_eq_of_degPos Y h]
    have hσ : 0 ≤ sigma2 (lHat Y) ∧ sigma2 (lHat Y) ≤ 1 :=
      sigma2_mem_of_contraction (lHat Y) (lhat_contraction Y h)
    have hsq : 0 ≤ (sigma2 (lHat Y)) ^ 2 ∧ (sigma2 (lHat Y)) ^ 2 ≤ 1 := by
      constructor
      · exact sq_nonneg _
      · nlinarith [hσ.1, hσ.2]
    unfold aOf
    constructor <;> linarith
  · rw [aHat_eq_zero_of_not_degPos Y h]
    norm_num

/-- Lag contribution bound: candidate at lag `k` is at most `1/k`. -/
theorem lag_bound {n : ℕ} (X : Fin (n + 1) → Fin d) (k : ℕ) (hk : 0 < k) :
    aHat (skipPath X k) / k ≤ 1 / k := by
  have hmem := aHat_mem (skipPath X k)
  have hk0 : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  exact div_le_div_of_nonneg_right hmem.2 (le_of_lt hk0)

/-! ## Finite maximum over all observed lags -/

/-- Uniform expression for the finite lag maximum, including the empty path.
The range includes lag `n`; the lag-zero entry is the harmless value zero. -/
theorem gammaHat_eq_fold {n : ℕ} (X : Fin (n + 1) → Fin d) :
    gammaHat X = ((List.range (n + 1)).map (fun k =>
      if 0 < k then aHat (skipPath X k) / k else 0)).foldl max 0 := by
  cases n with
  | zero => simp [gammaHat]
  | succ n => rfl

private theorem foldMax_le (L : List ℝ) (a b : ℝ)
    (ha : a ≤ b) (hL : ∀ x ∈ L, x ≤ b) : L.foldl max a ≤ b := by
  induction L generalizing a with
  | nil => exact ha
  | cons x xs ih =>
    apply ih (max a x) (max_le ha (hL x (by simp)))
    intro y hy
    exact hL y (by simp [hy])

private theorem le_foldMax (L : List ℝ) (a : ℝ) : a ≤ L.foldl max a := by
  induction L generalizing a with
  | nil => exact le_rfl
  | cons x xs ih => exact (le_max_left a x).trans (ih (max a x))

private theorem member_le_foldMax (L : List ℝ) (a : ℝ) {x : ℝ}
    (hx : x ∈ L) : x ≤ L.foldl max a := by
  induction L generalizing a with
  | nil => simp at hx
  | cons y ys ih =>
    rcases List.mem_cons.mp hx with rfl | hx
    · exact (le_max_right a x).trans (le_foldMax ys (max a x))
    · exact ih (max a y) hx

/-- Every admissible lag is included in the empirical maximum. -/
theorem gammaHat_candidate_le {n : ℕ} (X : Fin (n + 1) → Fin d)
    (k : ℕ) (hk : 0 < k) (hkn : k ≤ n) :
    aHat (skipPath X k) / k ≤ gammaHat X := by
  rw [gammaHat_eq_fold]
  apply member_le_foldMax
  apply List.mem_map.mpr
  refine ⟨k, List.mem_range.mpr (by omega), ?_⟩
  simp [hk]

/-- An upper bound on every positive-lag candidate bounds the estimator. -/
theorem gammaHat_le {n : ℕ} (X : Fin (n + 1) → Fin d) (b : ℝ)
    (hb : 0 ≤ b)
    (h : ∀ k : ℕ, 0 < k → k ≤ n → aHat (skipPath X k) / k ≤ b) :
    gammaHat X ≤ b := by
  rw [gammaHat_eq_fold]
  apply foldMax_le _ _ _ hb
  intro x hx
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hx
  by_cases hkpos : 0 < k
  · simp only [hkpos, if_true]
    exact h k hkpos (by have := List.mem_range.mp hk; omega)
  · simpa [hkpos] using hb

/-- The finite maximum is nonnegative, also for zero transitions. -/
theorem gammaHat_nonneg {n : ℕ} (X : Fin (n + 1) → Fin d) : 0 ≤ gammaHat X := by
  rw [gammaHat_eq_fold]
  exact le_foldMax _ _

/-- Deterministic range of the empirical pseudo-spectral-gap estimator. -/
theorem gammaHat_mem {n : ℕ} (X : Fin (n + 1) → Fin d) :
    0 ≤ gammaHat X ∧ gammaHat X ≤ 1 := by
  refine ⟨gammaHat_nonneg X, gammaHat_le X 1 (by norm_num) ?_⟩
  intro k hk _
  apply (lag_bound X k hk).trans
  have hk0 : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  apply (div_le_iff₀ hk0).mpr
  have hk1 : (1 : ℝ) ≤ k := Nat.one_le_cast.mpr hk
  simpa using hk1

end PsgEst
