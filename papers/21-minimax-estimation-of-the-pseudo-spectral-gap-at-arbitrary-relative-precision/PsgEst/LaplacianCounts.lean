import PsgEst.Laplacian
import PsgEst.Estimator

open Matrix BigOperators Real

namespace PsgEst

variable {d m : ℕ}

/-- The stationary normalized edge vector in (16). -/
noncomputable def edgeVector (μ : Fin d → ℝ) (i j : Fin d) : Fin d ⊕ Fin d → ℝ :=
  Sum.elim (Pi.single i (Real.sqrt (μ i))⁻¹) (Pi.single j (-(Real.sqrt (μ j))⁻¹))

/-- The positive semidefinite rank-one matrix of an edge. -/
noncomputable def edgeOuter (μ : Fin d → ℝ) (i j : Fin d) :
    Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) ℝ :=
  Matrix.vecMulVec (edgeVector μ i j) (edgeVector μ i j)

/-- Outgoing and incoming degree ratios used in the actual normalization. -/
noncomputable def empiricalScale (μ : Fin d → ℝ) (Y : Fin (m+1) → Fin d) :
    Fin d ⊕ Fin d → ℝ :=
  Sum.elim (fun i => (outDeg Y i : ℝ) / ((m : ℝ) * μ i))
    (fun j => (inDeg Y j : ℝ) / ((m : ℝ) * μ j))

/-- Empirical mean of the normalized edge outer products, grouped by transition
counts. Grouping preserves every observed transition and its multiplicity. -/
noncomputable def empiricalHbar (μ : Fin d → ℝ) (Y : Fin (m+1) → Fin d) :
    Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) ℝ :=
  (m : ℝ)⁻¹ • ∑ i, ∑ j, (countMatR Y i j) • edgeOuter μ i j

theorem edgeOuter_isHermitian (μ : Fin d → ℝ) (i j : Fin d) :
    (edgeOuter μ i j).IsHermitian := by
  ext a b
  simp [edgeOuter, Matrix.conjTranspose]

theorem empiricalHbar_isHermitian (μ : Fin d → ℝ) (Y : Fin (m+1) → Fin d) :
    (empiricalHbar μ Y).IsHermitian := by
  ext a b
  simp [empiricalHbar, Matrix.conjTranspose, Matrix.sum_apply, Matrix.smul_apply,
    edgeOuter, Matrix.vecMulVec_apply, mul_comm]

theorem edgeOuter_quadratic (μ : Fin d → ℝ) (i j : Fin d)
    (x : Fin d ⊕ Fin d → ℝ) :
    x ⬝ᵥ (edgeOuter μ i j *ᵥ x) = ((edgeVector μ i j) ⬝ᵥ x) ^ 2 := by
  rw [edgeOuter, Matrix.vecMulVec_mulVec, dotProduct_smul]
  simp only [op_smul_eq_mul, dotProduct_comm x (edgeVector μ i j), pow_two]

theorem empiricalHbar_nonneg (μ : Fin d → ℝ) (Y : Fin (m+1) → Fin d)
    (x : Fin d ⊕ Fin d → ℝ) : 0 ≤ x ⬝ᵥ (empiricalHbar μ Y *ᵥ x) := by
  simp only [empiricalHbar, Matrix.smul_mulVec, Matrix.sum_mulVec,
    dotProduct_smul, dotProduct_sum, smul_eq_mul, edgeOuter_quadratic]
  apply mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
    mul_nonneg (countMatR_nonneg Y i j) (sq_nonneg _)

theorem edgeOuter_posSemidef (μ : Fin d → ℝ) (i j : Fin d) :
    (edgeOuter μ i j).PosSemidef := by
  refine ⟨edgeOuter_isHermitian μ i j, ?_⟩
  intro x
  simpa only [star_trivial, edgeOuter_quadratic] using
    sq_nonneg ((edgeVector μ i j) ⬝ᵥ x)

theorem empiricalHbar_posSemidef (μ : Fin d → ℝ) (Y : Fin (m+1) → Fin d) :
    (empiricalHbar μ Y).PosSemidef := by
  refine ⟨empiricalHbar_isHermitian μ Y, ?_⟩
  intro x
  simpa only [star_trivial] using empiricalHbar_nonneg μ Y x

/-- Grouping the actual observed edges by their transition counts gives exactly
the path average in the proof of Proposition 1. -/
theorem empiricalHbar_eq_path_average (μ : Fin d → ℝ) (Y : Fin (m+1) → Fin d) :
    empiricalHbar μ Y = (m : ℝ)⁻¹ •
      ∑ t : Fin m, edgeOuter μ (Y t.castSucc) (Y t.succ) := by
  have hc (i j : Fin d) : (countMatR Y i j) • edgeOuter μ i j =
      ∑ t : Fin m, if Y t.castSucc = i ∧ Y t.succ = j then edgeOuter μ i j else 0 := by
    have hcount : countMatR Y i j = ∑ t : Fin m,
        if Y t.castSucc = i ∧ Y t.succ = j then (1 : ℝ) else 0 := by
      simp [countMatR, countMat]
    rw [hcount, Finset.sum_smul]
    apply Finset.sum_congr rfl
    intro t _
    split_ifs <;> simp
  unfold empiricalHbar
  congr 1
  simp_rw [hc]
  calc (∑ i, ∑ j, ∑ t : Fin m,
        if Y t.castSucc = i ∧ Y t.succ = j then edgeOuter μ i j else 0)
      = ∑ i, ∑ t : Fin m, ∑ j,
        if Y t.castSucc = i ∧ Y t.succ = j then edgeOuter μ i j else 0 := by
          apply Finset.sum_congr rfl
          intro i _
          exact Finset.sum_comm
    _ = ∑ t : Fin m, ∑ i, ∑ j,
        if Y t.castSucc = i ∧ Y t.succ = j then edgeOuter μ i j else 0 :=
          Finset.sum_comm
    _ = ∑ t : Fin m, edgeOuter μ (Y t.castSucc) (Y t.succ) := by
      apply Finset.sum_congr rfl
      intro t _
      simp [ite_and]

private theorem inverse_sqrt_sq (x : ℝ) (hx : 0 < x) :
    (Real.sqrt x)⁻¹ * (Real.sqrt x)⁻¹ = x⁻¹ := by
  rw [← mul_inv, Real.mul_self_sqrt hx.le]

/-- Explicit count-block representation of the empirical edge average. -/
theorem empiricalHbar_blocks (μ : Fin d → ℝ) (hμ : ∀ i, 0 < μ i)
    (Y : Fin (m+1) → Fin d) :
    empiricalHbar μ Y = Matrix.fromBlocks
      (Matrix.diagonal fun i => (outDeg Y i : ℝ) / ((m : ℝ) * μ i))
      (fun i j => -(countMatR Y i j / ((m : ℝ) * Real.sqrt (μ i) * Real.sqrt (μ j))))
      (fun j i => -(countMatR Y i j / ((m : ℝ) * Real.sqrt (μ i) * Real.sqrt (μ j))))
      (Matrix.diagonal fun j => (inDeg Y j : ℝ) / ((m : ℝ) * μ j)) := by
  ext a b
  rcases a with a | a <;> rcases b with b | b
  · by_cases hab : a = b
    · subst b
      simp [empiricalHbar, edgeOuter, edgeVector, Matrix.vecMulVec_apply, Pi.single_apply,
        Matrix.smul_apply, Matrix.sum_apply, mul_ite, ite_mul, ← Finset.sum_mul,
        ← outDeg_cast, inverse_sqrt_sq _ (hμ a), div_eq_mul_inv, mul_assoc]
      ring
    · simp [empiricalHbar, edgeOuter, edgeVector, Matrix.vecMulVec_apply, Pi.single_apply,
        Matrix.smul_apply, Matrix.sum_apply, mul_ite, ite_mul, hab]
  · simp [empiricalHbar, edgeOuter, edgeVector, Matrix.vecMulVec_apply, Pi.single_apply,
      Matrix.smul_apply, Matrix.sum_apply, mul_ite, ite_mul, div_eq_mul_inv,
      mul_comm, mul_left_comm]
    ring
  · simp [empiricalHbar, edgeOuter, edgeVector, Matrix.vecMulVec_apply, Pi.single_apply,
      Matrix.smul_apply, Matrix.sum_apply, mul_ite, ite_mul, div_eq_mul_inv,
      mul_comm, mul_left_comm]
  · by_cases hab : a = b
    · subst b
      simp [empiricalHbar, edgeOuter, edgeVector, Matrix.vecMulVec_apply, Pi.single_apply,
        Matrix.smul_apply, Matrix.sum_apply, mul_ite, ite_mul, ← Finset.sum_mul,
        ← inDeg_cast, inverse_sqrt_sq _ (hμ a), div_eq_mul_inv, mul_assoc]
      ring
    · simp [empiricalHbar, edgeOuter, edgeVector, Matrix.vecMulVec_apply, Pi.single_apply,
        Matrix.smul_apply, Matrix.sum_apply, mul_ite, ite_mul, hab]

/-- Entry formula for a concrete diagonal congruence. -/
theorem diagonalNormalize_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (t : ι → ℝ) (i j : ι) :
    diagonalNormalize A t i j = (Real.sqrt (t i))⁻¹ * A i j * (Real.sqrt (t j))⁻¹ := by
  simp [diagonalNormalize, inverseSqrtDiagonal, Matrix.diagonal_mul, Matrix.mul_diagonal]

/-- Positive degrees make the empirical substitution genuinely invertible. -/
theorem empiricalScale_pos (μ : Fin d → ℝ) (hμ : ∀ i, 0 < μ i)
    (Y : Fin (m+1) → Fin d) (hm : 0 < m) (hpos : degPos Y)
    (a : Fin d ⊕ Fin d) : 0 < empiricalScale μ Y a := by
  rcases a with i | i
  · exact div_pos (Nat.cast_pos.mpr (hpos i).1) (mul_pos (Nat.cast_pos.mpr hm) (hμ i))
  · exact div_pos (Nat.cast_pos.mpr (hpos i).2) (mul_pos (Nat.cast_pos.mpr hm) (hμ i))

private theorem normalize_count_scalar (M r c u v z : ℝ)
    (hM : 0 < M) (hr : 0 < r) (hc : 0 < c) (hu : 0 < u) (hv : 0 < v) :
    (Real.sqrt (r / (M * u)))⁻¹ * (z / (M * Real.sqrt u * Real.sqrt v)) *
        (Real.sqrt (c / (M * v)))⁻¹ =
      r ^ (-(1/2 : ℝ)) * z * c ^ (-(1/2 : ℝ)) := by
  rw [Real.sqrt_div hr.le, Real.sqrt_div hc.le, Real.sqrt_mul hM.le,
    Real.sqrt_mul hM.le, Real.rpow_neg hr.le, Real.rpow_neg hc.le,
    ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
  simp only [inv_div]
  field_simp [ne_of_gt hM, ne_of_gt (Real.sqrt_pos.mpr hr),
    ne_of_gt (Real.sqrt_pos.mpr hc), ne_of_gt (Real.sqrt_pos.mpr hu),
    ne_of_gt (Real.sqrt_pos.mpr hv)]
  nlinarith only [congrArg (fun q : ℝ => q * z) (Real.sq_sqrt hM.le)]

private theorem normalize_diagonal_scalar (t : ℝ) (ht : 0 < t) :
    (Real.sqrt t)⁻¹ * t * (Real.sqrt t)⁻¹ = 1 := by
  calc (Real.sqrt t)⁻¹ * t * (Real.sqrt t)⁻¹
      = t * ((Real.sqrt t)⁻¹ * (Real.sqrt t)⁻¹) := by ring
    _ = 1 := by rw [inverse_sqrt_sq t ht, mul_inv_cancel₀ ht.ne']

/-- The empirical edge average normalizes to the exact bipartite Laplacian of
the separately incoming/outgoing normalized count matrix in (6). -/
theorem empiricalHbar_normalize (μ : Fin d → ℝ) (hμ : ∀ i, 0 < μ i)
    (Y : Fin (m+1) → Fin d) (hm : 0 < m) (hpos : degPos Y) :
    diagonalNormalize (empiricalHbar μ Y) (empiricalScale μ Y) = bipH (lHat Y) := by
  ext a b
  rcases a with a | a <;> rcases b with b | b
  · rw [diagonalNormalize_apply, empiricalHbar_blocks μ hμ]
    by_cases hab : a = b
    · subst b
      simpa only [Matrix.fromBlocks_apply₁₁, Matrix.diagonal_apply_eq,
        bipH_apply_inl_inl, if_pos rfl] using
        normalize_diagonal_scalar (empiricalScale μ Y (Sum.inl a))
          (empiricalScale_pos μ hμ Y hm hpos _)
    · simp [hab, empiricalScale]
  · rw [diagonalNormalize_apply, empiricalHbar_blocks μ hμ]
    simp only [Matrix.fromBlocks_apply₁₂, bipH_apply_inl_inr, lHat_eq_of_degPos Y hpos,
      Matrix.diagonal_mul, Matrix.mul_diagonal, mul_neg, neg_mul]
    congr 1
    exact normalize_count_scalar (m : ℝ) (outDeg Y a : ℝ) (inDeg Y b : ℝ)
      (μ a) (μ b) (countMatR Y a b) (Nat.cast_pos.mpr hm)
      (Nat.cast_pos.mpr (hpos a).1) (Nat.cast_pos.mpr (hpos b).2) (hμ a) (hμ b)
  · rw [diagonalNormalize_apply, empiricalHbar_blocks μ hμ]
    simp only [Matrix.fromBlocks_apply₂₁, bipH_apply_inr_inl, lHat_eq_of_degPos Y hpos,
      Matrix.diagonal_mul, Matrix.mul_diagonal, mul_neg, neg_mul]
    have h := normalize_count_scalar (m : ℝ) (outDeg Y b : ℝ) (inDeg Y a : ℝ)
      (μ b) (μ a) (countMatR Y b a) (Nat.cast_pos.mpr hm)
      (Nat.cast_pos.mpr (hpos b).1) (Nat.cast_pos.mpr (hpos a).2) (hμ b) (hμ a)
    dsimp [empiricalScale]
    simp only [countMatR_apply] at h
    convert congrArg (fun z : ℝ => -z) h using 1
    all_goals ring
  · rw [diagonalNormalize_apply, empiricalHbar_blocks μ hμ]
    by_cases hab : a = b
    · subst b
      simpa only [Matrix.fromBlocks_apply₂₂, Matrix.diagonal_apply_eq,
        bipH_apply_inr_inr, if_pos rfl] using
        normalize_diagonal_scalar (empiricalScale μ Y (Sum.inr a))
          (empiricalScale_pos μ hμ Y hm hpos _)
    · simp [hab, empiricalScale]

/-- The stationary average of the actual positive edge matrices is precisely
the population bipartite Laplacian (16). -/
theorem stationary_edge_sum_eq_bipH (Q : Stoch d) (st : Stationary Q) :
    (∑ i, st.mu i • (∑ j, Q.P i j • edgeOuter st.mu i j)) =
      bipH (simil st.mu Q.P) := by
  have hpow (i : Fin d) : (st.mu i) ^ (-(1/2 : ℝ)) = (Real.sqrt (st.mu i))⁻¹ := by
    rw [Real.rpow_neg (st.pos i).le, ← Real.sqrt_eq_rpow]
  simp only [one_div] at hpow
  have hsqrt (i : Fin d) : (st.mu i) ^ ((2 : ℝ)⁻¹) = Real.sqrt (st.mu i) := by
    rw [← one_div, ← Real.sqrt_eq_rpow]
  have hcancel (i : Fin d) : st.mu i * (Real.sqrt (st.mu i))⁻¹ = Real.sqrt (st.mu i) := by
    have hs := Real.mul_self_sqrt (st.pos i).le
    calc st.mu i * (Real.sqrt (st.mu i))⁻¹
        = (Real.sqrt (st.mu i) * Real.sqrt (st.mu i)) * (Real.sqrt (st.mu i))⁻¹ := by rw [hs]
      _ = Real.sqrt (st.mu i) := by simp [ne_of_gt (Real.sqrt_pos.mpr (st.pos i))]
  ext a b
  rcases a with a | a <;> rcases b with b | b
  · by_cases hab : a = b
    · subst b
      simp [edgeOuter, edgeVector, Matrix.vecMulVec_apply, Pi.single_apply,
        Matrix.smul_apply, Matrix.sum_apply, mul_ite, ite_mul, ← Finset.sum_mul,
        inverse_sqrt_sq _ (st.pos a), Q.row_stoch, (st.pos a).ne']
    · simp [edgeOuter, edgeVector, Matrix.vecMulVec_apply, Pi.single_apply,
        Matrix.smul_apply, Matrix.sum_apply, mul_ite, ite_mul, hab]
  · simp [edgeOuter, edgeVector, Matrix.vecMulVec_apply, Pi.single_apply,
      Matrix.smul_apply, Matrix.sum_apply, mul_ite, ite_mul, simil,
      Matrix.diagonal_mul, Matrix.mul_diagonal, hpow, hsqrt]
    nlinarith only [congrArg (fun z : ℝ => z * Q.P a b * (Real.sqrt (st.mu b))⁻¹) (hcancel a)]
  · simp [edgeOuter, edgeVector, Matrix.vecMulVec_apply, Pi.single_apply,
      Matrix.smul_apply, Matrix.sum_apply, mul_ite, ite_mul, simil,
      Matrix.diagonal_mul, Matrix.mul_diagonal, hpow, hsqrt]
    nlinarith only [congrArg (fun z : ℝ => z * Q.P b a * (Real.sqrt (st.mu a))⁻¹) (hcancel b)]
  · by_cases hab : a = b
    · subst b
      simp [edgeOuter, edgeVector, Matrix.vecMulVec_apply, Pi.single_apply,
        Matrix.smul_apply, Matrix.sum_apply, mul_ite, ite_mul,
        inverse_sqrt_sq _ (st.pos a)]
      simp_rw [← mul_assoc]
      rw [← Finset.sum_mul, st.station, mul_inv_cancel₀ (st.pos a).ne']
    · simp [edgeOuter, edgeVector, Matrix.vecMulVec_apply, Pi.single_apply,
        Matrix.smul_apply, Matrix.sum_apply, mul_ite, ite_mul, hab]

end PsgEst
