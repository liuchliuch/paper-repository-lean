import P31.QuadraticMetric

/-! The substantive unnumbered quadratic-norm identity in Section 7.3.
Only standard operator-norm facts and finite ℓₚ norm duality are external inputs;
the PSD seminorm argument and supremum comparison are proved here. -/

noncomputable section
open scoped Matrix
namespace P31.QuadraticMetric

/-- The exact supremum of the quadratic form over the actual ℓₚ unit ball. -/
def quadraticSup {d : ℕ} (p : ℝ) (A : Mat d) : ℝ :=
  sSup {t : ℝ | ∃u : Vec d, lpNorm p u ≤ 1 ∧ t=quad A u}

lemma quad_smul {d : ℕ} (A : Mat d) (a : ℝ) (u : Vec d) :
    quad A (a • u)=a^2*quad A u := by
  simp only [quad, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  ring

lemma lpNorm_eq_zero_implies_vector_eq_zero {d : ℕ} {p : ℝ} (hp : 0 < p)
    (u : Vec d) (hu : lpNorm p u=0) : u=0 := by
  ext i
  apply abs_nonpos_iff.mp
  simpa only [hu] using abs_coordinate_le_lpNorm hp u i

lemma quadratic_unit_le_operatorNorm {d : ℕ} {p : ℝ} (hp : 2 ≤ p)
    (A : Mat d) (O : OperatorNormInput d p A) (u : Vec d) (hu : lpNorm p u ≤ 1) :
    quad A u ≤ operatorNorm p A := by
  have hL := operatorNorm_nonneg hp A O
  have hn := lpNorm_nonneg p u
  have hsq : (lpNorm p u)^2 ≤ 1 := by nlinarith
  exact (quad_le_operatorNorm hp A O.bound u).trans
    (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hsq hL)

lemma quadraticSet_bddAbove {d : ℕ} {p : ℝ} (hp : 2 ≤ p)
    (A : Mat d) (O : OperatorNormInput d p A) :
    BddAbove {t : ℝ | ∃u : Vec d, lpNorm p u ≤ 1 ∧ t=quad A u} := by
  refine ⟨operatorNorm p A, ?_⟩
  rintro t ⟨u, hu, rfl⟩
  exact quadratic_unit_le_operatorNorm hp A O u hu

lemma quadraticSet_nonempty {d : ℕ} {p : ℝ} (hp : 2 ≤ p) (A : Mat d) :
    Set.Nonempty {t : ℝ | ∃u : Vec d, lpNorm p u ≤ 1 ∧ t=quad A u} := by
  refine ⟨0, 0, ?_, ?_⟩
  · simp only [lpNorm_zero (by linarith : 0 < p)]
    norm_num
  · simp [quad]

lemma quadraticSup_nonneg {d : ℕ} {p : ℝ} (hp : 2 ≤ p)
    (A : Mat d) (O : OperatorNormInput d p A) : 0 ≤ quadraticSup p A := by
  apply le_csSup (quadraticSet_bddAbove hp A O)
  refine ⟨0, ?_, ?_⟩
  · simp only [lpNorm_zero (by linarith : 0 < p)]
    norm_num
  · simp [quad]

lemma quadraticSup_le_operatorNorm {d : ℕ} {p : ℝ} (hp : 2 ≤ p)
    (A : Mat d) (O : OperatorNormInput d p A) : quadraticSup p A ≤ operatorNorm p A := by
  apply csSup_le (quadraticSet_nonempty hp A)
  rintro t ⟨u, hu, rfl⟩
  exact quadratic_unit_le_operatorNorm hp A O u hu

/-- The unit-ball supremum controls the quadratic form on every vector.
The zero vector is handled before normalizing by the ℓₚ norm. -/
theorem quad_le_quadraticSup {d : ℕ} {p : ℝ} (hp : 2 ≤ p)
    (A : Mat d) (O : OperatorNormInput d p A) (u : Vec d) :
    quad A u ≤ quadraticSup p A*(lpNorm p u)^2 := by
  have hp0 : 0 < p := by linarith
  by_cases hn : lpNorm p u=0
  · have hu := lpNorm_eq_zero_implies_vector_eq_zero hp0 u hn
    simp [hu, quad, lpNorm_zero hp0]
  · have hnpos : 0 < lpNorm p u := lt_of_le_of_ne (lpNorm_nonneg p u) (Ne.symm hn)
    have hnorm : lpNorm p ((lpNorm p u)⁻¹ • u)=1 := by
      rw [lpNorm_smul hp0, abs_of_pos (inv_pos.mpr hnpos), inv_mul_cancel₀ hn]
    have hunit : quad A ((lpNorm p u)⁻¹ • u) ≤ quadraticSup p A := by
      apply le_csSup (quadraticSet_bddAbove hp A O)
      exact ⟨_, hnorm.le, rfl⟩
    rw [quad_smul] at hunit
    have heq : (lpNorm p u)⁻¹^2*quad A u=quad A u/(lpNorm p u)^2 := by ring
    rw [heq] at hunit
    exact (div_le_iff₀ (pow_pos hnpos 2)).mp hunit

/-- PSD Cauchy--Schwarz promotes the quadratic supremum to a uniform pairing
bound; this is the reverse direction of the norm identity. -/
theorem pairing_le_quadraticSup {d : ℕ} {p : ℝ} (hp : 2 ≤ p)
    (A : Mat d) (hA : A.PosSemidef) (O : OperatorNormInput d p A) (u v : Vec d) :
    |u ⬝ᵥ (A *ᵥ v)| ≤ quadraticSup p A*lpNorm p u*lpNorm p v := by
  have hQ := quadraticSup_nonneg hp A O
  have hu0 := lpNorm_nonneg p u
  have hv0 := lpNorm_nonneg p v
  have hqu : 0 ≤ quad A u := by simpa only [quad, star_trivial] using hA.2 u
  have hqv : 0 ≤ quad A v := by simpa only [quad, star_trivial] using hA.2 v
  have hu := quad_le_quadraticSup hp A O u
  have hv := quad_le_quadraticSup hp A O v
  have hmul : quad A u*quad A v ≤
      (quadraticSup p A*(lpNorm p u)^2)*(quadraticSup p A*(lpNorm p v)^2) :=
    mul_le_mul hu hv hqv (mul_nonneg hQ (sq_nonneg _))
  have hcs := (psd_cauchy_sq hA u v).trans hmul
  have htarget : 0 ≤ quadraticSup p A*lpNorm p u*lpNorm p v :=
    mul_nonneg (mul_nonneg hQ hu0) hv0
  nlinarith [sq_abs (u ⬝ᵥ (A *ᵥ v)), abs_nonneg (u ⬝ᵥ (A *ᵥ v))]

/-- Standard finite norm duality converts the internally proved pairing bound
into the actual ℓₚ→ℓ_q operator bound with the quadratic supremum constant. -/
theorem operatorNorm_le_quadraticSup {d : ℕ} {p : ℝ} (hp : 2 ≤ p)
    (A : Mat d) (hA : A.PosSemidef) (O : OperatorNormInput d p A)
    (dual : LpDualityInput d p) : operatorNorm p A ≤ quadraticSup p A := by
  have hQ := quadraticSup_nonneg hp A O
  have hop (v : Vec d) : lpNorm (dualExponent p) (A *ᵥ v) ≤ quadraticSup p A*lpNorm p v := by
    apply dual _ _ (mul_nonneg hQ (lpNorm_nonneg _ _))
    intro u
    simpa only [dotProduct_comm, mul_assoc, mul_comm, mul_left_comm] using pairing_le_quadraticSup hp A hA O u v
  unfold operatorNorm
  have hnonempty : Set.Nonempty {t : ℝ | ∃v : Vec d, lpNorm p v ≤ 1 ∧
      t=lpNorm (dualExponent p) (A *ᵥ v)} := by
    refine ⟨0, 0, ?_, ?_⟩
    · simp only [lpNorm_zero (by linarith : 0 < p)]; norm_num
    · simp only [Matrix.mulVec_zero, lpNorm_zero (dualExponent_pos (by linarith : 1 < p))]
  apply csSup_le hnonempty
  rintro t ⟨v, hv, rfl⟩
  exact (hop v).trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hv hQ)

/-- The exact source Section 7.3 Ex6 equality, for actual finite real PSD matrices. -/
theorem operatorNorm_eq_quadraticSup {d : ℕ} {p : ℝ} (hp : 2 ≤ p)
    (A : Mat d) (hA : A.PosSemidef) (O : OperatorNormInput d p A)
    (dual : LpDualityInput d p) :
    operatorNorm p A = sSup {t : ℝ | ∃u : Vec d, lpNorm p u ≤ 1 ∧ t=quad A u} := by
  apply le_antisymm (operatorNorm_le_quadraticSup hp A hA O dual)
  exact quadraticSup_le_operatorNorm hp A O

end P31.QuadraticMetric
