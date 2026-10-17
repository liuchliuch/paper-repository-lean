import Paper38.HilbertCoordinates
import Paper38.AffineLifting
import Paper38.Sampling
import Paper38.ModelBridges
import Paper38.GaussianDifferentiation
import Mathlib.Tactic

/-! Deterministic good-event localization and the square-root perturbation estimate (7.4).
Frobenius norms are the norms of flattened Euclidean matrices, independently
of every scoped operator norm instance. -/
noncomputable section
open MeasureTheory
open scoped BigOperators Matrix MatrixOrder InnerProductSpace Matrix.Norms.Frobenius

namespace Paper38.GaussianLocalization
open Paper38.Model Paper38.HilbertCoordinates

variable {d : ℕ}

def frobNorm (A : Mat d) : ℝ := ‖flattenEquiv d A‖

@[simp] lemma frobNorm_sq (A : Mat d) : frobNorm A ^ 2 = frobSq A := norm_flatten_sq A

lemma inner_flatten (A B : Mat d) : ⟪flattenEquiv d A, flattenEquiv d B⟫_ℝ = matrixInner A B := by
  simp [EuclideanSpace.inner_eq_star_dotProduct, matrixInner, dotProduct,
    Fintype.sum_prod_type, mul_comm]

lemma matrixInner_add_right (X A B : Mat d) :
    matrixInner X (A + B) = matrixInner X A + matrixInner X B := by
  simp [matrixInner, mul_add, Finset.sum_add_distrib]

lemma left_rayleigh (A X : Mat d) (a : ℝ)
    (ha : ∀ v : Fin d → ℝ, a * (v ⬝ᵥ v) ≤ v ⬝ᵥ (A *ᵥ v)) :
    a * frobSq X ≤ matrixInner X (A * X) := by
  calc
    a * frobSq X = ∑ j, a * ((fun i => X i j) ⬝ᵥ (fun i => X i j)) := by
      simp only [frobSq, dotProduct, pow_two, Finset.mul_sum]
      exact Finset.sum_comm
    _ ≤ ∑ j, (fun i => X i j) ⬝ᵥ (A *ᵥ (fun i => X i j)) :=
      Finset.sum_le_sum (fun j _ => ha _)
    _ = matrixInner X (A * X) := by
      unfold matrixInner
      rw [Finset.sum_comm]
      rfl

lemma right_rayleigh (A X : Mat d) (a : ℝ) (hA : Aᵀ = A)
    (ha : ∀ v : Fin d → ℝ, a * (v ⬝ᵥ v) ≤ v ⬝ᵥ (A *ᵥ v)) :
    a * frobSq X ≤ matrixInner X (X * A) := by
  have he (i : Fin d) : (X * A) i = A *ᵥ X i := by
    ext j
    simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct]
    apply Finset.sum_congr rfl
    intro k _
    have hs : A k j = A j k := congrFun (congrFun hA j) k
    rw [hs, mul_comm]
  calc
    a * frobSq X = ∑ i, a * (X i ⬝ᵥ X i) := by
      simp only [frobSq, dotProduct, pow_two, Finset.mul_sum]
    _ ≤ ∑ i, X i ⬝ᵥ (A *ᵥ X i) := Finset.sum_le_sum (fun i _ => ha _)
    _ = matrixInner X (X * A) := by simp only [matrixInner, he, dotProduct]

lemma sqrt_scalar_identity (m : ℝ) (hm : 0 ≤ m) :
    CFC.sqrt (m • (1 : Mat d)) = Real.sqrt m • (1 : Mat d) := by
  have hp : (m • (1 : Mat d)).PosSemidef := Matrix.PosSemidef.one.smul hm
  have hs : (Real.sqrt m • (1 : Mat d)).PosSemidef :=
    Matrix.PosSemidef.one.smul (Real.sqrt_nonneg m)
  apply (CFC.sqrt_eq_iff _ _ hp.nonneg hs.nonneg).mpr
  simp [smul_smul, Real.mul_self_sqrt hm]

lemma norm_vec_sq (v : Fin d → ℝ) : ‖vec d v‖ ^ 2 = v ⬝ᵥ v := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [vec, PiLp.toLp_apply, Real.norm_eq_abs, sq_abs]
  simp only [dotProduct, pow_two]

/-- A genuine quadratic lower bound passes through the principal matrix square root.
The proof diagonalizes the actual square root and tests the lower bound for C
on its orthonormal eigenvectors. -/
lemma sqrt_lower [NeZero d] (C : Mat d) (hC : C.PosDef) (m : ℝ) (_hm : 0 ≤ m)
    (hLower : ∀ v : Fin d → ℝ, m * (v ⬝ᵥ v) ≤ v ⬝ᵥ (C *ᵥ v)) :
    ∀ v : Fin d → ℝ, Real.sqrt m * (v ⬝ᵥ v) ≤ v ⬝ᵥ (CFC.sqrt C *ᵥ v) := by
  have hs := hC.posDef_sqrt
  have he (i : Fin d) : Real.sqrt m ≤ hs.1.eigenvalues i := by
    let w : Fin d → ℝ := WithLp.ofLp (hs.1.eigenvectorBasis i)
    have hw : w ⬝ᵥ w = 1 := by
      rw [← norm_vec_sq]
      change ‖hs.1.eigenvectorBasis i‖ ^ 2 = 1
      rw [hs.1.eigenvectorBasis.orthonormal.norm_eq_one]
      norm_num
    have heig : CFC.sqrt C *ᵥ w = hs.1.eigenvalues i • w := hs.1.mulVec_eigenvectorBasis i
    have hcw : C *ᵥ w = hs.1.eigenvalues i ^ 2 • w := by
      calc
        C *ᵥ w = (CFC.sqrt C * CFC.sqrt C) *ᵥ w :=
          congrArg (fun M : Mat d => M *ᵥ w) (CFC.sqrt_mul_sqrt_self C hC.posSemidef.nonneg).symm
        _ = _ := by
          rw [← Matrix.mulVec_mulVec, heig, Matrix.mulVec_smul, heig, smul_smul, ← pow_two]
    have hl := hLower w
    rw [hcw, dotProduct_smul, smul_eq_mul, hw, mul_one, mul_one] at hl
    exact Real.sqrt_le_iff.mpr ⟨hs.posSemidef.eigenvalues_nonneg i, hl⟩
  have hp := (Paper38.AffineLifting.shift_posSemidef (CFC.sqrt C) hs.1 (Real.sqrt m) he)
  intro v
  have hq := hp.2 v
  exact sub_nonneg.mp (by
    simpa only [star_trivial, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      dotProduct_sub, dotProduct_smul, smul_eq_mul] using hq)

/-- Equation (7.4), before choosing the actual smallest eigenvalues as lower bounds. -/
theorem sqrt_lipschitz_of_lower [NeZero d] (C D : Mat d) (hC : C.PosDef) (hD : D.PosDef)
    (mC mD : ℝ) (hmC : 0 ≤ mC) (hmD : 0 ≤ mD)
    (hden : 0 < Real.sqrt mC + Real.sqrt mD)
    (hLowerC : ∀ v : Fin d → ℝ, mC * (v ⬝ᵥ v) ≤ v ⬝ᵥ (C *ᵥ v))
    (hLowerD : ∀ v : Fin d → ℝ, mD * (v ⬝ᵥ v) ≤ v ⬝ᵥ (D *ᵥ v)) :
    frobNorm (CFC.sqrt C - CFC.sqrt D) ≤
      frobNorm (C - D) / (Real.sqrt mC + Real.sqrt mD) := by
  let X := CFC.sqrt C - CFC.sqrt D
  have hleft := left_rayleigh (CFC.sqrt C) X (Real.sqrt mC) (sqrt_lower C hC mC hmC hLowerC)
  have hdt : (CFC.sqrt D)ᵀ = CFC.sqrt D := by simpa using hD.posDef_sqrt.1
  have hright := right_rayleigh (CFC.sqrt D) X (Real.sqrt mD) hdt
    (sqrt_lower D hD mD hmD hLowerD)
  have he : CFC.sqrt C * X + X * CFC.sqrt D = C - D := by
    dsimp [X]
    rw [Matrix.mul_sub, Matrix.sub_mul]
    rw [CFC.sqrt_mul_sqrt_self C hC.posSemidef.nonneg,
      CFC.sqrt_mul_sqrt_self D hD.posSemidef.nonneg]
    abel
  have hlow : (Real.sqrt mC + Real.sqrt mD) * frobSq X ≤ matrixInner X (C - D) := by
    rw [← he, matrixInner_add_right]
    linarith
  have hcs : matrixInner X (C - D) ≤ frobNorm X * frobNorm (C - D) := by
    simpa only [inner_flatten, frobNorm] using real_inner_le_norm (flattenEquiv d X) (flattenEquiv d (C-D))
  rw [← frobNorm_sq] at hlow
  have hx : 0 ≤ frobNorm X := norm_nonneg _
  by_cases hz : frobNorm X = 0
  · change frobNorm X ≤ _
    rw [hz]
    exact div_nonneg (norm_nonneg _) hden.le
  · have hx' : 0 < frobNorm X := lt_of_le_of_ne hx (Ne.symm hz)
    apply (le_div_iff₀ hden).mpr
    change frobNorm X * (Real.sqrt mC + Real.sqrt mD) ≤ frobNorm (C-D)
    nlinarith [hlow.trans hcs]

lemma eigenMin_pos [NeZero d] (C : Mat d) (hC : C.PosDef) :
    0 < Paper38.AffineLifting.eigenMin C hC.1 := by
  rw [Paper38.AffineLifting.eigenMin, Finset.lt_inf'_iff]
  intro i _
  exact hC.eigenvalues_pos i

/-- The literal smallest-eigenvalue form of source equation (7.4). -/
theorem sqrt_lipschitz [NeZero d] (C D : Mat d) (hC : C.PosDef) (hD : D.PosDef) :
    frobNorm (CFC.sqrt C - CFC.sqrt D) ≤ frobNorm (C-D) /
      (Real.sqrt (Paper38.AffineLifting.eigenMin C hC.1) +
        Real.sqrt (Paper38.AffineLifting.eigenMin D hD.1)) := by
  have hc := eigenMin_pos C hC
  have hd := eigenMin_pos D hD
  apply sqrt_lipschitz_of_lower C D hC hD _ _ hc.le hd.le
    (add_pos (Real.sqrt_pos.mpr hc) (Real.sqrt_pos.mpr hd))
  · intro v
    have h := Paper38.AffineLifting.lower_rayleigh C hC.1 (vec d v)
    rw [Paper38.AffineLifting.inner_matVec_eq, norm_vec_sq] at h
    simpa only [vec, WithLp.ofLp_toLp] using h
  · intro v
    have h := Paper38.AffineLifting.lower_rayleigh D hD.1 (vec d v)
    rw [Paper38.AffineLifting.inner_matVec_eq, norm_vec_sq] at h
    simpa only [vec, WithLp.ofLp_toLp] using h

/-- A common bounded mean/covariance-root box with a strict spectral barrier. -/
def compactBox (l B : ℝ) : Set (Tangent d) :=
  {q | ‖q‖ ≤ B ∧ ∀ v : E d, l * ‖v‖ ^ 2 ≤ quadratic (toModel d q).2 v}

lemma compactBox_isClosed (l B : ℝ) : IsClosed (compactBox (d := d) l B) := by
  have hc (v : E d) : Continuous (fun q : Tangent d => quadratic (toModel d q).2 v) := by
    unfold quadratic Matrix.mulVec dotProduct
    fun_prop
  have hs : IsClosed (⋂ v : E d, {q : Tangent d | l * ‖v‖ ^ 2 ≤ quadratic (toModel d q).2 v}) :=
    isClosed_iInter (fun v => isClosed_le continuous_const (hc v))
  have hn : IsClosed {q : Tangent d | ‖q‖ ≤ B} := isClosed_le continuous_norm continuous_const
  convert hn.inter hs using 1
  ext q
  simp [compactBox]

lemma compactBox_isCompact (l B : ℝ) : IsCompact (compactBox (d := d) l B) := by
  apply Metric.isCompact_of_isClosed_isBounded (compactBox_isClosed l B)
  apply (Metric.isBounded_closedBall (x := (0 : Tangent d)) (r := B)).subset
  intro q hq
  simpa only [Metric.mem_closedBall, dist_zero_right] using hq.1

lemma compactBox_subset_Domain (l B : ℝ) (hl : 0 < l) :
    compactBox (d := d) l B ⊆ Domain d := by
  intro q hq
  apply (posDef_iff_quadratic_unit _ (toModel_symmetric q)).mpr
  intro v
  have hn : ‖v.val‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using v.property
  have hh := hq.2 v.val
  rw [hn, one_pow, mul_one] at hh
  exact hl.trans_le hh

/-- The actual principal-root moment state associated to a mean and covariance. -/
def rootState (μ : E d) (C : Mat d) : Tangent d :=
  ofModel (μ, CFC.sqrt C) (by
    have hp : (CFC.sqrt C).PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg C)
    simpa using hp.1)

@[simp] lemma toModel_rootState (μ : E d) (C : Mat d) :
    toModel d (rootState μ C) = (μ, CFC.sqrt C) := toModel_ofModel _ _

lemma frobSq_sqrt_trace (C : Mat d) (hC : C.PosDef) : frobSq (CFC.sqrt C) = C.trace := by
  change Standardization.frobSq (CFC.sqrt C) = C.trace
  rw [← Standardization.trace_self_transpose]
  have ht : (CFC.sqrt C)ᵀ = CFC.sqrt C := by simpa using hC.posDef_sqrt.1
  rw [ht, CFC.sqrt_mul_sqrt_self C hC.posSemidef.nonneg]

/-- Fixed quantitative mean/second-moment bounds place an actual Gaussian
moment state in one compact subset of the source positive definite domain. -/
theorem rootState_mem_compactBox [NeZero d] (μ : E d) (C : Mat d) (hC : C.PosDef)
    (m M T : ℝ) (hm : 0 < m) (_hM : 0 ≤ M) (hmean : ‖μ‖ ≤ M) (htrace : C.trace ≤ T)
    (hLower : ∀ v : Fin d → ℝ, m * (v ⬝ᵥ v) ≤ v ⬝ᵥ (C *ᵥ v)) :
    rootState μ C ∈ compactBox (Real.sqrt m) (M ^ 2 + T + 1) := by
  have hn : ‖rootState μ C‖ ^ 2 = ‖μ‖ ^ 2 + C.trace := by
    have hh := norm_ambient_sq (toModel d (rootState μ C))
    rw [ambient_toModel, toModel_rootState, frobSq_sqrt_trace C hC] at hh
    exact hh
  constructor
  · have hmean2 : ‖μ‖ ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hmean 2
    have hx := norm_nonneg (rootState μ C)
    nlinarith [sq_nonneg (‖rootState μ C‖ - 1)]
  · intro v
    have hh := sqrt_lower C hC m hm.le hLower (WithLp.ofLp v)
    have hv : WithLp.ofLp v ⬝ᵥ WithLp.ofLp v = ‖v‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq]
      simp only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
    simpa only [toModel_rootState, quadratic, hv] using hh

/-- The deterministic initial moment mismatch bound used before (7.3) and (7.7). -/
theorem rootState_distance_sq_le [NeZero d] (μ ν : E d) (C D : Mat d)
    (hC : C.PosDef) (hD : D.PosDef) (mC mD : ℝ) (hmC : 0 ≤ mC) (hmD : 0 ≤ mD)
    (hden : 0 < Real.sqrt mC + Real.sqrt mD)
    (hLowerC : ∀ v : Fin d → ℝ, mC * (v ⬝ᵥ v) ≤ v ⬝ᵥ (C *ᵥ v))
    (hLowerD : ∀ v : Fin d → ℝ, mD * (v ⬝ᵥ v) ≤ v ⬝ᵥ (D *ᵥ v)) :
    ‖rootState μ C - rootState ν D‖ ^ 2 ≤ ‖μ - ν‖ ^ 2 +
      frobSq (C-D) / (Real.sqrt mC + Real.sqrt mD) ^ 2 := by
  have h := sqrt_lipschitz_of_lower C D hC hD mC mD hmC hmD hden hLowerC hLowerD
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  have hsq : frobSq (CFC.sqrt C - CFC.sqrt D) ≤
      frobSq (C-D) / (Real.sqrt mC + Real.sqrt mD) ^ 2 := by
    calc
      frobSq (CFC.sqrt C - CFC.sqrt D) = frobNorm (CFC.sqrt C - CFC.sqrt D) ^ 2 :=
        (frobNorm_sq _).symm
      _ ≤ _ := h2
      _ = _ := by rw [div_pow, frobNorm_sq]
  rw [← coordinateSqDist_toModel, toModel_rootState, toModel_rootState]
  exact add_le_add_left hsq _

lemma opNorm_nonneg (A : Mat d) : 0 ≤ Sampling.opNorm A := norm_nonneg _

lemma norm_matVec_le (A : Mat d) (v : E d) :
    ‖matVec A v‖ ≤ Sampling.opNorm A * ‖v‖ :=
  (Matrix.toEuclideanLin A).toContinuousLinearMap.le_opNorm v

lemma quadratic_eq_inner (A : Mat d) (v : E d) :
    quadratic A v = inner ℝ v (matVec A v) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [quadratic, matVec, vec, WithLp.ofLp_toLp, star_trivial]
  exact dotProduct_comm _ _

lemma dot_self_norm_sq (v : E d) : WithLp.ofLp v ⬝ᵥ WithLp.ofLp v = ‖v‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial]

/-- Operator-norm closeness to I gives both genuine quadratic covariance bounds. -/
theorem rayleigh_of_opNorm (S : Mat d) (ε : ℝ) (hS : Sampling.opNorm (S-1) ≤ ε)
    (v : E d) :
    (1-ε) * ‖v‖ ^ 2 ≤ quadratic S v ∧ quadratic S v ≤ (1+ε) * ‖v‖ ^ 2 := by
  have hnorm : ‖matVec (S-1) v‖ ≤ ε * ‖v‖ :=
    (norm_matVec_le _ _).trans (mul_le_mul_of_nonneg_right hS (norm_nonneg _))
  have hab : |quadratic (S-1) v| ≤ ε * ‖v‖ ^ 2 := by
    rw [quadratic_eq_inner]
    calc
      |inner ℝ v (matVec (S-1) v)| ≤ ‖v‖ * ‖matVec (S-1) v‖ := abs_real_inner_le_norm _ _
      _ ≤ ‖v‖ * (ε * ‖v‖) := mul_le_mul_of_nonneg_left hnorm (norm_nonneg _)
      _ = _ := by ring
  have he : quadratic (S-1) v = quadratic S v - ‖v‖ ^ 2 := by
    simp only [quadratic, Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub, dot_self_norm_sq]
  rw [he] at hab
  have hh := abs_le.mp hab
  constructor <;> nlinarith [hh.1, hh.2]

lemma posDef_of_opNorm (S : Mat d) (hSym : Sᵀ = S) (ε : ℝ)
    (hε : ε < 1) (hS : Sampling.opNorm (S-1) ≤ ε) : S.PosDef := by
  apply (posDef_iff_quadratic_unit S hSym).mpr
  intro v
  have hn : ‖v.val‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using v.property
  have hl := (rayleigh_of_opNorm S ε hS v.val).1
  rw [hn, one_pow, mul_one] at hl
  exact (sub_pos.mpr hε).trans_le hl

lemma affine_quadratic (A S : Mat d) (hA : Aᵀ = A) (v : E d) :
    quadratic (A * S * Aᵀ) v = quadratic S (matVec A v) := by
  rw [quadratic_eq_inner, quadratic_eq_inner]
  rw [GaussianAffine.matVec_mul, GaussianAffine.matVec_mul, hA]
  calc
    inner ℝ v (matVec A (matVec S (matVec A v))) =
        inner ℝ (matVec A (matVec S (matVec A v))) v := real_inner_comm _ _
    _ = inner ℝ (matVec S (matVec A v)) (matVec A v) := by
      rw [GaussianAffine.inner_matVec, hA]
    _ = _ := real_inner_comm _ _

theorem affine_covariance_rayleigh [NeZero d] (A S : Mat d) (hA : A.PosDef)
    (ε : ℝ) (hε : 0 ≤ ε) (hε' : ε < 1) (hS : Sampling.opNorm (S-1) ≤ ε) (v : E d) :
    ((1-ε) * (Paper38.AffineLifting.covarianceMin A : ℝ)) * ‖v‖ ^ 2 ≤
      quadratic (A*S*Aᵀ) v ∧
    quadratic (A*S*Aᵀ) v ≤ ((1+ε) * (Paper38.AffineLifting.covarianceMax A : ℝ)) * ‖v‖ ^ 2 := by
  have ht : Aᵀ = A := by simpa using hA.1
  rw [affine_quadratic A S ht]
  have hs := rayleigh_of_opNorm S ε hS (matVec A v)
  have ha := Paper38.AffineLifting.norm_sq_bounds A v
  have hl := mul_le_mul_of_nonneg_left ha.1 (sub_nonneg.mpr hε'.le)
  have hu := mul_le_mul_of_nonneg_left ha.2 (add_nonneg zero_le_one hε)
  constructor <;> nlinarith [hs.1, hs.2]

/-- The actual initial cloud for a fixed full-rank population Gaussian. -/
def initialCloud {N : ℕ} (μ : E d) (A : Mat d) (ω : Sampling.Sample d N) : Fin N → E d :=
  fun i => μ + matVec A (Sampling.cloud d N ω i)

lemma matVec_sub (A : Mat d) (x y : E d) :
    matVec A (x-y) = matVec A x - matVec A y :=
  (Matrix.toEuclideanLin A).map_sub x y

lemma initialCloud_centered_lift {N : ℕ} (μ : E d) (A : Mat d) (ω : Sampling.Sample d N) :
    initialCloud μ A ω = fun i =>
      (μ + matVec A (Sampling.mean d N ω)) +
        matVec A (Sampling.cloud d N ω i - empiricalMean (Sampling.cloud d N ω)) := by
  funext i
  unfold initialCloud Sampling.mean
  rw [matVec_sub]
  abel

/-- Exact source affine mean and covariance identities on the raw Gaussian sample. -/
theorem initial_moments {N : ℕ} (hN : 0 < N) (μ : E d) (A : Mat d)
    (ω : Sampling.Sample d N) :
    empiricalMean (initialCloud μ A ω) = μ + matVec A (Sampling.mean d N ω) ∧
    empiricalCovariance (initialCloud μ A ω) = A * Sampling.covariance d N ω * Aᵀ := by
  rw [initialCloud_centered_lift]
  exact ⟨ModelBridges.empiricalMean_affine_lift hN _ _ _,
    ModelBridges.empiricalCovariance_affine_lift hN _ _ _⟩

section FrobeniusNorm
open scoped Matrix.Norms.Frobenius

lemma frobNorm_eq_matrixNorm (A : Mat d) : frobNorm A = ‖A‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  calc
    ‖flattenEquiv d A‖ ^ 2 = frobSq A := norm_flatten_sq A
    _ = ‖A‖ ^ 2 := by
      change frobSq A =
        ‖(WithLp.toLp 2 (fun i : Fin d => WithLp.toLp 2 (fun j : Fin d => A i j)) :
          PiLp 2 (fun _ : Fin d => EuclideanSpace ℝ (Fin d)))‖ ^ 2
      rw [PiLp.norm_sq_eq_of_L2]
      simp only [PiLp.toLp_apply, EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs, frobSq]

lemma frobNorm_mul (A B : Mat d) : frobNorm (A*B) ≤ frobNorm A * frobNorm B := by
  simp only [frobNorm_eq_matrixNorm]
  exact norm_mul_le _ _

@[simp] lemma frobNorm_transpose (A : Mat d) : frobNorm Aᵀ = frobNorm A := by
  simp only [frobNorm_eq_matrixNorm, Matrix.frobenius_norm_transpose]

end FrobeniusNorm

lemma covarianceMin_pos [NeZero d] (A : Mat d) (hA : A.PosDef) :
    0 < (Paper38.AffineLifting.covarianceMin A : ℝ) := by
  have hp : (A*Aᵀ).PosDef := by
    have hh := Matrix.PosDef.mul_conjTranspose_self A
      (Matrix.vecMul_injective_iff_isUnit.mpr hA.isUnit)
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hh
  exact eigenMin_pos (A*Aᵀ) hp

lemma trace_le_of_rayleigh (C : Mat d) (T : ℝ)
    (hUpper : ∀ v : E d, quadratic C v ≤ T * ‖v‖ ^ 2) : C.trace ≤ (d : ℝ) * T := by
  calc
    C.trace = ∑ i, C i i := rfl
    _ ≤ ∑ _i : Fin d, T := by
      apply Finset.sum_le_sum
      intro i _
      have h := hUpper (vec d (Pi.single i 1))
      rw [norm_vec_sq] at h
      simpa [quadratic, vec, Matrix.mulVec_single_one, dotProduct, Pi.single_apply] using h
    _ = _ := by simp

def meanBoxBound (μ : E d) (A : Mat d) (r : ℝ) : ℝ := ‖μ‖ + Sampling.opNorm A * r

def covarianceBoxLower [NeZero d] (A : Mat d) (ε : ℝ) : ℝ :=
  (1-ε) * (Paper38.AffineLifting.covarianceMin A : ℝ)

def covarianceBoxTrace [NeZero d] (A : Mat d) (ε : ℝ) : ℝ :=
  (d : ℝ) * ((1+ε) * (Paper38.AffineLifting.covarianceMax A : ℝ))

def localizationBox [NeZero d] (μ : E d) (A : Mat d) (r ε : ℝ) : Set (Tangent d) :=
  compactBox (Real.sqrt (covarianceBoxLower A ε))
    ((meanBoxBound μ A r) ^ 2 + covarianceBoxTrace A ε + 1)

lemma localizationBox_isCompact [NeZero d] (μ : E d) (A : Mat d) (r ε : ℝ) :
    IsCompact (localizationBox μ A r ε) := compactBox_isCompact _ _

lemma localizationBox_subset_Domain [NeZero d] (μ : E d) (A : Mat d) (hA : A.PosDef)
    (r ε : ℝ) (hε : ε < 1) : localizationBox μ A r ε ⊆ Domain d := by
  apply compactBox_subset_Domain
  apply Real.sqrt_pos.mpr
  exact mul_pos (sub_pos.mpr hε) (covarianceMin_pos A hA)

/-- Mean and covariance on a raw well-conditioned box yield a fixed compact
source state box. No energy or particle estimate is an input. -/
theorem affine_state_mem_localizationBox [NeZero d] (μ : E d) (A : Mat d) (hA : A.PosDef)
    (z : E d) (S : Mat d) (hSym : Sᵀ = S) (r ε : ℝ)
    (hr : 0 ≤ r) (hε : 0 ≤ ε) (hε' : ε < 1) (hz : ‖z‖ ≤ r)
    (hS : Sampling.opNorm (S-1) ≤ ε) :
    rootState (μ + matVec A z) (A*S*Aᵀ) ∈ localizationBox μ A r ε := by
  have hpS := posDef_of_opNorm S hSym ε hε' hS
  have hpC : (A*S*Aᵀ).PosDef := by
    have hh := hpS.mul_mul_conjTranspose_same
      (Matrix.vecMul_injective_iff_isUnit.mpr hA.isUnit)
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hh
  have hlow : 0 < covarianceBoxLower A ε :=
    mul_pos (sub_pos.mpr hε') (covarianceMin_pos A hA)
  have hmean : ‖μ + matVec A z‖ ≤ meanBoxBound μ A r := by
    exact (norm_add_le _ _).trans (add_le_add_left
      ((norm_matVec_le A z).trans (mul_le_mul_of_nonneg_left hz (opNorm_nonneg A))) _)
  apply rootState_mem_compactBox _ _ hpC _ _ _ hlow
    (add_nonneg (norm_nonneg _) (mul_nonneg (opNorm_nonneg A) hr)) hmean
  · apply trace_le_of_rayleigh
    intro v
    exact (affine_covariance_rayleigh A S hA ε hε hε' hS v).2
  · intro v
    have h := (affine_covariance_rayleigh A S hA ε hε hε' hS (vec d v)).1
    rw [norm_vec_sq] at h
    simpa only [quadratic, vec, WithLp.ofLp_toLp] using h

/-- The fixed population state belongs to the very same deterministic box. -/
theorem population_mem_localizationBox [NeZero d] (μ : E d) (A : Mat d) (hA : A.PosDef)
    (r ε : ℝ) (hr : 0 ≤ r) (hε : 0 ≤ ε) (hε' : ε < 1) :
    rootState μ (A*Aᵀ) ∈ localizationBox μ A r ε := by
  have h := affine_state_mem_localizationBox μ A hA 0 1 (by simp) r ε hr hε hε'
    (by simpa using hr) (by simpa [Sampling.opNorm] using hε)
  simpa [matVec, vec] using h

/-- Source (7.1): every actual Gaussian initialized sample on G_N lies in a
single deterministic compact positive definite coordinate box. -/
theorem good_initial_state_localized [NeZero d] {N : ℕ} (hN : 0 < N)
    (μ : E d) (A : Mat d) (hA : A.PosDef) (ω : Sampling.Sample d N)
    (hω : ω ∈ Sampling.good d N) :
    rootState (empiricalMean (initialCloud μ A ω))
      (empiricalCovariance (initialCloud μ A ω)) ∈ localizationBox μ A (1/4) (1/4) := by
  have hp := ModelBridges.empiricalCovariance_posSemidef (Sampling.cloud d N ω)
  have ht : (Sampling.covariance d N ω)ᵀ = Sampling.covariance d N ω := by simpa using hp.1
  rw [(initial_moments hN μ A ω).1, (initial_moments hN μ A ω).2]
  exact affine_state_mem_localizationBox μ A hA _ _ ht _ _
    (by norm_num) (by norm_num) (by norm_num) hω.1 hω.2

/-- Continuity of the actual energy follows from the proved Gaussian average
regularity and continuity of the logarithm at the positive determinant. -/
theorem energy_continuousOn {V : E d → ℝ} {α β : ℝ}
    (hV : AdmissiblePotential V α β) : ContinuousOn (HilbertCoordinates.energy V) (Domain d) := by
  have hav : Continuous (GaussianDifferentiation.potentialAverage V) :=
    (GaussianDifferentiation.potentialAverage_contDiff hV).continuous
  have hp : Continuous (fun q : Tangent d =>
      GaussianDifferentiation.potentialAverage V (toModel d q)) := hav.comp (toModel d).continuous
  have hd : Continuous (fun q : Tangent d => (toModel d q).2.det) := by fun_prop
  have hl : ContinuousOn (fun q : Tangent d => Real.log (toModel d q).2.det) (Domain d) :=
    hd.continuousOn.log (fun q hq => hq.det_pos.ne')
  exact hp.continuousOn.sub hl

/-- A single deterministic sublevel contains the entire localized compact box.
The radius is chosen before any sample size or cloud. -/
theorem exists_common_energy_sublevel [NeZero d] {V : E d → ℝ} {α β : ℝ}
    (hV : AdmissiblePotential V α β) (μ : E d) (A : Mat d) (hA : A.PosDef)
    (r ε : ℝ) (hε : ε < 1) (qstar : Coordinates d) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ q ∈ localizationBox μ A r ε,
      toModel d q ∈ Model.sublevel V qstar R := by
  have hK := localizationBox_isCompact μ A r ε
  have hKD := localizationBox_subset_Domain μ A hA r ε hε
  have hc : ContinuousOn (HilbertCoordinates.energy V) (localizationBox μ A r ε) :=
    (energy_continuousOn hV).mono hKD
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hc
  refine ⟨max 0 (M - Model.energy V qstar), le_max_left _ _, ?_⟩
  intro q hq
  refine ⟨hKD hq, ?_⟩
  have hh := hM q hq
  have hupper : HilbertCoordinates.energy V q ≤ M := (le_abs_self _).trans hh
  exact (sub_le_sub_right hupper _).trans (le_max_right _ _)

/-- The common energy sublevel part of Lemma 7.1, for the actual initialized
cloud and fixed population state, uniformly in N. -/
theorem good_common_energy_sublevel [NeZero d] {V : E d → ℝ} {α β : ℝ}
    (hV : AdmissiblePotential V α β) (μ : E d) (A : Mat d) (hA : A.PosDef)
    (qstar : Coordinates d) :
    ∃ R : ℝ, 0 ≤ R ∧
      toModel d (rootState μ (A*Aᵀ)) ∈ Model.sublevel V qstar R ∧
      ∀ N : ℕ, 0 < N → ∀ ω : Sampling.Sample d N, ω ∈ Sampling.good d N →
        Specification.cloudQ (initialCloud μ A ω) ∈ Model.sublevel V qstar R := by
  obtain ⟨R, hR, hbound⟩ := exists_common_energy_sublevel hV μ A hA (1/4) (1/4) (by norm_num) qstar
  refine ⟨R, hR, hbound _ (population_mem_localizationBox μ A hA _ _
    (by norm_num) (by norm_num) (by norm_num)), ?_⟩
  intro N hN ω hω
  have h := hbound _ (good_initial_state_localized hN μ A hA ω hω)
  simpa only [toModel_rootState, Specification.cloudQ, Model.covarianceRoot] using h

/-- The common sublevel statement with the paper's exact Gaussian-cloud parameters. -/
theorem gaussian_good_common_sublevel [NeZero d] {V : E d → ℝ} {α β : ℝ}
    (hV : AdmissiblePotential V α β) (μ : E d) (S0 : Mat d) (hS0 : S0.PosDef)
    (qstar : Coordinates d) :
    ∃ R : ℝ, 0 ≤ R ∧ (μ, covarianceRoot S0) ∈ Model.sublevel V qstar R ∧
      ∀ N : ℕ, 0 < N → ∀ ω : Sampling.Sample d N, ω ∈ Sampling.good d N →
        Specification.cloudQ (Specification.gaussianCloud μ S0 N ω) ∈ Model.sublevel V qstar R := by
  have hs : (covarianceRoot S0).PosDef := hS0.posDef_sqrt
  have ht : (covarianceRoot S0)ᵀ = covarianceRoot S0 := by simpa using hs.1
  have hc : covarianceRoot S0 * (covarianceRoot S0)ᵀ = S0 := by
    rw [ht]
    exact CFC.sqrt_mul_sqrt_self S0 hS0.posSemidef.nonneg
  obtain ⟨R, hR, hp, hbound⟩ := good_common_energy_sublevel hV μ (covarianceRoot S0) hs qstar
  refine ⟨R, hR, ?_, ?_⟩
  · rw [toModel_rootState] at hp
    change (μ, CFC.sqrt (CFC.sqrt S0 * (CFC.sqrt S0)ᵀ)) ∈ Model.sublevel V qstar R at hp
    have hcs : CFC.sqrt S0 * (CFC.sqrt S0)ᵀ = S0 := hc
    rw [hcs] at hp
    exact hp
  · intro N hN ω hω
    exact hbound N hN ω hω

/-- Exact non-principal whitening used in source (6.8): empirical whitening of
an affine Gaussian initialization is precisely raw standard-Gaussian whitening. -/
theorem initialization_whitening {N : ℕ} (hN : 0 < N) (μ : E d) (A : Mat d)
    (hA : IsUnit A) (ω : Sampling.Sample d N) (hS : (Sampling.covariance d N ω).PosDef) :
    let W := (covarianceRoot (Sampling.covariance d N ω))⁻¹ * A⁻¹
    IsWhitening (initialCloud μ A ω) W ∧
      standardizedCloud (initialCloud μ A ω) W = Sampling.standardized d N ω := by
  let S := Sampling.covariance d N ω
  let H := covarianceRoot S
  let W := H⁻¹ * A⁻¹
  have hH : H.PosDef := hS.posDef_sqrt
  have ht : Hᵀ = H := by simpa using hH.1
  have hiA : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A ((Matrix.isUnit_iff_isUnit_det A).mp hA)
  have hiH : H⁻¹ * H = 1 := Matrix.nonsing_inv_mul H ((Matrix.isUnit_iff_isUnit_det H).mp hH.isUnit)
  have hWA : W*A = H⁻¹ := by
    dsimp [W]
    rw [Matrix.mul_assoc, hiA, Matrix.mul_one]
  have hWB : W * (A*H) = 1 := by rw [← Matrix.mul_assoc, hWA, hiH]
  have hfact : empiricalCovariance (initialCloud μ A ω) = (A*H) * (A*H)ᵀ := by
    rw [(initial_moments hN μ A ω).2]
    change A*S*Aᵀ = _
    calc
      A*S*Aᵀ = A*(H*Hᵀ)*Aᵀ := by
        rw [ht, show H*H = S from CFC.sqrt_mul_sqrt_self S hS.posSemidef.nonneg]
      _ = _ := by simp only [Matrix.transpose_mul, Matrix.mul_assoc]
  change IsWhitening (initialCloud μ A ω) W ∧ _
  constructor
  · change W * empiricalCovariance (initialCloud μ A ω) * Wᵀ = 1
    rw [hfact]
    calc
      W*((A*H)*(A*H)ᵀ)*Wᵀ = (W*(A*H))*(W*(A*H))ᵀ := by
        simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = 1 := by rw [hWB]; simp
  · funext i
    change matVec W (initialCloud μ A ω i - empiricalMean (initialCloud μ A ω)) =
      matVec H⁻¹ (Sampling.cloud d N ω i - Sampling.mean d N ω)
    rw [(initial_moments hN μ A ω).1]
    have hcent : initialCloud μ A ω i - (μ + matVec A (Sampling.mean d N ω)) =
        matVec A (Sampling.cloud d N ω i - Sampling.mean d N ω) := by
      unfold initialCloud
      rw [matVec_sub]
      abel
    rw [hcent, ← GaussianAffine.matVec_mul, hWA]

/-- The same bridge with the exact population-covariance initialization of the paper. -/
theorem gaussianCloud_whitening {N : ℕ} (hN : 0 < N) (μ : E d) (S0 : Mat d)
    (hS0 : S0.PosDef) (ω : Sampling.Sample d N) (hS : (Sampling.covariance d N ω).PosDef) :
    let W := (covarianceRoot (Sampling.covariance d N ω))⁻¹ * (covarianceRoot S0)⁻¹
    IsWhitening (Specification.gaussianCloud μ S0 N ω) W ∧
      standardizedCloud (Specification.gaussianCloud μ S0 N ω) W = Sampling.standardized d N ω :=
  initialization_whitening hN μ (covarianceRoot S0) hS0.posDef_sqrt.isUnit ω hS

end Paper38.GaussianLocalization
