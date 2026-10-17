import Paper38.HilbertMobility
import Paper38.GaussianEnergyFacts

/-! Compact source sublevels give actual spectral and explicit mobility bounds. -/
noncomputable section
open scoped Matrix MatrixOrder Matrix.Norms.Frobenius InnerProductSpace
namespace Paper38.SourceGeometryBounds
open Model HilbertCoordinates Set
set_option maxHeartbeats 400000

/-- A compact family of genuinely positive matrices has a uniform positive
quadratic lower bound. The state and vector spaces are kept distinct. -/
theorem compact_matrix_lower {d : ℕ} {K : Set (Tangent d)}
    (hK : IsCompact K) (hKD : K ⊆ Domain d) :
    ∃ a > 0, ∀ q ∈ K, ∀ v : E d,
      a * ‖v‖^2 ≤ ⟪v, matVec (matrixProjection d q) v⟫_ℝ := by
  classical
  rcases subsingleton_or_nontrivial (E d) with hE | hE
  · letI := hE
    refine ⟨1, zero_lt_one, ?_⟩
    intro q hq v
    have hv : v = 0 := Subsingleton.elim _ _
    simp [hv]
  · letI := hE
    by_cases hne : K.Nonempty
    · obtain ⟨q₀,hq₀⟩ := hne
      obtain ⟨w,hw⟩ := exists_norm_eq (E d) (by norm_num : 0 ≤ (1:ℝ))
      let S : Set (Tangent d × E d) := K ×ˢ Metric.sphere (0:E d) 1
      let φ : Tangent d × E d → ℝ := fun x =>
        ⟪x.2, (HilbertMobility.matrixAction d) (matrixProjection d x.1) x.2⟫_ℝ
      have hS : IsCompact S := hK.prod (isCompact_sphere (0:E d) 1)
      have hSne : S.Nonempty := ⟨(q₀,w),hq₀,by simpa using hw⟩
      have hc : Continuous φ := continuous_snd.inner
        (((HilbertMobility.matrixAction d).continuous.comp
          ((matrixProjection d).continuous.comp continuous_fst)).clm_apply continuous_snd)
      obtain ⟨x,hx,hxmin⟩ := hS.exists_isMinOn hSne hc.continuousOn
      have hxunit : ‖x.2‖ = 1 := by simpa using hx.2
      have hx0 : WithLp.ofLp x.2 ≠ 0 := by
        intro h
        have hx0 : x.2 = 0 := congrArg (WithLp.toLp 2) h
        simp [hx0] at hxunit
      have hpos : 0 < φ x := by
        change 0 < ⟪x.2, matVec (matrixProjection d x.1) x.2⟫_ℝ
        simpa only [matVec,vec,EuclideanSpace.inner_eq_star_dotProduct,
          WithLp.ofLp_toLp,star_trivial,dotProduct_comm] using (hKD hx.1).2 _ hx0
      refine ⟨φ x,hpos,?_⟩
      intro q hq v
      by_cases hv : v = 0
      · simp [hv]
      · let u := (‖v‖⁻¹ : ℝ) • v
        have hu : u ∈ Metric.sphere (0:E d) 1 := by
          simpa only [Metric.mem_sphere, dist_zero_right] using norm_smul_inv_norm (𝕜 := ℝ) hv
        have hunit : φ x ≤ φ (q,u) := hxmin ⟨hq,hu⟩
        have hvnorm : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
        calc
          φ x * ‖v‖^2 ≤ φ (q,u) * ‖v‖^2 :=
            mul_le_mul_of_nonneg_right hunit (sq_nonneg _)
          _ = ⟪v, matVec (matrixProjection d q) v⟫_ℝ := by
            change ⟪(‖v‖⁻¹ : ℝ) • v, (HilbertMobility.matrixAction d) (matrixProjection d q) ((‖v‖⁻¹ : ℝ) • v)⟫_ℝ * ‖v‖^2 = _
            rw [map_smul, inner_smul_left, inner_smul_right]
            simp only [conj_trivial, HilbertMobility.matrixAction_apply]
            field_simp
    · refine ⟨1,zero_lt_one,?_⟩
      intro q hq
      exact False.elim (hne ⟨q,hq⟩)

/-- Genuine Euclidean and Loewner bounds on every compact source sublevel. -/
theorem compact_spectral_bounds {d : ℕ} {K : Set (Tangent d)}
    (hK : IsCompact K) (hKD : K ⊆ Domain d) :
    ∃ M a b : ℝ, 0 < M ∧ 0 < a ∧ 0 < b ∧
      ∀ q ∈ K, ‖meanProjection d q‖ ≤ M ∧
        (∀ v : E d, a * ‖v‖^2 ≤ ⟪v,matVec (matrixProjection d q) v⟫_ℝ ∧
          ⟪v,matVec (matrixProjection d q) v⟫_ℝ ≤ b * ‖v‖^2) ∧
        (∀ v : E d, a^2 * ‖v‖^2 ≤ ‖matVec (matrixProjection d q) v‖^2 ∧
          ‖matVec (matrixProjection d q) v‖^2 ≤ b^2 * ‖v‖^2) := by
  obtain ⟨a,ha,hlow⟩ := compact_matrix_lower hK hKD
  obtain ⟨M,hM⟩ := hK.exists_bound_of_continuousOn (meanProjection d).continuous.continuousOn
  obtain ⟨b,hb⟩ := hK.exists_bound_of_continuousOn
    ((HilbertMobility.matrixAction d).continuous.comp (matrixProjection d).continuous).continuousOn
  refine ⟨|M|+1,a,|b|+1,by positivity,ha,by positivity,?_⟩
  intro q hq
  have hmean : ‖meanProjection d q‖ ≤ |M|+1 := (hM q hq).trans (by linarith [le_abs_self M])
  have hbound (v : E d) : ‖matVec (matrixProjection d q) v‖ ≤ (|b|+1)*‖v‖ := by
    have hop := ((HilbertMobility.matrixAction d) (matrixProjection d q)).le_opNorm v
    change ‖matVec (matrixProjection d q) v‖ ≤ _ at hop
    exact hop.trans (mul_le_mul_of_nonneg_right ((hb q hq).trans (by linarith [le_abs_self b])) (norm_nonneg v))
  refine ⟨hmean,?_,?_⟩
  · intro v
    refine ⟨hlow q hq v,?_⟩
    calc
      ⟪v,matVec (matrixProjection d q) v⟫_ℝ ≤ ‖v‖ * ‖matVec (matrixProjection d q) v‖ := real_inner_le_norm _ _
      _ ≤ ‖v‖ * ((|b|+1)*‖v‖) := mul_le_mul_of_nonneg_left (hbound v) (norm_nonneg _)
      _ = (|b|+1)*‖v‖^2 := by ring
  · intro v
    have hcs := real_inner_le_norm v (matVec (matrixProjection d q) v)
    have hl := hlow q hq v
    have han : a*‖v‖ ≤ ‖matVec (matrixProjection d q) v‖ := by
      by_cases hv : v = 0
      · simp [hv]
      · have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
        nlinarith
    constructor
    · nlinarith [sq_nonneg (‖matVec (matrixProjection d q) v‖-a*‖v‖)]
    · have hnon : 0 ≤ (|b|+1)*‖v‖ := by positivity
      have hs := (sq_le_sq₀ (norm_nonneg _) hnon).mpr (hbound v)
      nlinarith

/-- The quadratic-form inequalities are exactly the source Loewner bounds,
using Mathlib's genuine positive-semidefinite matrix order. -/
theorem quadratic_loewner {d : ℕ} (q : Tangent d) (a b : ℝ)
    (hquad : ∀ v : E d,
      a*‖v‖^2 ≤ ⟪v,matVec (matrixProjection d q) v⟫_ℝ ∧
      ⟪v,matVec (matrixProjection d q) v⟫_ℝ ≤ b*‖v‖^2) :
    a • (1 : Mat d) ≤ matrixProjection d q ∧ matrixProjection d q ≤ b • (1 : Mat d) := by
  have hn (x : Fin d → ℝ) : ‖vec d x‖^2 = x ⬝ᵥ x := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [vec,EuclideanSpace.inner_eq_star_dotProduct,WithLp.ofLp_toLp,star_trivial]
  have hi (x : Fin d → ℝ) : ⟪vec d x,matVec (matrixProjection d q) (vec d x)⟫_ℝ =
      x ⬝ᵥ ((matrixProjection d q) *ᵥ x) := by
    simp only [matVec,vec,EuclideanSpace.inner_eq_star_dotProduct,WithLp.ofLp_toLp,star_trivial]
    exact dotProduct_comm _ _
  have hs : (matrixProjection d q).IsHermitian := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using toModel_symmetric q
  constructor
  · rw [Matrix.le_iff]
    refine ⟨hs.sub (by simp [Matrix.IsHermitian]),?_⟩
    intro x
    have h := (hquad (vec d x)).1
    rw [hn,hi] at h
    simpa only [star_trivial,Matrix.sub_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec,
      dotProduct_sub,dotProduct_smul,smul_eq_mul] using sub_nonneg.mpr h
  · rw [Matrix.le_iff]
    refine ⟨(show (b • (1 : Mat d)).IsHermitian by simp [Matrix.IsHermitian]).sub hs,?_⟩
    intro x
    have h := (hquad (vec d x)).2
    rw [hn,hi] at h
    simpa only [star_trivial,Matrix.sub_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec,
      dotProduct_sub,dotProduct_smul,smul_eq_mul] using sub_nonneg.mpr h

/-- The Hilbert norm is exactly the unmodified Euclidean--Frobenius pairing. -/
theorem norm_sq_pairing {d : ℕ} (v : Tangent d) :
    ‖v‖^2 = (WithLp.ofLp (meanProjection d v)) ⬝ᵥ (WithLp.ofLp (meanProjection d v)) +
      Mobility.frobenius (matrixProjection d v) (matrixProjection d v) := by
  rw [← real_inner_self_eq_norm_sq,inner_eq_mobility_pairing]
  rfl

/-- Exact P quadratic form in the constructed inverse-Sylvester components. -/
theorem P_quadratic_formula {d : ℕ} (q v : Tangent d) (hq : q ∈ Domain d) :
    ⟪v,HilbertMobility.P q v⟫_ℝ = Mobility.pairing
      (WithLp.ofLp (meanProjection d v)) (matrixProjection d v)
      (MobilityEllipticity.pullbackMobilityMean (WithLp.ofLp (meanProjection d q))
        (matrixProjection d q) hq (WithLp.ofLp (meanProjection d v)) (matrixProjection d v))
      (MobilityEllipticity.pullbackMobilityCov (WithLp.ofLp (meanProjection d q))
        (matrixProjection d q) hq (WithLp.ofLp (meanProjection d v)) (matrixProjection d v)) := by
  simp only [HilbertMobility.P,ContinuousLinearMap.comp_apply,
    HilbertMobility.inverseJ_eq q hq,inner_eq_mobility_pairing,
    HilbertMobility.toModel_inverseJOn,HilbertMobility.toModel_mobility,
    HilbertMobility.rawM_apply,Model.vec,WithLp.ofLp_toLp]
  rfl

/-- The exact source p_R bound for the actual intrinsic P, from genuine
Euclidean singular/mean bounds. No mobility lower bound is assumed. -/
theorem P_explicit_lower {d : ℕ} (q : Tangent d) (hq : q ∈ Domain d)
    (M a b : ℝ) (hmean : ‖meanProjection d q‖ ≤ M) (hM : 0 ≤ M)
    (hlower : ∀ v : E d, a^2 * ‖v‖^2 ≤ ‖matVec (matrixProjection d q) v‖^2)
    (hupper : ∀ v : E d, ‖matVec (matrixProjection d q) v‖^2 ≤ b^2 * ‖v‖^2)
    (v : Tangent d) :
    MobilityEllipticity.sublevelConstant a M b * ‖v‖^2 ≤ ⟪v,HilbertMobility.P q v⟫_ℝ := by
  have hn (x : Fin d → ℝ) : ‖vec d x‖^2 = x ⬝ᵥ x := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [vec,EuclideanSpace.inner_eq_star_dotProduct,WithLp.ofLp_toLp,star_trivial]
  have hmeansq : (WithLp.ofLp (meanProjection d q)) ⬝ᵥ
      (WithLp.ofLp (meanProjection d q)) ≤ M^2 := by
    have h := (sq_le_sq₀ (norm_nonneg _) hM).mpr hmean
    simpa only [← hn,vec,WithLp.toLp_ofLp] using h
  rw [norm_sq_pairing,P_quadratic_formula q v hq]
  apply MobilityEllipticity.pullback_mobility_ellipticity _ _ _ _ hq a M b
    (toModel_symmetric v)
  · intro x
    have hl := hlower (vec d x)
    change a^2 * ‖vec d x‖^2 ≤ ‖vec d ((matrixProjection d q) *ᵥ x)‖^2 at hl
    simpa only [hn] using hl
  · intro x
    have hu := hupper (vec d x)
    change ‖vec d ((matrixProjection d q) *ᵥ x)‖^2 ≤ b^2 * ‖vec d x‖^2 at hu
    simpa only [hn] using hu
  · exact hmeansq

end Paper38.SourceGeometryBounds
