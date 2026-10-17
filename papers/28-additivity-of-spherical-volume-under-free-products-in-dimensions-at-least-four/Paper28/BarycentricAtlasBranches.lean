import Paper28.BarycentricNeighborhoodAtlas
import Paper28.NormalizedAffineMaps

/-! The actual affine branches of the full-subcomplex construction. The
spherical lift on a cell is normalization of an explicit affine map. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Set
variable {H V Idx E : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [DecidableEq H]
  [Fintype V] [DecidableEq V] [Fintype Idx]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {K : FiniteEuclideanComplex H} (A : FullSubcomplexBarycentricAtlas K V Idx)

def atlasCell (j : Idx) : Set H := convexHull ℝ (A.vertex '' (A.cells j : Set V))

def atlasWeightedVector (q : V → E) (x : H) : E := ∑ v ∈ A.selected, A.hat v x • q v

def atlasLiftLinear (q : V → E) (j : Idx) : H →L[ℝ] E :=
  ∑ v ∈ A.selected, (A.slope j v).smulRight (q v)

def atlasLiftOffset (q : V → E) (j : Idx) : E :=
  ∑ v ∈ A.selected, A.offset j v • q v

def atlasSphereLift (q : V → E) (j : Idx) : H → E :=
  normalizedAffineMap (atlasLiftLinear A q j) (atlasLiftOffset A q j)

theorem atlasLift_raw_eq (q : V → E) (j : Idx) (x : H) (hx : x ∈ atlasCell A j) :
    atlasLiftLinear A q j x+atlasLiftOffset A q j = atlasWeightedVector A q x := by
  simp only [atlasLiftLinear,atlasLiftOffset,ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smulRight_apply,← Finset.sum_add_distrib,← add_smul]
  apply Finset.sum_congr rfl
  intro v _
  rw [← A.coordinate_on_cell j x hx v]

theorem atlasSphereLift_eq (q : V → E) (j : Idx) (x : H) (hx : x ∈ atlasCell A j) :
    atlasSphereLift A q j x = sphericalNormalize (atlasWeightedVector A q x) := by
  unfold atlasSphereLift normalizedAffineMap
  rw [atlasLift_raw_eq A q j x hx]

theorem atlasWeightedVector_normalized_coordinates (q : V → E) (x : H)
    (hx : 0 < atlasSelectedSum A x) :
    sphericalNormalize (∑ v ∈ A.selected, ((atlasSelectedSum A x)⁻¹*A.hat v x) • q v) =
      sphericalNormalize (atlasWeightedVector A q x) := by
  simp_rw [mul_smul]
  rw [← Finset.smul_sum]
  exact sphericalNormalize_pos_smul _ (inv_pos.mpr hx) _

theorem atlasWeightedVector_nonzero (q : V → E) (j : Idx) (x : H)
    (hx : x ∈ atlasRetractionDomain A) (hxj : x ∈ atlasCell A j)
    (c : E) (hc : ∀ v ∈ A.cells j ∩ A.selected, 0 < inner ℝ c (q v)) :
    atlasWeightedVector A q x ≠ 0 := by
  classical
  change x ∈ A.domain ∧ 0 < atlasSelectedSum A x at hx
  have hPos : ∃ v ∈ A.selected, 0 < A.hat v x := by
    by_contra h
    push_neg at h
    have hz : atlasSelectedSum A x ≤ 0 := Finset.sum_nonpos (fun v hv => h v hv)
    linarith
  obtain ⟨v,hv,hvp⟩ := hPos
  have hvc : v ∈ A.cells j := by
    by_contra h
    have hz := A.support_cell j x hxj v h
    linarith
  have hTerm : ∀ w ∈ A.selected, 0 ≤ A.hat w x*inner ℝ c (q w) := by
    intro w hw
    by_cases hwc : w ∈ A.cells j
    · exact mul_nonneg (A.nonneg x hx.1 w) (hc w (Finset.mem_inter.mpr ⟨hwc,hw⟩)).le
    · rw [A.support_cell j x hxj w hwc,zero_mul]
  have hp : 0 < ∑ w ∈ A.selected, A.hat w x*inner ℝ c (q w) :=
    Finset.sum_pos' hTerm ⟨v,hv,mul_pos hvp (hc v (Finset.mem_inter.mpr ⟨hvc,hv⟩))⟩
  intro hz
  have he : inner ℝ c (atlasWeightedVector A q x) =
      ∑ w ∈ A.selected, A.hat w x*inner ℝ c (q w) := by
    simp only [atlasWeightedVector,inner_sum,real_inner_smul_right]
  rw [hz,inner_zero_right] at he
  linarith

theorem atlasSphereLift_smooth (q : V → E) (j : Idx) (x : H)
    (hx : x ∈ atlasRetractionDomain A) (hxj : x ∈ atlasCell A j)
    (c : E) (hc : ∀ v ∈ A.cells j ∩ A.selected, 0 < inner ℝ c (q v)) (n : ℕ∞) :
    ContDiffAt ℝ n (atlasSphereLift A q j) x := by
  apply normalizedAffineMap_contDiffAt
  rw [atlasLift_raw_eq A q j x hxj]
  exact atlasWeightedVector_nonzero A q j x hx hxj c hc

end Paper28
