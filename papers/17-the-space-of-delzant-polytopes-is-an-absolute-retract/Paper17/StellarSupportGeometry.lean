import Paper17.FacetSupportData

/-! Explicit dual-basis geometry of truncating a face in a supporting presentation. -/
noncomputable section
open scoped BigOperators Topology
namespace Paper17

theorem dot_sub_right {n : ℕ} (u x y : V n) : dot u (x - y) = dot u x - dot u y := by
  simp only [dot, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

namespace IntegralConeComplex
variable {n : ℕ} (K : IntegralConeComplex n)

theorem constraintMatrix_det_ne_zero (s : K.complex.facets) :
    (constraintMatrix (realRays K.rays) s.val (K.fullCard s.val s.property)).det ≠ 0 := by
  change ((cellMatrix K.rays s.val (K.fullCard s.val s.property)).map (fun z => (z : ℝ))).det ≠ 0
  rw [← Int.cast_det]
  exact_mod_cast cellMatrix_det_ne_zero K.rays s.val (K.fullCard s.val s.property)
    (K.complex.independent s.val s.property)

/-- The actual dual-basis direction to an incident facet normal. -/
def dualDirection (s : K.complex.facets) (k : K.index) : V n :=
  if hk : k ∈ s.val then
    (constraintMatrix (realRays K.rays) s.val (K.fullCard s.val s.property))⁻¹.mulVec
      (Pi.single ((cellEnumeration s.val (K.fullCard s.val s.property)).symm ⟨k, hk⟩) 1)
  else 0

theorem dualDirection_eval (s : K.complex.facets) (k : K.index) (hk : k ∈ s.val)
    (i : K.index) (hi : i ∈ s.val) :
    dot (realRays K.rays i) (K.dualDirection s k) = if i = k then 1 else 0 := by
  classical
  let e := cellEnumeration s.val (K.fullCard s.val s.property)
  let M := constraintMatrix (realRays K.rays) s.val (K.fullCard s.val s.property)
  have hsolve : M.mulVec (K.dualDirection s k) = Pi.single (e.symm ⟨k, hk⟩) 1 := by
    rw [dualDirection, dif_pos hk]
    change M.mulVec (M⁻¹.mulVec _) = _
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv M
      (isUnit_iff_ne_zero.mpr (K.constraintMatrix_det_ne_zero s)), Matrix.one_mulVec]
  have hh := congrFun hsolve (e.symm ⟨i, hi⟩)
  change dot (realRays K.rays (e (e.symm ⟨i, hi⟩)).val) (K.dualDirection s k) = _ at hh
  simp only [Equiv.apply_symm_apply, Pi.single_apply] at hh
  have heq : (e.symm ⟨i, hi⟩ = e.symm ⟨k, hk⟩) ↔ i = k := by
    constructor
    · intro h
      exact congrArg Subtype.val (e.symm.injective h)
    · intro h
      subst i
      rfl
  simpa only [heq] using hh

namespace FacetSupportData
variable {K : IntegralConeComplex n} (R : FacetSupportData K) (D : StellarData K)

/-- Supporting value of the new ray at the face to be truncated. -/
def faceHeight : ℝ := ∑ i, D.coefficients i * R.heights i

theorem faceHeight_bound (s : K.complex.facets) :
    dot (fun j => (D.ray j : ℝ)) (R.vertex s) ≤ R.faceHeight D := by
  rw [D.ray_eq, dot_fintype_sum_smul]
  exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (R.feasible s i) (D.nonneg i))

/-- Exactly the old vertices incident to the chosen face maximize the new ray. -/
theorem faceHeight_eq_iff (s : K.complex.facets) :
    dot (fun j => (D.ray j : ℝ)) (R.vertex s) = R.faceHeight D ↔ D.face ⊆ s.val := by
  classical
  constructor
  · intro heq
    have hz : ∑ i, D.coefficients i * (R.heights i - dot (realRays K.rays i) (R.vertex s)) = 0 := by
      simp only [mul_sub, Finset.sum_sub_distrib]
      rw [← dot_fintype_sum_smul, ← D.ray_eq, heq]
      simp only [faceHeight, sub_self]
    have hnonneg : ∀ i, 0 ≤ D.coefficients i * (R.heights i - dot (realRays K.rays i) (R.vertex s)) :=
      fun i => mul_nonneg (D.nonneg i) (sub_nonneg.mpr (R.feasible s i))
    intro i hi
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hnonneg j)).mp hz i (Finset.mem_univ i)
    have hgap := (mul_eq_zero.mp hterm).resolve_left (D.positive i hi).ne'
    exact (R.active s i).mp (sub_eq_zero.mp hgap).symm
  · intro hIs
    rw [D.ray_eq, dot_fintype_sum_smul]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i ∈ D.face
    · rw [(R.active s i).mpr (hIs hi)]
    · simp [D.supported i hi]

theorem faceHeight_interior_lt :
    dot (fun j => (D.ray j : ℝ)) R.interiorPoint < R.faceHeight D := by
  have hnonneg : ∀ i, 0 ≤ D.coefficients i *
      (R.heights i - dot (realRays K.rays i) R.interiorPoint) :=
    fun i => mul_nonneg (D.nonneg i) (sub_pos.mpr (R.strictInterior i)).le
  have hpos : 0 < ∑ i, D.coefficients i *
      (R.heights i - dot (realRays K.rays i) R.interiorPoint) := by
    apply Finset.sum_pos' (fun i _ => hnonneg i)
    obtain ⟨i, hi⟩ := D.face_nonempty
    exact ⟨i, Finset.mem_univ _, mul_pos (D.positive i hi) (sub_pos.mpr (R.strictInterior i))⟩
  simp only [mul_sub, Finset.sum_sub_distrib] at hpos
  rw [← dot_fintype_sum_smul, ← D.ray_eq] at hpos
  exact sub_pos.mp hpos

/-- Pairing the new ray with the actual old dual-basis direction extracts
its corresponding positive coefficient. -/
theorem faceRay_dualDirection (s : K.complex.facets) (hIs : D.face ⊆ s.val)
    (k : K.index) (hk : k ∈ D.face) :
    dot (fun j => (D.ray j : ℝ)) (K.dualDirection s k) = D.coefficients k := by
  classical
  rw [D.ray_eq, dot_fintype_sum_smul]
  have hterm : ∀ i, D.coefficients i * dot (realRays K.rays i) (K.dualDirection s k) =
      if i = k then D.coefficients k else 0 := by
    intro i
    by_cases hik : i = k
    · subst i
      rw [K.dualDirection_eval s k (hIs hk) k (hIs hk), if_pos rfl, mul_one, if_pos rfl]
    · by_cases hi : i ∈ s.val
      · rw [K.dualDirection_eval s k (hIs hk) i hi, if_neg hik, mul_zero, if_neg hik]
      · have hiI : i ∉ D.face := fun h => hi (hIs h)
        simp only [D.supported i hiI, zero_mul, if_neg hik]
  simp_rw [hterm]
  simp

/-- Explicit vertex of a small truncation, along an actual dual-basis edge
at the original vertex. -/
def truncationVertex (s : K.complex.facets) (k : K.index) (ε : ℝ) : V n :=
  R.vertex s - (ε / D.coefficients k) • K.dualDirection s k

theorem continuous_truncationVertex (s : K.complex.facets) (k : K.index) :
    Continuous (R.truncationVertex D s k) :=
  continuous_const.sub ((continuous_id.div_const _).smul continuous_const)

@[simp] theorem truncationVertex_zero (s : K.complex.facets) (k : K.index) :
    R.truncationVertex D s k 0 = R.vertex s := by simp [truncationVertex]

theorem truncationVertex_old_pairing (s : K.complex.facets) (hIs : D.face ⊆ s.val)
    (k : K.index) (hk : k ∈ D.face) (i : K.index) (hi : i ∈ s.val) (ε : ℝ) :
    dot (realRays K.rays i) (R.truncationVertex D s k ε) =
      R.heights i - (ε / D.coefficients k) * (if i = k then 1 else 0) := by
  rw [truncationVertex, dot_sub_right, dot_smul_right, (R.active s i).mpr hi,
    K.dualDirection_eval s k (hIs hk) i hi]

theorem truncationVertex_new_pairing (s : K.complex.facets) (hIs : D.face ⊆ s.val)
    (k : K.index) (hk : k ∈ D.face) (ε : ℝ) :
    dot (fun j => (D.ray j : ℝ)) (R.truncationVertex D s k ε) = R.faceHeight D - ε := by
  rw [truncationVertex, dot_sub_right, dot_smul_right, (R.faceHeight_eq_iff D s).mpr hIs,
    faceRay_dualDirection D s hIs k hk, div_mul_cancel₀ _ (D.positive k hk).ne']

end FacetSupportData
end IntegralConeComplex
end Paper17
