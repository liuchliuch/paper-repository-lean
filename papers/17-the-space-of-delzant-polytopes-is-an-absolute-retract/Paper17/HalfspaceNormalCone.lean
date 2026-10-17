import Paper17.HalfspaceGeometry

/-! Actual normal cones at simple intersections of supporting hyperplanes. -/
noncomputable section
open scoped BigOperators Topology
namespace Paper17
section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}

/-- Coefficients in any enumeration of a finite ray set describe the same
actual positive span. -/
theorem raySpan_iff_enumerated {E J : Type*} [AddCommGroup E] [Module ℝ E] [Fintype J]
    (v : ι → E) (s : Finset ι) (e : J ≃ ↑s) (x : E) :
    x ∈ raySpan v s ↔ ∃ c : J → ℝ, (∀ i, 0 ≤ c i) ∧ x = ∑ i, c i • v (e i).val := by
  classical
  constructor
  · rintro ⟨d, hd, hs, hx⟩
    refine ⟨fun i => d (e i).val, fun i => hd _, ?_⟩
    rw [hx, sum_supported_eq_subtype v s d hs]
    exact (Fintype.sum_equiv e _ _ (fun _ => rfl)).symm
  · rintro ⟨c, hc, hx⟩
    let d : ι → ℝ := fun i => if hi : i ∈ s then c (e.symm ⟨i, hi⟩) else 0
    have hd : ∀ i, 0 ≤ d i := by
      intro i
      dsimp [d]
      split_ifs
      · exact hc _
      · exact le_refl 0
    have hs : ∀ i, i ∉ s → d i = 0 := fun i hi => dif_neg hi
    refine ⟨d, hd, hs, ?_⟩
    rw [sum_supported_eq_subtype v s d hs, hx]
    exact Fintype.sum_equiv e _ _ (fun i => by simp [d, (e i).property])

/-- Linearity of the actual pairing over arbitrary finite weighted sums. -/
theorem dot_fintype_sum_smul {J : Type*} [Fintype J]
    (c : J → ℝ) (v : J → V n) (z : V n) :
    dot (∑ i, c i • v i) z = ∑ i, c i * dot (v i) z := by
  simp only [dot, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [mul_assoc]

/-- The square matrix of the actual active real normals. -/
def constraintMatrix (a : ι → V n) (s : Finset ι) (hs : s.card = n) :
    Matrix (Fin n) (Fin n) ℝ := fun i => a (cellEnumeration s hs i).val

/-- At an extreme point with exactly `n` active constraints the active
normal matrix really is nonsingular. -/
theorem extreme_constraintMatrix_det_ne_zero (a : ι → V n) (h : ι → ℝ)
    {x : V n} (hx : x ∈ (finiteHalfspaces a h).extremePoints ℝ)
    (hs : (activeConstraints a h x).card = n) :
    (constraintMatrix a (activeConstraints a h x) hs).det ≠ 0 := by
  let e := cellEnumeration (activeConstraints a h x) hs
  let M := constraintMatrix a (activeConstraints a h x) hs
  have hinj : Function.Injective M.mulVec := by
    intro v w heq
    apply extreme_activeEvaluation_injective a h hx
    funext i
    obtain ⟨j, rfl⟩ := e.surjective i
    exact congrFun heq j
  have hu : IsUnit M := Matrix.mulVec_injective_iff_isUnit.mp hinj
  exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det M).mp hu)

/-- The geometric normal cone for any actual convex carrier. -/
def carrierNormalCone (K : Set (V n)) (x : V n) : Set (V n) :=
  {u | ∀ y ∈ K, dot u y ≤ dot u x}

/-- A simple feasible point has exactly the positive span of its active
normals as its true normal cone. The reverse inclusion uses an actual small
feasible motion in a dual-basis direction, not an assumed Farkas certificate. -/
theorem normalCone_finiteHalfspaces (a : ι → V n) (h : ι → ℝ)
    {x : V n} (hx : x ∈ finiteHalfspaces a h)
    (hs : (activeConstraints a h x).card = n)
    (hdet : (constraintMatrix a (activeConstraints a h x) hs).det ≠ 0) :
    carrierNormalCone (finiteHalfspaces a h) x = raySpan a (activeConstraints a h x) := by
  classical
  let s := activeConstraints a h x
  let e := cellEnumeration s hs
  let M := constraintMatrix a s hs
  have hMu : IsUnit M := (Matrix.isUnit_iff_isUnit_det M).mpr (isUnit_iff_ne_zero.mpr hdet)
  ext u
  rw [raySpan_iff_enumerated a s e]
  constructor
  · intro hu
    obtain ⟨c, hc⟩ := Matrix.vecMul_surjective_iff_isUnit.mpr hMu u
    have hcoord : u = ∑ i, c i • a (e i).val := by
      ext j
      simpa only [Matrix.vecMul, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, M,
        constraintMatrix, e] using congrFun hc.symm j
    refine ⟨c, ?_, hcoord⟩
    intro k
    by_contra hck
    have hck' : c k < 0 := lt_of_not_ge hck
    obtain ⟨v, hv⟩ := Matrix.mulVec_surjective_iff_isUnit.mpr hMu (Pi.single k (-1))
    have hvnorm : ∀ i : Fin n, dot (a (e i).val) v = if i = k then -1 else 0 := by
      intro i
      have hh := congrFun hv i
      simpa only [Matrix.mulVec, dotProduct, M, constraintMatrix, e, Pi.single_apply] using hh
    obtain ⟨δ, hδ, hbound⟩ := finiteHalfspaces_small_motion a h hx v
    let t : ℝ := δ / 2
    have ht : 0 < t := div_pos hδ (by norm_num)
    have htd : |t| < δ := by rw [abs_of_pos ht]; dsimp [t]; linarith
    have hy : x + t • v ∈ finiteHalfspaces a h := by
      apply hbound t htd
      intro i hi
      obtain ⟨j, hj⟩ := e.surjective ⟨i, hi⟩
      have hij : (e j).val = i := congrArg Subtype.val hj
      rw [← hij, hvnorm]
      split_ifs <;> nlinarith
    have hdot : dot u v = -c k := by
      rw [hcoord]
      simp only [dot, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
      rw [Finset.sum_comm]
      have hh : (∑ i, ∑ j, c i * a (e i).val j * v j) =
          ∑ i, c i * dot (a (e i).val) v := by
        apply Finset.sum_congr rfl
        intro i _
        rw [dot, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      rw [hh]
      simp_rw [hvnorm]
      simp
    have hnormal := hu (x + t • v) hy
    rw [dot_add_right, dot_smul_right, hdot] at hnormal
    nlinarith [mul_pos ht (neg_pos.mpr hck')]
  · rintro ⟨c, hc, rfl⟩ y hy
    have hdot : ∀ z : V n, dot (∑ i, c i • a (e i).val) z =
        ∑ i, c i * dot (a (e i).val) z := by
      intro z
      simp only [dot, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [hdot, hdot]
    apply Finset.sum_le_sum
    intro i _
    have hactive := (mem_activeConstraints a h x (e i).val).mp (e i).property
    rw [hactive]
    exact mul_le_mul_of_nonneg_left (hy _) (hc i)

end
end Paper17
