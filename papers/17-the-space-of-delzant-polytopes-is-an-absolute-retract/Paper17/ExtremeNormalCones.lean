import Paper17.RationalNormalCones
import Paper17.FanPresentation

/-! True extreme vertices and faces of smooth normal cones, allowing redundant
finite vertex presentations. -/
noncomputable section
open scoped BigOperators Topology
namespace Paper17

/-- The actual extreme vertices of a finite convex hull. -/
def Polytope.extremeVertices {n : ℕ} (P : Polytope n) : Finset (V n) := by
  classical
  exact P.verts.filter (fun v => v ∈ P.carrier.extremePoints ℝ)

theorem Polytope.coe_extremeVertices {n : ℕ} (P : Polytope n) :
    (P.extremeVertices : Set (V n)) = P.carrier.extremePoints ℝ := by
  classical
  ext v
  constructor
  · intro hv
    exact (Finset.mem_filter.mp hv).2
  · intro hv
    exact Finset.mem_filter.mpr ⟨extremePoints_convexHull_subset hv, hv⟩

theorem Polytope.convexHull_extremeVertices {n : ℕ} (P : Polytope n) :
    convexHull ℝ (P.extremeVertices : Set (V n)) = P.carrier := by
  have hc : IsClosed (convexHull ℝ (P.extremeVertices : Set (V n))) :=
    P.extremeVertices.finite_toSet.isCompact_convexHull.isClosed
  rw [← hc.closure_eq, P.coe_extremeVertices]
  exact closure_convexHull_extremePoints P.isCompact P.convex

/-- At every true extreme vertex of a polytope the actual normal cone has
interior, by strict separation from the hull of the remaining vertices. -/
theorem extreme_normalCone_interior {n : ℕ} (P : Polytope n) {v : V n}
    (hv : v ∈ P.carrier.extremePoints ℝ) :
    (interior (normalConeAt P v : Set (V n))).Nonempty := by
  classical
  let s := P.extremeVertices.erase v
  have hnot : v ∉ convexHull ℝ (s : Set (V n)) := by
    have hh := (P.convex.mem_extremePoints_iff_mem_diff_convexHull_diff.mp hv).2
    intro hc
    apply hh
    apply convexHull_mono _ hc
    intro y hy
    obtain ⟨hne, hym⟩ := Finset.mem_erase.mp hy
    have hyext : y ∈ P.carrier.extremePoints ℝ := by
      rw [← P.coe_extremeVertices]
      exact hym
    exact ⟨extremePoints_subset hyext, hne⟩
  obtain ⟨f, b, hfb, hbf⟩ := geometric_hahn_banach_closed_point
    (convex_convexHull ℝ (s : Set (V n))) s.finite_toSet.isCompact_convexHull.isClosed hnot
  obtain ⟨u, hu⟩ := exists_forall_eq_dot f.toLinearMap
  let U : Set (V n) := {w | ∀ y ∈ s, dot w y < dot w v}
  have hU : IsOpen U := by
    have hc : ∀ y : V n, Continuous (fun w : V n => dot w y) :=
      fun y => by simpa only [dot_comm] using continuous_dot y
    simpa only [U, Set.setOf_forall] using
      (isOpen_biInter_finset (s := s) (fun y _ => isOpen_lt (hc y) (hc v)))
  have huU : u ∈ U := by
    intro y hy
    rw [← hu y, ← hu v]
    exact (hfb y (subset_convexHull ℝ _ hy)).trans hbf
  have hsub : U ⊆ (normalConeAt P v : Set (V n)) := by
    intro w hw
    have hconv : Convex ℝ {y | dot w y ≤ dot w v} := by
      rw [convex_iff_add_mem]
      intro x hx y hy a b ha hb hab
      change dot w (a • x + b • y) ≤ dot w v
      rw [dot_add_right, dot_smul_right, dot_smul_right]
      calc a * dot w x + b * dot w y ≤ a * dot w v + b * dot w v :=
          add_le_add (mul_le_mul_of_nonneg_left hx ha) (mul_le_mul_of_nonneg_left hy hb)
        _ = dot w v := by rw [← add_mul, hab, one_mul]
    change ∀ y ∈ P.carrier, dot w y ≤ dot w v
    rw [← P.convexHull_extremeVertices]
    apply convexHull_min _ hconv
    intro y hy
    by_cases hyv : y = v
    · subst y
      show dot w v ≤ dot w v
      exact le_refl _
    · exact (hw y (Finset.mem_erase.mpr ⟨hyv, hy⟩)).le
  exact ⟨u, interior_mono hsub (by rwa [hU.interior_eq])⟩

/-- Every actual carrier point has its normal cone contained in a
full-dimensional normal cone of a true listed extreme vertex. -/
theorem exists_full_vertex_normalCone_superset {n : ℕ} (P : Polytope n) {v : V n}
    (hv : v ∈ P.carrier) :
    ∃ q ∈ P.verts, (interior (normalConeAt P q : Set (V n))).Nonempty ∧
      (normalConeAt P v : Set (V n)) ⊆ normalConeAt P q := by
  classical
  have hne : P.extremeVertices.Nonempty := by
    have hh : (convexHull ℝ (P.extremeVertices : Set (V n))).Nonempty := by
      rw [P.convexHull_extremeVertices]
      exact P.nonempty
    exact convexHull_nonempty_iff.mp hh
  let R : Polytope n := ⟨P.extremeVertices, hne⟩
  have hcar : R.carrier = P.carrier := P.convexHull_extremeVertices
  obtain ⟨q, hq, hsub⟩ := exists_vertex_normalCone_superset R (hcar.symm ▸ hv)
  have hqext : q ∈ P.carrier.extremePoints ℝ := by
    rw [← P.coe_extremeVertices]
    exact hq
  refine ⟨q, extremePoints_convexHull_subset hqext, extreme_normalCone_interior P hqext, ?_⟩
  intro u hu y hy
  exact hsub (by simpa only [normalConeAt, hcar] using hu) y (hcar.symm ▸ hy)

/-- Every normal cone of a Delzant polytope, even at a redundant carrier point,
is an actual coordinate face of an integral nonsingular basis cone. -/
theorem delzant_normalCone_basis_face {n : ℕ} (P : DelzantPolytope n) {v : V n}
    (hv : v ∈ P.carrier) :
    ∃ a : Fin n → Fin n → ℤ, ∃ I : Finset (Fin n),
      (Matrix.det (realRays a)) ≠ 0 ∧
      (normalConeAt P.val v : Set (V n)) = raySpan (realRays a) I := by
  classical
  obtain ⟨q, hq, hqi, hsub⟩ := exists_full_vertex_normalCone_superset P.val hv
  obtain ⟨u, hint, hdet, hcone⟩ := P.property.2 (normalConeAt P.val q)
    (Finset.mem_image.mpr ⟨q, hq, rfl⟩) hqi
  choose a ha using hint
  have hau : realRays a = u := by ext i j; exact (ha i j).symm
  let I : Finset (Fin n) := Finset.univ.filter (fun i => dot (u i) v = dot (u i) q)
  have hray : ∀ i, u i ∈ normalConeAt P.val q := by
    intro i
    change u i ∈ (normalConeAt P.val q : Set (V n))
    rw [hcone]
    refine ⟨Pi.single i 1, ?_, ?_⟩
    · intro j
      simp only [Pi.single_apply]
      split_ifs <;> norm_num
    · simp
  have hgap : ∀ i, 0 ≤ dot (u i) q - dot (u i) v :=
    fun i => sub_nonneg.mpr (hray i v hv)
  refine ⟨a, I, ?_, ?_⟩
  · rw [hau]
    intro hz
    rw [hz, abs_zero] at hdet
    norm_num at hdet
  · rw [hau]
    ext z
    constructor
    · intro hz
      obtain ⟨c, hc, hzc⟩ := (hcone ▸ hsub hz)
      have heq : dot z q = dot z v := le_antisymm
        (hz q (subset_convexHull ℝ _ hq)) (hsub hz v hv)
      have hsum : ∑ i, c i * (dot (u i) q - dot (u i) v) = 0 := by
        simp only [mul_sub, Finset.sum_sub_distrib]
        rw [← dot_fintype_sum_smul, ← dot_fintype_sum_smul, ← hzc, heq, sub_self]
      refine ⟨c, hc, ?_, hzc⟩
      intro i hi
      have hzprod := (Finset.sum_eq_zero_iff_of_nonneg
        (fun j _ => mul_nonneg (hc j) (hgap j))).mp hsum i (Finset.mem_univ _)
      apply (mul_eq_zero.mp hzprod).resolve_right
      intro he
      exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, (sub_eq_zero.mp he).symm⟩)
    · rintro ⟨c, hc, hs, rfl⟩ y hy
      rw [dot_fintype_sum_smul, dot_fintype_sum_smul]
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : i ∈ I
      · rw [(Finset.mem_filter.mp hi).2]
        exact mul_le_mul_of_nonneg_left (hray i y hy) (hc i)
      · rw [hs i hi, zero_mul, zero_mul]

end Paper17
