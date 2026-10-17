import Paper17.HeightStability
import Paper17.ProjectiveStellarStep

/-!
# Smooth projective refinements of bounded integral halfspace presentations

Generic outward offsets first produce a simple actual polytope. Compact
active-face stability proves refinement of the original carrier's normal
cones. The completed compatible, projectivity-preserving resolution then
produces an actual Delzant polytope with the same refinement guarantee.
-/
noncomputable section
open scoped BigOperators Topology
namespace Paper17
section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}

/-- An actual Delzant normal-fan refinement for a bounded integral halfspace
presentation. The bounding hypothesis is an explicit uniform containment for
nearby heights and will be supplied by redundant coordinate inequalities. -/
theorem exists_delzant_refinement_halfspaces (v : ι → Fin n → ℤ) (h : ι → ℝ)
    (B : Set (V n)) (hB : IsCompact B)
    (hbound : ∀ h' : ι → ℝ, dist h' h < 1 → finiteHalfspaces (realRays v) h' ⊆ B)
    (hne : (finiteHalfspaces (realRays v) h).Nonempty) :
    ∃ Q : DelzantPolytope n, ∀ C ∈ (NormalFan Q.val).cones,
      ∃ y ∈ finiteHalfspaces (realRays v) h,
        (C : Set (V n)) ⊆ carrierNormalCone (finiteHalfspaces (realRays v) h) y := by
  classical
  obtain ⟨δ, hδ, hstable⟩ := finiteHalfspaces_active_stability (realRays v) h B hB
  let η := min δ 1
  have hη : 0 < η := lt_min hδ zero_lt_one
  obtain ⟨h', hclose, hgen⟩ := exists_outward_generic_heights (realRays v) h η hη
  have hdist : dist h' h < η := by
    rw [dist_eq_norm, pi_norm_lt_iff hη]
    intro i
    change ‖h' i - h i‖ < η
    rw [Real.norm_eq_abs, abs_of_pos (sub_pos.mpr (hclose i).1)]
    linarith [(hclose i).2]
  have hsubset : finiteHalfspaces (realRays v) h' ⊆ B :=
    hbound h' (hdist.trans_le (min_le_right _ _))
  have hcompact : IsCompact (finiteHalfspaces (realRays v) h') :=
    hB.of_isClosed_subset (finiteHalfspaces_isClosed _ _) hsubset
  obtain ⟨z, hz⟩ := hne
  have hstrict : ∀ i, dot (realRays v i) z < h' i := fun i => (hz i).trans_lt (hclose i).1
  let R := halfspaceFacetSupportData v h' hgen hcompact z hstrict
  obtain ⟨Q, _, _, _, hrefine⟩ := R.exists_delzant_refining_support
  refine ⟨Q, ?_⟩
  intro C hC
  obtain ⟨s, hs, hCs⟩ := hrefine C hC
  obtain ⟨hcard, hdet, hfeas, hact, _⟩ := halfspaceFacet_spec (realRays v) h' hgen hs
  have hactive : ∀ i ∈ s, dot (realRays v i) (constraintVertex (realRays v) h' s) = h' i :=
    constraintVertex_solves (realRays v) h' s hcard hdet
  obtain ⟨y, hy, hys⟩ := hstable h' (hdist.trans_le (min_le_left _ _))
    _ (hsubset hfeas) hfeas s hactive
  exact ⟨y, hy, hCs.trans (raySpan_subset_carrierNormalCone (realRays v) h s hy hys)⟩

/-- Adjoin redundant coordinate bounding halfspaces with integral normals. -/
def coordinateAugmentedNormals (v : ι → Fin n → ℤ) : (ι ⊕ (Fin n × Bool)) → Fin n → ℤ
  | Sum.inl i => v i
  | Sum.inr (j, b) => if b then Pi.single j 1 else Pi.single j (-1)

def coordinateAugmentedHeights (h : ι → ℝ) (R : ℝ) : (ι ⊕ (Fin n × Bool)) → ℝ
  | Sum.inl i => h i
  | Sum.inr _ => R

/-- Coordinate augmentation preserves the actual carrier when the chosen
coordinate box already contains it. -/
theorem coordinateAugmented_carrier (v : ι → Fin n → ℤ) (h : ι → ℝ)
    (R : ℝ) (hR : 0 ≤ R) (hbound : ∀ x ∈ finiteHalfspaces (realRays v) h, ‖x‖ ≤ R) :
    finiteHalfspaces (realRays (coordinateAugmentedNormals v)) (coordinateAugmentedHeights h R) =
      finiteHalfspaces (realRays v) h := by
  ext x
  constructor
  · intro hx i
    exact hx (Sum.inl i)
  · intro hx j
    cases j with
    | inl i => exact hx i
    | inr p =>
      obtain ⟨i, b⟩ := p
      have hnorm := (pi_norm_le_iff_of_nonneg hR).mp (hbound x hx) i
      rw [Real.norm_eq_abs, abs_le] at hnorm
      cases b <;> simp [coordinateAugmentedNormals, coordinateAugmentedHeights, realRays, dot,
        Pi.single_apply] <;> linarith

/-- All nearby augmented halfspace intersections lie in one actual compact
coordinate box, independently of degeneracies or feasibility. -/
theorem coordinateAugmented_uniform_bound (v : ι → Fin n → ℤ) (h : ι → ℝ)
    (R : ℝ) (hR : 0 ≤ R) (h' : (ι ⊕ (Fin n × Bool)) → ℝ)
    (hh : dist h' (coordinateAugmentedHeights h R) < 1) :
    finiteHalfspaces (realRays (coordinateAugmentedNormals v)) h' ⊆
      Metric.closedBall (0 : V n) (R + 1) := by
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg (by linarith)]
  intro i
  have hplus : x i ≤ h' (Sum.inr (i, true)) := by
    simpa [coordinateAugmentedNormals, realRays, dot, Pi.single_apply] using hx (Sum.inr (i, true))
  have hminus : -x i ≤ h' (Sum.inr (i, false)) := by
    simpa [coordinateAugmentedNormals, realRays, dot, Pi.single_apply] using hx (Sum.inr (i, false))
  have hp : |h' (Sum.inr (i, true)) - R| < 1 := by
    simpa only [Real.dist_eq, coordinateAugmentedHeights] using
      (dist_le_pi_dist h' (coordinateAugmentedHeights h R) (Sum.inr (i, true))).trans_lt hh
  have hm : |h' (Sum.inr (i, false)) - R| < 1 := by
    simpa only [Real.dist_eq, coordinateAugmentedHeights] using
      (dist_le_pi_dist h' (coordinateAugmentedHeights h R) (Sum.inr (i, false))).trans_lt hh
  rw [Real.norm_eq_abs, abs_le]
  exact ⟨by linarith [le_abs_self (h' (Sum.inr (i, false)) - R)],
    by linarith [le_abs_self (h' (Sum.inr (i, true)) - R)]⟩

end
end Paper17
