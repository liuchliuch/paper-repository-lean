import Paper17.TruncationRadius

/-!
# Actual polytopal realization of a simultaneous stellar subdivision

The new inequality is a face truncation. Explicit dual-basis vertices satisfy
all old and new inequalities, and their exact active sets are the stellar
maximal cells. Supporting data and hence a genuine polytope are constructed.
-/
noncomputable section
open scoped BigOperators
namespace Paper17.IntegralConeComplex.FacetSupportData
variable {n : ℕ} {K : IntegralConeComplex n}
variable (R : FacetSupportData K) (D : StellarData K)

def starHeights (ε : ℝ) : Option K.index → ℝ
  | none => R.faceHeight D - ε
  | some i => R.heights i

def starVertexFor (ε : ℝ) (s : K.complex.facets) : Option K.index → V n
  | none => R.vertex s
  | some k => R.truncationVertex D s k ε

/-- The explicit points have precisely the new active hyperplanes, and all
other inequalities remain strict at a sufficiently small actual cut size. -/
theorem starVertexFor_spec (T : TruncationRadius R D) (s : K.complex.facets)
    (q : Option K.index) (hq : starCellValid D.face s.val q) (j : Option K.index) :
    dot (realRays (starRays K.rays D.ray) j) (R.starVertexFor D T.value s q) ≤ R.starHeights D T.value j ∧
      (dot (realRays (starRays K.rays D.ray) j) (R.starVertexFor D T.value s q) =
        R.starHeights D T.value j ↔ j ∈ starCellGenerators s.val q) := by
  classical
  cases q with
  | none =>
    cases j with
    | none =>
      change dot (fun i => (D.ray i : ℝ)) (R.vertex s) ≤ R.faceHeight D - T.value ∧ _
      have hstrict := T.unaffected s hq
      exact ⟨hstrict.le, iff_of_false hstrict.ne (by simp [starCellGenerators])⟩
    | some i =>
      change dot (realRays K.rays i) (R.vertex s) ≤ R.heights i ∧ _
      refine ⟨R.feasible s i, ?_⟩
      simpa [starCellGenerators] using R.active s i
  | some k =>
    have hIs : D.face ⊆ s.val := hq.1
    have hk : k ∈ D.face := hq.2
    cases j with
    | none =>
      change dot (fun i => (D.ray i : ℝ)) (R.truncationVertex D s k T.value) ≤ R.faceHeight D - T.value ∧ _
      have heq := R.truncationVertex_new_pairing D s hIs k hk T.value
      exact ⟨heq.le, iff_of_true heq (mem_starFacet_none s.val k)⟩
    | some i =>
      change dot (realRays K.rays i) (R.truncationVertex D s k T.value) ≤ R.heights i ∧ _
      by_cases hi : i ∈ s.val
      · have heq := R.truncationVertex_old_pairing D s hIs k hk i hi T.value
        by_cases hik : i = k
        · have hstrict : dot (realRays K.rays i) (R.truncationVertex D s k T.value) < R.heights i := by
            rw [heq, if_pos hik, mul_one]
            exact sub_lt_self _ (div_pos T.positive (D.positive k hk))
          exact ⟨hstrict.le, iff_of_false hstrict.ne (by simp [starCellGenerators, hik])⟩
        · have heq' : dot (realRays K.rays i) (R.truncationVertex D s k T.value) = R.heights i := by
            simpa only [if_neg hik, mul_zero, sub_zero] using heq
          exact ⟨heq'.le, iff_of_true heq' ((mem_starFacet_some s.val k i).mpr ⟨hi, hik⟩)⟩
      · have hstrict := T.inactive s k i hIs hk hi
        exact ⟨hstrict.le, iff_of_false hstrict.ne (by simp [starCellGenerators, hi])⟩

/-- Construct all supporting points and heights for the global stellar
complex from the actual face truncation. -/
def afterTruncation (T : TruncationRadius R D) : FacetSupportData D.result := by
  classical
  have horigin : ∀ s : D.result.complex.facets,
      ∃ t : K.complex.facets, ∃ q : Option K.index,
        starCellValid D.face t.val q ∧ starCellGenerators t.val q = s.val := by
    intro s
    obtain ⟨t, ht, q, hq, heq⟩ := (K.complex.mem_starFacets D.face s.val).mp s.property
    exact ⟨⟨t, ht⟩, q, hq, heq⟩
  choose t q hvalid heq using horigin
  exact {
    heights := R.starHeights D T.value
    vertex := fun s => R.starVertexFor D T.value (t s) (q s)
    feasible := by
      intro s j
      exact (R.starVertexFor_spec D T (t s) (q s) (hvalid s) j).1
    active := by
      intro s j
      have hh := (R.starVertexFor_spec D T (t s) (q s) (hvalid s) j).2
      simpa only [heq s] using hh
    interiorPoint := R.interiorPoint
    strictInterior := by
      intro j
      cases j with
      | none => exact T.interior
      | some i => exact R.strictInterior i
    complete := D.support_eq.trans R.complete }

include R in
/-- Polytopal supporting realizations are genuinely preserved by each
admissible lattice stellar step. -/
theorem supporting_realization_preserved : Nonempty (FacetSupportData D.result) := by
  let T := Classical.choice (truncationRadius_nonempty R D)
  exact ⟨R.afterTruncation D T⟩

include R in
/-- The completed compatible terminating resolution retains actual supporting
realizations. No projective-resolution conclusion was added as a premise. -/
theorem exists_smooth_realized_refinement :
    ∃ L : IntegralConeComplex n,
      (∀ s ∈ L.complex.facets, coneMultiplicity L.rays s = 1) ∧
      L.support = K.support ∧ L.Refines K ∧ Nonempty (FacetSupportData L) := by
  apply exists_smooth_refinement_preserving (fun L => Nonempty (FacetSupportData L)) ?_ K ⟨R⟩
  intro J E hJ
  obtain ⟨RJ⟩ := hJ
  exact RJ.supporting_realization_preserved E

include R in
/-- A genuine Delzant polytope is produced from concrete polytopal supporting
data, by the terminating compatible stellar resolution. -/
theorem exists_delzant_refining_support :
    ∃ Q : DelzantPolytope n, ∃ L : IntegralConeComplex n,
      Nonempty (FacetSupportData L) ∧ L.Refines K ∧
      ∀ C ∈ (NormalFan Q.val).cones, ∃ s ∈ K.complex.facets, (C : Set (V n)) ⊆ raySpan (realRays K.rays) s := by
  classical
  obtain ⟨L, hm, _, hLK, ⟨RL⟩⟩ := R.exists_smooth_realized_refinement
  let Q : DelzantPolytope n := ⟨RL.polytope, RL.isDelzant hm⟩
  refine ⟨Q, L, ⟨RL⟩, hLK, ?_⟩
  intro C hC
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hC
  obtain ⟨s, _, rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨t, ht, hst⟩ := hLK s.val s.property
  refine ⟨t, ht, ?_⟩
  rw [RL.normalCone_eq s]
  exact hst

end Paper17.IntegralConeComplex.FacetSupportData
