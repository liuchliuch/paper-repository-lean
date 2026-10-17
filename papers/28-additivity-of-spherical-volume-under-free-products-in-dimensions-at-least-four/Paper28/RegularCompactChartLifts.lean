import Paper28.RegularChartClosed

/-! Compact lifted pieces of compact quotient sets in a small regular sphere
chart. The restricted quotient map is proved proper by closedness and finite
fibers, so compact chart lifts are not an external approximation assumption. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Metric
variable {G : Type*} [Group G] [DecidableEq G]

def regularChartMap (c : RegularSphere G) (r : ℝ) : closedBall c r → RegularOrbitQuotient G :=
  fun u => regularQuotientMap u.val

theorem regularChartMap_finite_fibers (c : RegularSphere G) (r : ℝ) (hr : r < 1/2)
    (q : RegularOrbitQuotient G) : (regularChartMap c r ⁻¹' {q}).Finite := by
  classical
  by_cases hx : (regularChartMap c r ⁻¹' {q}).Nonempty
  · obtain ⟨x,hx⟩ := hx
    change regularQuotientMap x.val = q at hx
    let F := {γ : G | dist c.val (leftRegular γ c.val) < 1}
    have hF : F.Finite := regular_near_translates_finite c.val c.val c.property c.property
    let S := (fun γ : G => γ • x.val) '' F
    have hS : S.Finite := hF.image _
    have hf : ((Subtype.val : closedBall c r → RegularSphere G) ⁻¹' S).Finite :=
      Set.Finite.preimage (fun a _ b _ h => Subtype.ext h) hS
    apply hf.subset
    intro y hy
    change regularQuotientMap y.val = q at hy
    have hrel : MulAction.orbitRel G (RegularSphere G) y.val x.val :=
      Quotient.exact (hy.trans hx.symm)
    obtain ⟨γ,hγ⟩ := hrel
    have hi : dist y.val (γ • c) = dist x.val c := by
      rw [← hγ]
      exact (isometry_smul (RegularSphere G) γ).dist_eq x.val c
    have hcy : dist c y.val ≤ r := by simpa only [mem_closedBall,dist_comm] using y.property
    have hxc : dist x.val c ≤ r := x.property
    have ht := dist_triangle c y.val (γ • c)
    rw [hi] at ht
    have hNear : γ ∈ F := by
      change dist c (γ • c) < 1
      linarith
    exact ⟨γ,hNear,hγ⟩
  · have he : regularChartMap c r ⁻¹' {q} = ∅ := Set.not_nonempty_iff_eq_empty.mp hx
    rw [he]
    exact Set.finite_empty

theorem regularChartMap_isClosedMap (c : RegularSphere G) (r : ℝ) (hr : r < 1) :
    IsClosedMap (regularChartMap c r) := by
  intro A hA
  have hS : IsClosed (Subtype.val '' A : Set (RegularSphere G)) :=
    isClosed_closedBall.isClosedEmbedding_subtypeVal.isClosedMap A hA
  have hb : (Subtype.val '' A : Set (RegularSphere G)) ⊆ closedBall c r := by
    rintro y ⟨x,_,rfl⟩
    exact x.property
  have h := regular_quotient_closed_image c r hr (Subtype.val '' A) hS hb
  simpa only [Set.image_image,Function.comp_def,regularChartMap] using h

theorem regularChartMap_proper (c : RegularSphere G) (r : ℝ) (hr : r < 1/2) :
    IsProperMap (regularChartMap c r) := by
  apply isProperMap_iff_isClosedMap_and_compact_fibers.mpr
  refine ⟨regularQuotientMap_continuous.comp continuous_subtype_val,
    regularChartMap_isClosedMap c r (by linarith),?_⟩
  intro q
  exact (regularChartMap_finite_fibers c r hr q).isCompact

/-- The lifted compact chart piece used to choose the finite-coordinate
projection in Lemma 5.1 is genuinely compact in the actual Hilbert sphere. -/
theorem regular_compact_chart_lift (c : RegularSphere G) (r : ℝ) (hr : r < 1/2)
    (K : Set (RegularOrbitQuotient G)) (hK : IsCompact K) :
    IsCompact {u : RegularSphere G | u ∈ closedBall c r ∧ regularQuotientMap u ∈ K} := by
  have h := ((regularChartMap_proper c r hr).isCompact_preimage hK).image continuous_subtype_val
  convert h using 1
  ext u
  simp only [Set.mem_setOf_eq,Set.mem_image,Set.mem_preimage,regularChartMap]
  exact ⟨fun hu => ⟨⟨u,hu.1⟩,hu.2,rfl⟩,fun ⟨x,hx,he⟩ => he ▸ ⟨x.property,hx⟩⟩

end Paper28
