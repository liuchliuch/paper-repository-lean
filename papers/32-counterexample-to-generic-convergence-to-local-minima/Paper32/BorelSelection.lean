import Paper32.FunctionClass
import Paper32.Selection
import Mathlib.Topology.Baire.Lemmas
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Analysis.Calculus.TangentCone

/-! Explicit Borel Clarke selections from a finite closed polyhedral cover.
An eligible affine piece at z is one whose open cell has z in its closure.
Eligibility is a closed condition. Scanning the fixed finite list of pieces
therefore gives a Borel map, and actual sequences inside the open cell prove
membership in the genuine reachable-gradient set.
-/

open Set Filter Topology MeasureTheory

noncomputable section
namespace Paper32

local instance (p : Prop) : Decidable p := Classical.propDecidable p

lemma IsPolyhedron.isClosed {s : Set Point} (hs : IsPolyhedron s) : IsClosed s := by
  rcases hs with ⟨n, a, rfl⟩
  have heq : {z | ∀ i, 0 ≤ (a i).eval z} = ⋂ i, {z | 0 ≤ (a i).eval z} := by
    ext z
    simp
  rw [heq]
  exact isClosed_iInter fun i => isClosed_le continuous_const (a i).continuous

lemma IsPolyhedron.convex {s : Set Point} (hs : IsPolyhedron s) : Convex ℝ s := by
  rcases hs with ⟨n, a, rfl⟩
  intro z hz w hw t u ht hu htu i
  have he : (a i).eval (t • z + u • w) = t * (a i).eval z + u * (a i).eval w := by
    simp only [AffineForm.eval, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
      Prod.smul_snd, smul_eq_mul]
    have hconst : t * (a i).c + u * (a i).c = (a i).c := by
      rw [← add_mul, htu, one_mul]
    nlinarith only [hconst]
  rw [he]
  exact add_nonneg (mul_nonneg ht (hz i)) (mul_nonneg hu (hw i))

lemma AffineForm.hasFDerivAt (a : AffineForm) (z : Point) :
    HasFDerivAt a.eval (linCLM (a.x, a.y)) z := by
  convert ((linCLM (a.x, a.y)).hasFDerivAt).add_const a.c using 1

/-- A closed eligibility set; lower-dimensional cells with empty interior
are automatically ineligible. -/
def eligibleCell (r : AffineRegion) : Set Point := closure (interior (regionCell r))

def regionGradient (r : AffineRegion) : Point := ((regionAffine r).x, (regionAffine r).y)

lemma eligibleCells_cover (z : Point) : ∃ r : AffineRegion, z ∈ eligibleCell r := by
  have hc : ∀ r, IsClosed (regionCell r) := fun r => (regionCell_polyhedron r).isClosed
  have hu : (⋃ r : AffineRegion, regionCell r) = univ := by
    ext q
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    exact regionCells_cover q
  have hd := dense_iUnion_interior_of_closed hc hu
  have hz : z ∈ closure (⋃ r : AffineRegion, interior (regionCell r)) := hd z
  rw [closure_iUnion_of_finite] at hz
  exact Set.mem_iUnion.mp hz

lemma F_hasFDerivAt_regionInterior {r : AffineRegion} {z : Point}
    (hz : z ∈ interior (regionCell r)) :
    HasFDerivAt F (linCLM (regionGradient r)) z := by
  have heq : F =ᶠ[𝓝 z] (regionAffine r).eval := by
    filter_upwards [isOpen_interior.mem_nhds hz] with q hq
    exact F_eq_regionAffine (interior_subset hq)
  exact ((regionAffine r).hasFDerivAt z).congr_of_eventuallyEq heq

/-- Eligibility supplies actual differentiability sequences with this constant gradient. -/
theorem regionGradient_reachable {r : AffineRegion} {z : Point} (hz : z ∈ eligibleCell r) :
    regionGradient r ∈ gradientLimits F z := by
  obtain ⟨a, ha, haz⟩ := mem_closure_iff_seq_limit.mp hz
  exact ⟨a, fun _ => regionGradient r, haz, tendsto_const_nhds,
    fun n => F_hasFDerivAt_regionInterior (ha n)⟩

private lemma point_eq_of_linCLM_eq {w u : Point} (h : linCLM w = linCLM u) : w = u := by
  apply Prod.ext
  · have hh := congrArg (fun L : Point →L[ℝ] ℝ => L (1,0)) h
    simpa [linCLM] using hh
  · have hh := congrArg (fun L : Point →L[ℝ] ℝ => L (0,1)) h
    simpa [linCLM] using hh

/-- At a differentiability point every eligible full-dimensional affine piece
has the actual differential, including when the point is on the cell boundary. -/
lemma gradient_eq_regionGradient {r : AffineRegion} {z w : Point}
    (hz : z ∈ eligibleCell r) (hd : HasFDerivAt F (linCLM w) z) :
    w = regionGradient r := by
  have hc := (regionCell_polyhedron r).isClosed
  have hzcell : z ∈ regionCell r := closure_minimal interior_subset hc hz
  have hne : (interior (regionCell r)).Nonempty := closure_nonempty_iff.mp ⟨z,hz⟩
  have hu := uniqueDiffWithinAt_convex (regionCell_polyhedron r).convex hne
    (closure_mono interior_subset hz)
  have hda : HasFDerivWithinAt F (linCLM (regionGradient r)) (regionCell r) z :=
    ((regionAffine r).hasFDerivAt z).hasFDerivWithinAt.congr'
      (fun q hq => F_eq_regionAffine hq) hzcell
  exact point_eq_of_linCLM_eq (hu.eq hd.hasFDerivWithinAt hda)

/-- The finite union of eligible coefficient graphs is closed. -/
private lemma isClosed_eligibleGradientGraph :
    IsClosed {p : Point × Point | ∃ r : AffineRegion,
      p.1 ∈ eligibleCell r ∧ p.2 = regionGradient r} := by
  have heq : {p : Point × Point | ∃ r : AffineRegion,
      p.1 ∈ eligibleCell r ∧ p.2 = regionGradient r} =
      ⋃ r : AffineRegion, eligibleCell r ×ˢ {regionGradient r} := by
    ext p
    simp
  rw [heq]
  exact isClosed_iUnion_of_finite fun r => isClosed_closure.prod isClosed_singleton

/-- Exact reachable-gradient formula derived from actual differentials and
sequences; the finite affine list is a conclusion, not the definition. -/
theorem gradientLimits_F_iff {z w : Point} : w ∈ gradientLimits F z ↔
    ∃ r : AffineRegion, z ∈ eligibleCell r ∧ w = regionGradient r := by
  constructor
  · rintro ⟨a,b,ha,hb,hd⟩
    apply isClosed_eligibleGradientGraph.mem_of_tendsto (ha.prodMk_nhds hb)
    apply Filter.Eventually.of_forall
    intro n
    obtain ⟨r,hr⟩ := eligibleCells_cover (a n)
    exact ⟨r,hr,gradient_eq_regionGradient hr (hd n)⟩
  · rintro ⟨r,hr,rfl⟩
    exact regionGradient_reachable hr

/-- Only a finite Boolean eligibility mask controls the entire Clarke value. -/
def eligibilityMask (z : Point) : Set AffineRegion := {r | z ∈ eligibleCell r}

lemma measurable_eligibilityMask : Measurable eligibilityMask := by
  apply measurable_set_iff.mpr
  intro r
  apply measurable_to_prop
  simpa only [Set.preimage_singleton_true] using
    (show MeasurableSet (eligibleCell r) from isClosed_closure.measurableSet)

lemma gradientLimits_F_eq_of_mask_eq {z u : Point} (h : eligibilityMask z = eligibilityMask u) :
    gradientLimits F z = gradientLimits F u := by
  have hm : ∀ r, z ∈ eligibleCell r ↔ u ∈ eligibleCell r := fun r =>
    Iff.of_eq (congrArg (fun m : Set AffineRegion => r ∈ m) h)
  ext w
  simp only [gradientLimits_F_iff, hm]

private def scanRegions : List AffineRegion → Point → Point
  | [], _ => 0
  | r :: rs, z => if z ∈ eligibleCell r then regionGradient r else scanRegions rs z

private theorem measurable_scanRegions (rs : List AffineRegion) : Measurable (scanRegions rs) := by
  induction rs with
  | nil => exact measurable_const
  | cons r rs ih =>
    exact Measurable.ite (show MeasurableSet (eligibleCell r) from isClosed_closure.measurableSet) measurable_const ih

private theorem scanRegions_mem (rs : List AffineRegion) (z : Point)
    (hz : ∃ r ∈ rs, z ∈ eligibleCell r) :
    ∃ r ∈ rs, z ∈ eligibleCell r ∧ scanRegions rs z = regionGradient r := by
  induction rs with
  | nil => simp at hz
  | cons r rs ih =>
    by_cases hr : z ∈ eligibleCell r
    · exact ⟨r, by simp, hr, by simp [scanRegions, hr]⟩
    · obtain ⟨q,hq,hzq⟩ := hz
      have hqr : q ∈ rs := by
        rcases List.mem_cons.mp hq with hq | hq
        · subst q
          exact False.elim (hr hzq)
        · exact hq
      obtain ⟨q,hq,hzq,heq⟩ := ih ⟨q,hqr,hzq⟩
      exact ⟨q, by simp [hq], hzq, by simpa [scanRegions, hr] using heq⟩

/-- A fixed finite-rule selection, with no dependence on time or sampled noise. -/
def borelClarkeSelection (v z : Point) : Point :=
  scanRegions Finset.univ.toList z - v

theorem measurable_borelClarkeSelection (v : Point) : Measurable (borelClarkeSelection v) :=
  (measurable_scanRegions _).sub measurable_const

theorem borelClarkeSelection_mem (v z : Point) :
    borelClarkeSelection v z ∈ clarkeSubdiff (tilt v) z := by
  have hz : ∃ r ∈ Finset.univ.toList, z ∈ eligibleCell r := by
    obtain ⟨r,hr⟩ := eligibleCells_cover z
    exact ⟨r, by simp, hr⟩
  obtain ⟨r,hr,hzr,heq⟩ := scanRegions_mem Finset.univ.toList z hz
  have hg := regionGradient_reachable hzr
  obtain ⟨a,b,ha,hb,hd⟩ := hg
  apply subset_closure
  apply subset_convexHull ℝ
  refine ⟨a,fun n => b n-v,ha,?_,?_⟩
  · simpa only [borelClarkeSelection, heq] using hb.sub_const v
  · intro n
    have he : linCLM (b n-v) = linCLM (b n) - linCLM v := by
      apply ContinuousLinearMap.ext
      intro q
      simp [linCLM]
      ring
    rw [he]
    exact (hd n).sub ((linCLM v).hasFDerivAt)

private lemma gradientLimits_sub_linear {f : Point → ℝ} {z w v : Point}
    (hw : w ∈ gradientLimits f z) :
    w-v ∈ gradientLimits (fun q => f q-lin v q) z := by
  obtain ⟨a,b,ha,hb,hd⟩ := hw
  refine ⟨a,fun n => b n-v,ha,hb.sub_const v,?_⟩
  intro n
  have he : linCLM (b n-v) = linCLM (b n) - linCLM v := by
    apply ContinuousLinearMap.ext
    intro q
    simp [linCLM]
    ring
  rw [he]
  exact (hd n).sub ((linCLM v).hasFDerivAt)

lemma gradientLimits_tilt_iff {v z w : Point} :
    w ∈ gradientLimits (tilt v) z ↔ w+v ∈ gradientLimits F z := by
  constructor
  · intro h
    have hh := gradientLimits_sub_linear (v := -v) h
    have heq : (fun q => tilt v q - lin (-v) q) = F := by
      funext q
      simp [tilt, lin]
      ring
    rw [heq] at hh
    simpa using hh
  · intro h
    have hh := gradientLimits_sub_linear (v := v) h
    simpa only [tilt, add_sub_cancel_right] using hh

lemma clarke_tilt_eq_of_mask_eq {v z u : Point} (h : eligibilityMask z = eligibilityMask u) :
    clarkeSubdiff (tilt v) z = clarkeSubdiff (tilt v) u := by
  have hg : gradientLimits (tilt v) z = gradientLimits (tilt v) u := by
    ext w
    simp only [gradientLimits_tilt_iff, gradientLimits_F_eq_of_mask_eq h]
  simp only [clarkeSubdiff, hg]

private def maskRepresentative (m : Set AffineRegion) : Point :=
  if hm : ∃ z : Point, eligibilityMask z = m then Classical.choose hm else 0

private lemma maskRepresentative_mask (z : Point) :
    eligibilityMask (maskRepresentative (eligibilityMask z)) = eligibilityMask z := by
  simp only [maskRepresentative, dif_pos (show ∃ u : Point, eligibilityMask u = eligibilityMask z from ⟨z,rfl⟩)]
  exact Classical.choose_spec (show ∃ u : Point, eligibilityMask u = eligibilityMask z from ⟨z,rfl⟩)

private lemma minimumNormSelection_maskRepresentative (v z : Point) :
    minimumNormSelection v (maskRepresentative (eligibilityMask z)) = minimumNormSelection v z := by
  have heq := clarke_tilt_eq_of_mask_eq (v := v) (maskRepresentative_mask z)
  apply minimumNormSelection_unique_norm v z
  · rw [← heq]
    exact minimumNormSelection_mem _ _
  · intro w hw
    apply minimumNormSelection_min_norm
    rwa [heq]

/-- The exact minimum-Euclidean-norm selection (2.11) is Borel measurable.
The proof factors it through the finite set of eligibility masks; it does not
assume any measurable-selection or quantifier-elimination theorem. -/
theorem measurable_minimumNormSelection (v : Point) : Measurable (minimumNormSelection v) := by
  have hm : Measurable (fun m : Set AffineRegion => minimumNormSelection v (maskRepresentative m)) :=
    measurable_of_finite _
  have hc := hm.comp measurable_eligibilityMask
  have heq : (fun z => minimumNormSelection v (maskRepresentative (eligibilityMask z))) =
      minimumNormSelection v := funext (minimumNormSelection_maskRepresentative v)
  change Measurable (fun z => minimumNormSelection v (maskRepresentative (eligibilityMask z))) at hc
  rwa [heq] at hc

end Paper32
