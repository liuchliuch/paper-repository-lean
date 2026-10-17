import Paper27.Geometry.BranchGraphs
import Paper27.Geometry.CyclicModel
import Mathlib.Topology.Maps.Proper.Basic

/-!
# Finite analytic germs with one smooth branch graph

The own argument here first identifies all the branch graphs at one fixed
source point, then uses their actual normalization cover to put the critical
image in that single graph. This implication is not an external input.

The separate classical input classifies finite analytic covers of a bidisc
whose branch locus is contained in one smooth graph. The punctured bidisc
has fundamental group `ℤ`; connected finite covers are cyclic, and the normal
finite extension is unique. Sources: SGA 1, Exposé XII, Proposition 5.3 and
Theorem 5.4, pp. 254–255, https://arxiv.org/pdf/math/0206203 ; Edixhoven,
de Jong, and Schepers, *Covers of surfaces with fixed branch locus*,
International Journal of Mathematics 21 (2010), 859–874, Lemma 2.1 proof,
preprint p. 3, https://arxiv.org/pdf/0807.0184 . The input below states only
this general local classification, with actual maps and actual sets. It does
not mention compact ramification components, normal bundles, retractions,
global group actions, or a bound on fibrations.
-/

noncomputable section

open scoped Topology
open Filter

namespace Paper27.Geometry.FiniteAnalyticGerm

/-- A bidisc after the actual target change `(x,v) ↦ (x,v-φ(x))`. -/
def graphBidisc (φ : ℂ → ℂ) (a : ℂ) (r s : ℝ) : Set (ℂ × ℂ) :=
  {z | ‖z.1 - a‖ < r ∧ ‖z.2 - φ z.1‖ < s}

/-- An actual analytic representative before any assertion about the
critical image. In particular, this record does not assume a cyclic model. -/
structure GraphNeighbourhood (F G : ℂ × ℂ → ℂ) (p : ℂ × ℂ) (φ : ℂ → ℂ) where
  source : Set (ℂ × ℂ)
  open_source : IsOpen source
  connected_source : IsConnected source
  centre_mem : p ∈ source
  radius : ℝ
  radius_positive : 0 < radius
  thickness : ℝ
  thickness_positive : 0 < thickness
  first_analytic : AnalyticOnNhd ℂ F source
  second_analytic : AnalyticOnNhd ℂ G source
  graph_analytic : AnalyticOnNhd ℂ φ (Metric.ball (F p) radius)
  graph_centre : φ (F p) = G p
  maps_target : ∀ q ∈ source, (F q, G q) ∈ graphBidisc φ (F p) radius thickness

namespace GraphNeighbourhood

variable {F G : ℂ × ℂ → ℂ} {p : ℂ × ℂ} {φ : ℂ → ℂ}

/-- The induced map uses the actual pair and the actual source and target
subspaces; properness and surjectivity below concern precisely this map. -/
def pairMap (A : GraphNeighbourhood F G p φ) :
    A.source → graphBidisc φ (F p) A.radius A.thickness :=
  fun q => ⟨(F q.val, G q.val), A.maps_target q.val q.property⟩

@[simp] theorem pairMap_val (A : GraphNeighbourhood F G p φ) (q : A.source) :
    (A.pairMap q).val = (F q.val, G q.val) := rfl

theorem first_in_ball (A : GraphNeighbourhood F G p φ) {q : ℂ × ℂ}
    (hq : q ∈ A.source) : F q ∈ Metric.ball (F p) A.radius := by
  simpa only [Metric.mem_ball, dist_eq_norm] using (A.maps_target q hq).1

end GraphNeighbourhood

/-- Raw proper finite-map data of an isolated source germ. All fields are
actual topological or analytic properties. The punctured source is the
complement of the actual inverse image of the graph. -/
structure FiniteGermData (F G : ℂ × ℂ → ℂ) (p : ℂ × ℂ) (φ : ℂ → ℂ)
    extends GraphNeighbourhood F G p φ where
  proper : IsProperMap toGraphNeighbourhood.pairMap
  surjective : Function.Surjective toGraphNeighbourhood.pairMap
  finite_fibres : ∀ y : graphBidisc φ (F p) radius thickness,
    (toGraphNeighbourhood.pairMap ⁻¹' {y}).Finite
  centre_fibre : {q | q ∈ source ∧ (F q, G q) = (F p, G p)} = {p}
  punctured_connected : IsConnected {q | q ∈ source ∧ G q ≠ φ (F q)}

/-- The single-graph condition is added only after the own branch argument. -/
structure FiniteGraphGerm (F G : ℂ × ℂ → ℂ) (p : ℂ × ℂ) (φ : ℂ → ℂ)
    extends FiniteGermData F G p φ where
  critical_image : ∀ q ∈ source,
    ¬ Function.Surjective (fderiv ℂ (fun z => (F z, G z)) q) → G q = φ (F q)

/-- Universal finite analytic cover classification over a smooth graph.
The only conclusion is an actual local cyclic coordinate identity, with
positive covering index as built into `CyclicNormalForm`. The equality of
graph functions specifies which smooth target divisor is being used. -/
def SmoothBranchFiniteCoverClassification : Prop :=
  ∀ (F G : ℂ × ℂ → ℂ) (p : ℂ × ℂ) (φ : ℂ → ℂ),
    FiniteGraphGerm F G p φ →
      ∃ B : CyclicModel.CyclicNormalForm F G p, B.graph = φ

/-- A finite collection of actual normalization branches at the one source
point, together with the cover of the actual critical locus by those branch
images. Graph identities are separate raw identities on those images. -/
structure FiniteBranchCover (F G : ℂ × ℂ → ℂ) (p : ℂ × ℂ)
    (ι : Type*) [Fintype ι] where
  region : Set (ℂ × ℂ)
  open_region : IsOpen region
  centre_mem : p ∈ region
  branches : ι → BranchGraphs.NormalizedBranchGraph F G p
  branch_domain : ι → Set ℂ
  critical_cover : ∀ q ∈ region,
    ¬ Function.Surjective (fderiv ℂ (fun z => (F z, G z)) q) →
      ∃ i t, t ∈ branch_domain i ∧ (branches i).normalization t = q
  branch_identity : ∀ i t, t ∈ branch_domain i →
    G ((branches i).normalization t) =
      (branches i).graph (F ((branches i).normalization t))

namespace FiniteBranchCover

variable {F G : ℂ × ℂ → ℂ} {p : ℂ × ℂ} {ι : Type*} [Fintype ι]

/-- Identifying all graph germs at this source point, followed by the actual
finite normalization cover, puts every nearby critical image in one graph. -/
theorem single_graph_neighbourhood (C : FiniteBranchCover F G p ι)
    (rigidity : BranchGraphs.IsometryFirstJetRigidity)
    (hF : AnalyticAt ℂ F p) (hG : AnalyticAt ℂ G p)
    (hsurj : Function.Surjective (fderiv ℂ F p)) (i₀ : ι) :
    ∃ U : Set ℂ, IsOpen U ∧ F p ∈ U ∧
      ∀ q ∈ C.region, F q ∈ U →
        ¬ Function.Surjective (fderiv ℂ (fun z => (F z, G z)) q) →
          G q = (C.branches i₀).graph (F q) := by
  obtain ⟨U, hU, hp, heq⟩ :=
    BranchGraphs.finite_branches_common_graph_neighbourhood rigidity hF hG hsurj C.branches i₀
  refine ⟨U, hU, hp, ?_⟩
  intro q hq hFq hcrit
  obtain ⟨i, t, ht, hν⟩ := C.critical_cover q hq hcrit
  have hid := C.branch_identity i t ht
  rw [hν] at hid
  exact hid.trans (heq (F q) hFq i)

/-- A genuine target radius can be chosen for all branches simultaneously.
The chosen graph is analytic on that whole disc. -/
theorem single_graph_radius (C : FiniteBranchCover F G p ι)
    (rigidity : BranchGraphs.IsometryFirstJetRigidity)
    (hF : AnalyticAt ℂ F p) (hG : AnalyticAt ℂ G p)
    (hsurj : Function.Surjective (fderiv ℂ F p)) (i₀ : ι) :
    ∃ r : ℝ, 0 < r ∧
      AnalyticOnNhd ℂ (C.branches i₀).graph.toFun (Metric.ball (F p) r) ∧
      ∀ q ∈ C.region, ‖F q - F p‖ < r →
        ¬ Function.Surjective (fderiv ℂ (fun z => (F z, G z)) q) →
          G q = (C.branches i₀).graph (F q) := by
  obtain ⟨U, hU, hp, hsingle⟩ := C.single_graph_neighbourhood rigidity hF hG hsurj i₀
  have hV := hU.inter (C.branches i₀).graph.open_domain
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hV (F p)
    ⟨hp, (C.branches i₀).graph.centre_mem⟩
  refine ⟨r, hr, ?_, ?_⟩
  · exact (C.branches i₀).graph.analytic.mono (fun z hz => (hball hz).2)
  · intro q hq hnorm hcrit
    apply hsingle q hq ((hball ?_).1) hcrit
    simpa only [Metric.mem_ball, dist_eq_norm] using hnorm

/-- Once a raw finite representative has been restricted to the common
target disc, its critical-single-graph condition follows from the actual
branch cover. No such condition is assumed of the raw representative. -/
def toFiniteGraphGerm (C : FiniteBranchCover F G p ι) (i₀ : ι)
    (r : ℝ)
    (hsingle : ∀ q ∈ C.region, ‖F q - F p‖ < r →
      ¬ Function.Surjective (fderiv ℂ (fun z => (F z, G z)) q) →
        G q = (C.branches i₀).graph (F q))
    (A : FiniteGermData F G p (C.branches i₀).graph.toFun)
    (hsmall : A.radius ≤ r) (hsource : A.source ⊆ C.region) :
    FiniteGraphGerm F G p (C.branches i₀).graph.toFun where
  toFiniteGermData := A
  critical_image := by
    intro q hq hcrit
    exact hsingle q (hsource hq) (lt_of_lt_of_le (A.maps_target q hq).1 hsmall) hcrit

/-- Own branch uniqueness and cover data feed the universal cover
classification. The representative is raw finite analytic data: the
single-graph critical-image hypothesis is proved in this theorem. -/
theorem classify (C : FiniteBranchCover F G p ι)
    (rigidity : BranchGraphs.IsometryFirstJetRigidity)
    (classification : SmoothBranchFiniteCoverClassification)
    (hF : AnalyticAt ℂ F p) (hG : AnalyticAt ℂ G p)
    (hsurj : Function.Surjective (fderiv ℂ F p)) (i₀ : ι) :
    ∃ r : ℝ, 0 < r ∧
      ∀ A : FiniteGermData F G p (C.branches i₀).graph.toFun,
        A.radius ≤ r → A.source ⊆ C.region →
          ∃ B : CyclicModel.CyclicNormalForm F G p,
            B.graph = (C.branches i₀).graph.toFun := by
  obtain ⟨r, hr, _hanalytic, hsingle⟩ := C.single_graph_radius rigidity hF hG hsurj i₀
  refine ⟨r, hr, ?_⟩
  intro A hsmall hsource
  exact classification F G p _ (C.toFiniteGraphGerm i₀ r hsingle A hsmall hsource)

/-- Reading the classified model gives the actual differential conclusions
at a critical point. The exponent bound, smooth normal curve, and both
unramified projection restrictions are proved by `CyclicModel`, rather than
being part of the classification interface. -/
theorem classify_ramified (C : FiniteBranchCover F G p ι)
    (rigidity : BranchGraphs.IsometryFirstJetRigidity)
    (classification : SmoothBranchFiniteCoverClassification)
    (hF : AnalyticAt ℂ F p) (hG : AnalyticAt ℂ G p)
    (hsurj : Function.Surjective (fderiv ℂ F p)) (i₀ : ι)
    (hp : ¬ Function.Surjective (fderiv ℂ (fun z => (F z, G z)) p))
    (hsecond : Function.Surjective (fderiv ℂ G p)) :
    ∃ r : ℝ, 0 < r ∧
      ∀ A : FiniteGermData F G p (C.branches i₀).graph.toFun,
        A.radius ≤ r → A.source ⊆ C.region →
          ∃ B : CyclicModel.CyclicNormalForm F G p,
            B.graph = (C.branches i₀).graph.toFun ∧ 2 ≤ B.exponent ∧
            deriv B.normalCurve B.centre_x ≠ 0 ∧
            deriv (F ∘ B.normalCurve) B.centre_x ≠ 0 ∧
            deriv (G ∘ B.normalCurve) B.centre_x ≠ 0 := by
  obtain ⟨r, hr, hclassify⟩ := C.classify rigidity classification hF hG hsurj i₀
  refine ⟨r, hr, ?_⟩
  intro A hsmall hsource
  obtain ⟨B, hgraph⟩ := hclassify A hsmall hsource
  have hsecond' : Function.Surjective (fderiv ℂ G (B.normalCurve B.centre_x)) := by
    rw [B.normalCurve_centre]
    exact hsecond
  have hunram := B.normalCurve_projections_unramified hp B.centre_x_mem_target hsecond'
  exact ⟨B, hgraph, B.exponent_ge_two hp,
    B.normalCurve_derivative_ne_zero B.centre_x_mem_target, hunram.1, hunram.2⟩

end FiniteBranchCover

end Paper27.Geometry.FiniteAnalyticGerm
