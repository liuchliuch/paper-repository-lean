import Paper27.Geometry.RamificationCovectors
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# The branch graph at one source point

This is the single-source graph-uniqueness step of P27, Proposition 2.4,
paragraph S2.p12. Everything is expressed in actual complex coordinates.
The ambient maps are `F,G : ℂ × ℂ → ℂ`, and a local normalization is an actual
map `ν : ℂ → ℂ × ℂ`. A regular graph identity is differentiated, its scalar
coefficient is identified using the actual ambient covectors, and continuity
extends the result to the normalization centre. Surjectivity of `dF` at the
fixed source point then makes the slopes of all branch graphs equal.

The only rigidity input says that actual local isometries of the Poincaré disc
with the same first jet have the same germ. It does not mention ramification,
normalizations, source branches, or finite maps. Existence of normalization
charts, dense regular points, and local graph isometries is not asserted here.
-/

noncomputable section

open scoped Topology
open Filter

namespace Paper27.Geometry.BranchGraphs

/-- The actual coefficient of the curvature-minus-one Poincaré metric on the
unit disc. It is only used where `‖z‖ < 1`. -/
def poincareDensity (z : ℂ) : ℝ := 4 / (1 - ‖z‖ ^ 2) ^ 2

/-- A local analytic isometry of the actual Poincaré metric, including its open
domain and both unit-disc conditions. This is not an uninterpreted label. -/
structure LocalDiscIsometry (centre : ℂ) where
  toFun : ℂ → ℂ
  domain : Set ℂ
  open_domain : IsOpen domain
  centre_mem : centre ∈ domain
  domain_disc : ∀ z ∈ domain, ‖z‖ < 1
  maps_disc : ∀ z ∈ domain, ‖toFun z‖ < 1
  analytic : AnalyticOnNhd ℂ toFun domain
  metric_identity : ∀ z ∈ domain,
    poincareDensity (toFun z) * ‖deriv toFun z‖ ^ 2 = poincareDensity z

instance {centre : ℂ} : CoeFun (LocalDiscIsometry centre) (fun _ => ℂ → ℂ) := ⟨fun a => a.toFun⟩

/-- Classical first-jet rigidity for local hyperbolic isometries. Petersen,
*Riemannian Geometry*, 2nd ed., Chapter 5, §10.1, Proposition 22 (pp. 143–144)
gives equality of local Riemannian isometries with the same first jet on a
connected neighbourhood. The hypotheses and conclusion here refer solely to
the actual local disc isometries above. -/
def IsometryFirstJetRigidity : Prop :=
  ∀ (z : ℂ) (a b : LocalDiscIsometry z), a z = b z →
    deriv a z = deriv b z → a.toFun =ᶠ[𝓝 z] b.toFun

/-- Equality on an accumulating set passes to a point if both actual functions
are continuous there. Global continuity and global density are unnecessary. -/
theorem eq_at_of_eq_on_accumulating_set {D Y : Type*} [TopologicalSpace D]
    [TopologicalSpace Y] [T2Space Y] {s : Set D} {p : D} {a b : D → Y}
    (hp : p ∈ closure s) (ha : ContinuousAt a p) (hb : ContinuousAt b p)
    (heq : Set.EqOn a b s) : a p = b p := by
  haveI : (𝓝[s] p).NeBot := mem_closure_iff_clusterPt.mp hp
  apply tendsto_nhds_unique_of_eventuallyEq
    (ha.continuousWithinAt (s := s)) (hb.continuousWithinAt (s := s))
  exact Filter.eventually_of_mem self_mem_nhdsWithin fun x hx => heq hx

/-- At a regular normalization point, the graph identity's actual derivative
identifies the unique ambient proportionality scalar. -/
theorem graph_slope_at_regular_point
    {F G : ℂ × ℂ → ℂ} {ν : ℂ → ℂ × ℂ} {φ : ℂ → ℂ} {z : ℂ}
    (hF : DifferentiableAt ℂ F (ν z)) (hG : DifferentiableAt ℂ G (ν z))
    (hν : DifferentiableAt ℂ ν z) (hφ : DifferentiableAt ℂ φ (F (ν z)))
    (hsurjF : Function.Surjective (fderiv ℂ F (ν z)))
    (hsurjG : Function.Surjective (fderiv ℂ G (ν z)))
    (hjoint : ¬ Function.Surjective
      (fun v : ℂ × ℂ => (fderiv ℂ F (ν z) v, fderiv ℂ G (ν z) v)))
    (hregular : fderiv ℂ F (ν z) (deriv ν z) ≠ 0)
    (hgraph : G ∘ ν =ᶠ[𝓝 z] φ ∘ F ∘ ν) :
    ∀ v : ℂ × ℂ, fderiv ℂ G (ν z) v = deriv φ (F (ν z)) * fderiv ℂ F (ν z) v := by
  obtain ⟨a, ⟨_ha0, ha⟩, _hu⟩ :=
    RamificationCovectors.existsUnique_nonzero_slope
      (fderiv ℂ F (ν z)).toLinearMap (fderiv ℂ G (ν z)).toLinearMap
      hsurjF hsurjG hjoint
  have hGν : HasDerivAt (G ∘ ν) (fderiv ℂ G (ν z) (deriv ν z)) z :=
    hG.hasFDerivAt.comp_hasDerivAt z hν.hasDerivAt
  have hFν : HasDerivAt (F ∘ ν) (fderiv ℂ F (ν z) (deriv ν z)) z :=
    hF.hasFDerivAt.comp_hasDerivAt z hν.hasDerivAt
  have hφFν : HasDerivAt (φ ∘ F ∘ ν)
      (deriv φ (F (ν z)) * fderiv ℂ F (ν z) (deriv ν z)) z :=
    hφ.hasDerivAt.comp z hFν
  have hderiv : fderiv ℂ G (ν z) (deriv ν z) =
      deriv φ (F (ν z)) * fderiv ℂ F (ν z) (deriv ν z) :=
    hGν.unique (hφFν.congr_of_eventuallyEq hgraph)
  have haφ : a = deriv φ (F (ν z)) := by
    apply mul_right_cancel₀ hregular
    exact (ha (deriv ν z)).symm.trans hderiv
  intro v
  simpa only [haφ] using ha v

/-- A local normalization branch and its local hyperbolic graph, all at one
specified source point `p`. No relation between different source points can be
obtained from this structure. -/
structure NormalizedBranchGraph (F G : ℂ × ℂ → ℂ) (p : ℂ × ℂ) where
  normalization : ℂ → ℂ × ℂ
  centre : ℂ
  centre_maps : normalization centre = p
  normalization_analytic : AnalyticAt ℂ normalization centre
  regular : Set ℂ
  centre_in_closure : centre ∈ closure regular
  first_differentiable : ∀ z ∈ regular, DifferentiableAt ℂ F (normalization z)
  second_differentiable : ∀ z ∈ regular, DifferentiableAt ℂ G (normalization z)
  normalization_differentiable : ∀ z ∈ regular, DifferentiableAt ℂ normalization z
  first_surjective : ∀ z ∈ regular, Function.Surjective (fderiv ℂ F (normalization z))
  second_surjective : ∀ z ∈ regular, Function.Surjective (fderiv ℂ G (normalization z))
  joint_not_surjective : ∀ z ∈ regular, ¬ Function.Surjective
    (fun v : ℂ × ℂ => (fderiv ℂ F (normalization z) v, fderiv ℂ G (normalization z) v))
  regular_first_derivative : ∀ z ∈ regular,
    fderiv ℂ F (normalization z) (deriv normalization z) ≠ 0
  graph : LocalDiscIsometry (F p)
  regular_image : ∀ z ∈ regular, F (normalization z) ∈ graph.domain
  graph_identity : ∀ z ∈ regular,
    G ∘ normalization =ᶠ[𝓝 z] graph.toFun ∘ F ∘ normalization

namespace NormalizedBranchGraph

variable {F G : ℂ × ℂ → ℂ} {p : ℂ × ℂ}

/-- The value of every graph is the same actual target value at this source
point. It is derived from the regular identities by continuity. -/
theorem value_at_centre (B : NormalizedBranchGraph F G p)
    (hF : AnalyticAt ℂ F p) (hG : AnalyticAt ℂ G p) : B.graph (F p) = G p := by
  have hν : ContinuousAt B.normalization B.centre := B.normalization_analytic.continuousAt
  have hFν : ContinuousAt (F ∘ B.normalization) B.centre := by
    apply ContinuousAt.comp _ hν
    simpa only [B.centre_maps] using hF.continuousAt
  have hGν : ContinuousAt (G ∘ B.normalization) B.centre := by
    apply ContinuousAt.comp _ hν
    simpa only [B.centre_maps] using hG.continuousAt
  have hφ : ContinuousAt B.graph.toFun (F (B.normalization B.centre)) := by
    simpa only [B.centre_maps] using (B.graph.analytic _ B.graph.centre_mem).continuousAt
  have heq := eq_at_of_eq_on_accumulating_set B.centre_in_closure hGν
    (hφ.comp (f := F ∘ B.normalization) (x := B.centre) hFν)
    (fun z hz => (B.graph_identity z hz).eq_of_nhds)
  simpa only [Function.comp_apply, B.centre_maps] using heq.symm

/-- The ambient derivative relation at the possibly singular normalization
centre is proved by continuity from the actual regular graph identities. -/
theorem covector_relation_at_centre (B : NormalizedBranchGraph F G p)
    (hF : AnalyticAt ℂ F p) (hG : AnalyticAt ℂ G p) :
    ∀ v : ℂ × ℂ, fderiv ℂ G p v = deriv B.graph.toFun (F p) * fderiv ℂ F p v := by
  intro v
  have hν : ContinuousAt B.normalization B.centre := B.normalization_analytic.continuousAt
  have hFν : ContinuousAt (F ∘ B.normalization) B.centre := by
    apply ContinuousAt.comp _ hν
    simpa only [B.centre_maps] using hF.continuousAt
  have hDF : ContinuousAt (fun z => fderiv ℂ F (B.normalization z) v) B.centre := by
    apply ContinuousAt.clm_apply _ continuousAt_const
    apply ContinuousAt.comp _ hν
    simpa only [B.centre_maps] using hF.fderiv.continuousAt
  have hDG : ContinuousAt (fun z => fderiv ℂ G (B.normalization z) v) B.centre := by
    apply ContinuousAt.clm_apply _ continuousAt_const
    apply ContinuousAt.comp _ hν
    simpa only [B.centre_maps] using hG.fderiv.continuousAt
  have hdφ : ContinuousAt (deriv B.graph.toFun) (F (B.normalization B.centre)) := by
    simpa only [B.centre_maps] using (B.graph.analytic _ B.graph.centre_mem).deriv.continuousAt
  have hright := (hdφ.comp (f := F ∘ B.normalization) (x := B.centre) hFν).mul hDF
  have heq : Set.EqOn (fun z => fderiv ℂ G (B.normalization z) v)
      (fun z => deriv B.graph.toFun (F (B.normalization z)) *
        fderiv ℂ F (B.normalization z) v) B.regular := by
    intro z hz
    exact graph_slope_at_regular_point (B.first_differentiable z hz)
      (B.second_differentiable z hz) (B.normalization_differentiable z hz)
      (B.graph.analytic _ (B.regular_image z hz)).differentiableAt
      (B.first_surjective z hz) (B.second_surjective z hz)
      (B.joint_not_surjective z hz) (B.regular_first_derivative z hz)
      (B.graph_identity z hz) v
  have hcentre := eq_at_of_eq_on_accumulating_set B.centre_in_closure hDG hright heq
  simpa only [Function.comp_apply, B.centre_maps] using hcentre

end NormalizedBranchGraph

/-- All branch graphs at the fixed source point have the same germ. The slope
is determined by the surjective covector `dF_p`, even if the normalization
derivative itself vanishes at its centre. -/
theorem single_source_branch_graph_germ_unique (rigidity : IsometryFirstJetRigidity)
    {F G : ℂ × ℂ → ℂ} {p : ℂ × ℂ} (hF : AnalyticAt ℂ F p) (hG : AnalyticAt ℂ G p)
    (hsurj : Function.Surjective (fderiv ℂ F p))
    (A B : NormalizedBranchGraph F G p) :
    A.graph.toFun =ᶠ[𝓝 (F p)] B.graph.toFun := by
  apply rigidity (F p) A.graph B.graph
  · exact (A.value_at_centre hF hG).trans (B.value_at_centre hF hG).symm
  · apply DifferentialRigidity.scalar_unique (fderiv ℂ F p).toLinearMap hsurj
    intro v
    exact (A.covector_relation_at_centre hF hG v).symm.trans
      (B.covector_relation_at_centre hF hG v)

/-- For finitely many branches through this one source point, a single target
neighbourhood represents all the identical graph germs. -/
theorem finite_branches_common_graph_neighbourhood (rigidity : IsometryFirstJetRigidity)
    {F G : ℂ × ℂ → ℂ} {p : ℂ × ℂ} (hF : AnalyticAt ℂ F p) (hG : AnalyticAt ℂ G p)
    (hsurj : Function.Surjective (fderiv ℂ F p)) {ι : Type*} [Fintype ι]
    (branches : ι → NormalizedBranchGraph F G p) (i₀ : ι) :
    ∃ U : Set ℂ, IsOpen U ∧ F p ∈ U ∧
      ∀ z ∈ U, ∀ i, (branches i).graph z = (branches i₀).graph z := by
  have hevent : ∀ᶠ z in 𝓝 (F p), ∀ i, (branches i).graph z = (branches i₀).graph z := by
    apply Filter.eventually_all.mpr
    intro i
    exact single_source_branch_graph_germ_unique rigidity hF hG hsurj
      (branches i) (branches i₀)
  obtain ⟨U, hU, hUopen, hp⟩ := mem_nhds_iff.mp hevent
  exact ⟨U, hUopen, hp, fun z hz => hU hz⟩

end Paper27.Geometry.BranchGraphs
