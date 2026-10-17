import Paper27.Geometry.PuncturedFormulaSix
import Paper27.Geometry.NormalAtlasAction

/-!
# Coordinates of actual differential pushforwards

The rotation weight in the Laurent average is obtained by differentiating the
actual local action. Both the evaluation point and the tangent vector are
transported by the honest neighbourhood permutation.
-/
noncomputable section
open scoped Manifold Topology BigOperators
open Filter
namespace Paper27.Geometry.NormalAtlasAction
variable {X : CompactComplexSurface}

/-- Coordinate conjugacy for the derivative at a general point, including
points off the fixed curve. -/
theorem rotation_derivative_conjugacy_at (c : OpenPartialHomeomorph X (ℂ × ℂ))
    (hc : MDifferentiableOn 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ) c c.source)
    (α : ℂ) (q : X) (hq : q ∈ c.source) (ht : rotate α (c q) ∈ c.target)
    (τ : X → X) (hτ : MDifferentiableAt 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ) τ q)
    (hgerm : τ =ᶠ[𝓝 q] localRotation c α) (v : ℂ × ℂ) :
    mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ) c (τ q)
      (mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ) τ q v) =
        rotate α (mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ) c q v) := by
  have hτq : τ q ∈ c.source := by
    rw [hgerm.self_of_nhds]
    exact localRotation_mem c α ht
  have heq : c ∘ τ =ᶠ[𝓝 q] (rotateLinear α) ∘ c := by
    have hcont := (rotate_continuous α).continuousAt.comp (c.continuousAt hq)
    have htarget : ∀ᶠ x in 𝓝 q, rotate α (c x) ∈ c.target :=
      hcont.tendsto (c.open_target.mem_nhds ht)
    filter_upwards [hgerm, htarget] with x hx htx
    change c (τ x) = rotate α (c x)
    rw [hx]
    exact localRotation_coordinate c α htx
  have hcd := hc.mdifferentiableAt (c.open_source.mem_nhds hq)
  have hcd' := hc.mdifferentiableAt (c.open_source.mem_nhds hτq)
  have he := heq.mfderiv_eq (I := 𝓘(ℂ, ℂ × ℂ)) (I' := 𝓘(ℂ, ℂ × ℂ))
  rw [mfderiv_comp q hcd' hτ,
    mfderiv_comp q (rotateLinear α).mdifferentiableAt hcd,
    ContinuousLinearMap.mfderiv_eq] at he
  exact congrArg (fun L : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ) => L v) he
end Paper27.Geometry.NormalAtlasAction

namespace Paper27.Geometry.RetractionCoordinateGerms.NormalAtlas
open PuncturedSplittingSections NormalAtlasAction EmbeddedFrames
variable {X : CompactComplexSurface} {D : EmbeddedCurve X} {U : D.Neighbourhood}
  {r₁ r₂ : D.Retraction U} {n : ℕ}
  (A : RetractionCoordinateGerms.NormalAtlas D U r₁ r₂ n)

/-- Scalar multiplication by a nonzero number preserves the punctured germ. -/
theorem scalar_punctured_tendsto {α : ℂ} (hα : α ≠ 0) :
    Tendsto (fun y : ℂ => α * y) (𝓝[≠] 0) (𝓝[≠] 0) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · simpa only [id_eq, mul_zero] using
      ((continuous_const.mul continuous_id).continuousAt.tendsto.mono_left
        nhdsWithin_le_nhds : Tendsto (fun y : ℂ => α * y) (𝓝[≠] 0) (𝓝 (α * 0)))
  · filter_upwards [self_mem_nhdsWithin] with y hy
    exact mul_ne_zero hα hy

/-- The actual inverse action, restricted to a normal slice, is the actual
inverse scalar rotation in that slice. -/
theorem action_inverse_slice_germ {G : Type} [Group G]
    (action : NeighbourhoodSplittings.NeighbourhoodAction G r₁)
    (g : G) (α : ℂ) (p : D.curve)
    (hgerm : action.map (g⁻¹) =ᶠ[𝓝 (D.inclusion p)]
      localRotation (A.chart p p).coordinates α⁻¹) :
    (fun y => action.map (g⁻¹) (A.slice p p y)) =ᶠ[𝓝 (0 : ℂ)]
      fun y => A.slice p p (α⁻¹ * y) := by
  have hs := A.slice_tendsto p p (mem_chart_source ℂ p)
  filter_upwards [hgerm.comp_tendsto hs,
    A.slice_eventually p p p (mem_chart_source ℂ p) (mem_chart_source ℂ p)] with y hy htarget
  change action.map (g⁻¹) (A.slice p p y) = localRotation (A.chart p p).coordinates α⁻¹ (A.slice p p y) at hy
  rw [hy]
  change (A.chart p p).coordinates.symm
    (rotate α⁻¹ ((A.chart p p).coordinates (A.slice p p y))) = _
  have hc : (A.chart p p).coordinates (A.slice p p y) = ((chartAt ℂ p) p, y) :=
    (A.chart p p).coordinates.right_inv htarget.1
  rw [hc]
  rfl

/-- The coordinate vector of an actual pushed section has the actual rotation
weight. This is proved on the punctured neighbourhood, before any Laurent
coefficient is extracted. -/
theorem pushforward_sliceCoefficient_germ {G : Type} [Group G]
    (action : NeighbourhoodSplittings.NeighbourhoodAction G r₁)
    (hfix : ∀ g p, action.permutation g (NeighbourhoodSplittings.curvePoint U p) =
      NeighbourhoodSplittings.curvePoint U p)
    (g : G) (α : ℂ) (hα : α ≠ 0) (p : D.curve)
    (hgerm : action.map g =ᶠ[𝓝 (D.inclusion p)]
      localRotation (A.chart p p).coordinates α)
    (hinv : action.map (g⁻¹) =ᶠ[𝓝 (D.inclusion p)]
      localRotation (A.chart p p).coordinates α⁻¹)
    (σ : PuncturedSplittingSections.Section D U) :
    A.sliceCoefficient p p
      (PuncturedSplittingSections.NeighbourhoodAction.pushforward action hfix g σ)
      =ᶠ[𝓝[≠] 0] fun y =>
        rotate α (A.sliceCoefficient p p σ (α⁻¹ * y)) := by
  have hi := mem_chart_source ℂ p
  have hs := A.slice_tendsto p p hi
  have hmul : Tendsto (fun y : ℂ => α⁻¹ * y) (𝓝 0) (𝓝 0) := by
    simpa only [id_eq, mul_zero] using
      ((continuous_const.mul continuous_id).continuousAt (x := (0 : ℂ))).tendsto
  have hsinv := hs.comp hmul
  have hrot : ∀ᶠ x in 𝓝 (D.inclusion p), x ∈ (A.chart p p).coordinates.source ∧
      rotate α ((A.chart p p).coordinates x) ∈ (A.chart p p).coordinates.target :=
    localRotation_eventually_target (A.chart p p).coordinates α
      (A.source_mem p p hi) (by rw [A.centre p p hi])
  have hgin : ∀ᶠ x in 𝓝 (D.inclusion p), action.map g =ᶠ[𝓝 x]
      localRotation (A.chart p p).coordinates α := hgerm.eventuallyEq_nhds
  have hpuninv : ∀ᶠ y in 𝓝[≠] (0 : ℂ), A.slice p p (α⁻¹ * y) ∈ U.domain ∧
      A.slice p p (α⁻¹ * y) ∉ D.support :=
    (scalar_punctured_tendsto (inv_ne_zero hα)).eventually (A.slice_punctured p p hi)
  have hpre := A.action_inverse_slice_germ action g α p hinv
  filter_upwards [(hpre.filter_mono nhdsWithin_le_nhds),
    A.slice_punctured p p hi,
    hpuninv,
    (hsinv.eventually hgin).filter_mono nhdsWithin_le_nhds,
    (hsinv.eventually hrot).filter_mono nhdsWithin_le_nhds] with y hpre hpun hpuninv hgin hrot
  let x := A.slice p p y
  let u := A.slice p p (α⁻¹ * y)
  let q : PuncturedSplittingSections.Point D U := ⟨⟨x, hpun.1⟩, hpun.2⟩
  let q' := PuncturedSplittingSections.NeighbourhoodAction.puncturePermutation action hfix (g⁻¹) q
  have hu : q'.val.val = u := (action.map_eq (g⁻¹) q.val).symm.trans hpre
  have hforw : action.map g u = x := by
    rw [← hu]
    exact action.forward_inverse_image g q.val
  have hbase : r₁.toFun u = r₁.toFun x := by
    rw [← hforw]
    exact (action.preserves_retraction g ⟨u, hpuninv.1⟩).symm
  have heval : PuncturedSplittingSections.evaluation x
      (PuncturedSplittingSections.NeighbourhoodAction.pushforward action hfix g σ) =
      (action.derivative g q'.val).comp (σ q') := by
    rw [PuncturedSplittingSections.evaluation_apply _ hpun.1 hpun.2]
    rfl
  have hevalu : PuncturedSplittingSections.evaluation u σ = σ q' := by
    have he := PuncturedSplittingSections.evaluation_apply σ hpuninv.1 hpuninv.2
    rw [he]
    congr 1
    exact Subtype.ext (Subtype.ext hu.symm)
  let v := σ q' ((tangentCoordinate D.curve p (r₁.toFun u)).symm 1)
  have hd := rotation_derivative_conjugacy_at (A.chart p p).coordinates
    (A.holomorphic p p) α u hrot.1 hrot.2 (action.map g)
    (action.differentiableAt g ⟨u, hpuninv.1⟩) hgin v
  rw [hforw] at hd
  change mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ) (A.chart p p).coordinates x
      ((PuncturedSplittingSections.evaluation x
        (PuncturedSplittingSections.NeighbourhoodAction.pushforward action hfix g σ))
        ((tangentCoordinate D.curve p (r₁.toFun x)).symm 1)) =
    rotate α (mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ) (A.chart p p).coordinates u
      (PuncturedSplittingSections.evaluation u σ
        ((tangentCoordinate D.curve p (r₁.toFun u)).symm 1)))
  rw [heval, hevalu, ← hbase]
  change mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ) (A.chart p p).coordinates x
    (action.derivative g q'.val v) = _
  have hder : action.derivative g q'.val =
      mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ) (action.map g) u :=
    mfderiv_congr_point hu
  rw [hder]
  exact hd
end Paper27.Geometry.RetractionCoordinateGerms.NormalAtlas
