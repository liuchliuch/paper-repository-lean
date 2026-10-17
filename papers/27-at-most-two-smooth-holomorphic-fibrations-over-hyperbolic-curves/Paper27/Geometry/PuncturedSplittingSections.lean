import Paper27.Geometry.MeromorphicSplittingAverage
import Paper27.Geometry.NormalAtlasTensor

/-!
# Actual joint-inverse sections on the punctured surface neighbourhood

The sections and coordinate evaluations are actual functions and actual
manifold differentials. The joint inverse is constructed on U minus D, where
it is nonsingular; no splitting is postulated on the curve itself.
-/
noncomputable section
open scoped Manifold Topology BigOperators
open Filter

namespace Paper27.Geometry.PuncturedSplittingSections
open EmbeddedFrames NeighbourhoodSplittings RetractionCoordinateGerms

variable {X : CompactComplexSurface} {D : EmbeddedCurve X} {U : D.Neighbourhood}

abbrev Point (D : EmbeddedCurve X) (U : D.Neighbourhood) :=
  {p : U.domain // p.val ∉ D.support}
abbrev Section (D : EmbeddedCurve X) (U : D.Neighbourhood) :=
  Point D U → ℂ →L[ℂ] (ℂ × ℂ)

 def restrict : NeighbourhoodSplittings.Section U →ₗ[ℂ] Section D U where
  toFun σ p := σ p.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

 def evaluation (x : X) : Section D U →ₗ[ℂ] (ℂ →L[ℂ] (ℂ × ℂ)) := by
  classical
  exact if hx : x ∈ U.domain ∧ x ∉ D.support then
    { toFun := fun σ => σ ⟨⟨x, hx.1⟩, hx.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl } else 0

 theorem evaluation_apply (σ : Section D U) {x : X}
    (hx : x ∈ U.domain) (hd : x ∉ D.support) :
    evaluation x σ = σ ⟨⟨x, hx⟩, hd⟩ := by
  classical
  simp only [evaluation, dif_pos (show x ∈ U.domain ∧ x ∉ D.support from ⟨hx, hd⟩)]
  rfl

 def IsSplitting (r : D.Retraction U) (σ : Section D U) : Prop :=
  ∀ p : Point D U, (mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ) r.toFun p.val.val).comp (σ p) =
    ContinuousLinearMap.id ℂ ℂ

 def jointDifferential (r s : D.Retraction U) (p : Point D U) :
    (ℂ × ℂ) →L[ℂ] (ℂ × ℂ) :=
  (mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ) r.toFun p.val.val).prod
    (mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ) s.toFun p.val.val)

 def JointTransverse (r s : D.Retraction U) : Prop :=
  ∀ p : Point D U, Function.Bijective (jointDifferential r s p)

 def jointEquiv (r s : D.Retraction U) (ht : JointTransverse r s) (p : Point D U) :
    (ℂ × ℂ) ≃L[ℂ] (ℂ × ℂ) :=
  (LinearEquiv.ofBijective (jointDifferential r s p).toLinearMap (ht p)).toContinuousLinearEquiv

/-- The actual splitting in the actual kernel of ds. -/
 def jointInverse (r s : D.Retraction U) (ht : JointTransverse r s) : Section D U :=
  fun p => (jointEquiv r s ht p).symm.toContinuousLinearMap.comp (ContinuousLinearMap.inl ℂ ℂ ℂ)

 theorem jointInverse_splitting (r s : D.Retraction U) (ht : JointTransverse r s) :
    IsSplitting r (jointInverse r s ht) := by
  intro p
  apply ContinuousLinearMap.ext
  intro w
  exact congrArg Prod.fst ((jointEquiv r s ht p).apply_symm_apply (w, 0))

 theorem jointInverse_kernel (r s : D.Retraction U) (ht : JointTransverse r s)
    (p : Point D U) (w : ℂ) :
    mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ) s.toFun p.val.val (jointInverse r s ht p w) = 0 :=
  congrArg Prod.snd ((jointEquiv r s ht p).apply_symm_apply (w, 0))

/-- Actual coefficients in any actual local surface chart, normalized by the
actual base chart derivative. -/
 def chartCoefficient (r : D.Retraction U) (c : OpenPartialHomeomorph X (ℂ × ℂ))
    (i : D.curve) (w : ℂ × ℂ) : Section D U →ₗ[ℂ] (ℂ × ℂ) where
  toFun σ :=
    let x := c.symm w
    mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ) c x
      (evaluation x σ ((tangentCoordinate D.curve i (r.toFun x)).symm 1))
  map_add' σ τ := by simp only [map_add, ContinuousLinearMap.add_apply]
  map_smul' a σ := by simp only [map_smul, ContinuousLinearMap.smul_apply, RingHom.id_apply]

 def HolomorphicSection (r : D.Retraction U) (σ : Section D U) : Prop :=
  ∀ p : Point D U, AnalyticAt ℂ
    (fun z => chartCoefficient r (chartAt (ℂ × ℂ) p.val.val) (r.toFun p.val.val) z σ)
    ((chartAt (ℂ × ℂ) p.val.val) p.val.val)

end Paper27.Geometry.PuncturedSplittingSections

namespace Paper27.Geometry.RetractionCoordinateGerms.NormalAtlas
open EmbeddedFrames PuncturedSplittingSections
variable {X : CompactComplexSurface} {D : EmbeddedCurve X} {U : D.Neighbourhood}
  {r₁ r₂ r₃ : D.Retraction U} {n : ℕ}
  (A : RetractionCoordinateGerms.NormalAtlas D U r₁ r₂ n)

/-- Actual differential transport in a normal chart, for an actual retraction. -/
 theorem coordinate_derivative_apply (r : D.Retraction U) (i p : D.curve)
    {w : ℂ × ℂ} (hw : w ∈ (A.chart i p).coordinates.target)
    (hb : r.toFun ((A.chart i p).coordinates.symm w) ∈ D.curve.chartDomain i)
    (v : ℂ × ℂ) :
    fderiv ℂ (A.coordinate r i p) w v =
      tangentCoordinate D.curve i (r.toFun ((A.chart i p).coordinates.symm w))
        (mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ) r.toFun ((A.chart i p).coordinates.symm w)
          (mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ) (A.chart i p).coordinates.symm w v)) := by
  have hinv := (A.inverse_holomorphic i p).mdifferentiableAt
    ((A.chart i p).coordinates.open_target.mem_nhds hw)
  have hr := r.holomorphic.mdifferentiableAt (U.open_domain.mem_nhds
    (A.source_subset i p ((A.chart i p).coordinates.map_target hw)))
  have hc := (mdifferentiable_chart (I := 𝓘(ℂ, ℂ)) i).mdifferentiableAt hb
  rw [← mfderiv_eq_fderiv]
  change mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ)
    ((chartAt ℂ i) ∘ r.toFun ∘ (A.chart i p).coordinates.symm) w v = _
  rw [mfderiv_comp w hc (hr.comp w hinv), mfderiv_comp w hr hinv]
  have heq := tangentCoordinate_eq_chart D.curve i
    (r.toFun ((A.chart i p).coordinates.symm w)) hb
  exact congrArg (fun L : ℂ →L[ℂ] ℂ => L
    (mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ) r.toFun ((A.chart i p).coordinates.symm w)
      (mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ) (A.chart i p).coordinates.symm w v))) heq.symm

/-- A splitting in the actual kernel has exactly (1,-rx/ry) as coordinate
vector, proved using the actual joint derivative and chart inverse derivative. -/
 theorem splitting_coordinate (r : D.Retraction U) (σ : PuncturedSplittingSections.Section D U)
    (hs : PuncturedSplittingSections.IsSplitting r₁ σ)
    (hk : ∀ q : Point D U, ∀ v : ℂ,
      mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ) r.toFun q.val.val (σ q v) = 0)
    (i p : D.curve) {w : ℂ × ℂ} (hw : w ∈ (A.chart i p).coordinates.target)
    (hd : (A.chart i p).coordinates.symm w ∉ D.support)
    (hb : r.toFun ((A.chart i p).coordinates.symm w) ∈ D.curve.chartDomain i)
    (hy : fderiv ℂ (A.coordinate r i p) w (0, 1) ≠ 0) :
    chartCoefficient r₁ (A.chart i p).coordinates i w σ =
      (1, -fderiv ℂ (A.coordinate r i p) w (1, 0) /
        fderiv ℂ (A.coordinate r i p) w (0, 1)) := by
  let x := (A.chart i p).coordinates.symm w
  have hx : x ∈ (A.chart i p).coordinates.source := (A.chart i p).coordinates.map_target hw
  have hxU : x ∈ U.domain := A.source_subset i p hx
  let q : Point D U := ⟨⟨x, hxU⟩, hd⟩
  let t := (tangentCoordinate D.curve i (r₁.toFun x)).symm 1
  let V := mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ) (A.chart i p).coordinates x (σ q t)
  have hinv : mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ) (A.chart i p).coordinates.symm w V = σ q t := by
    have he : (A.chart i p).coordinates.MDifferentiable 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ) :=
      ⟨A.holomorphic i p, A.inverse_holomorphic i p⟩
    have hh := congrArg (fun L : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ) => L (σ q t)) (he.symm_comp_deriv hx)
    have hc : (A.chart i p).coordinates x = w := (A.chart i p).coordinates.right_inv hw
    change mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ) (A.chart i p).coordinates.symm
      ((A.chart i p).coordinates x) V = σ q t at hh
    rwa [hc] at hh
  have hfirst : V.1 = 1 := by
    have hcoord := (A.coordinate_derivative_apply r₁ i p hw ((A.chart i p).r_source x hx) V)
    have hf := (A.coordinate_first_germ i p hw).fderiv_eq (𝕜 := ℂ)
    rw [hf, fderiv_fst, hinv] at hcoord
    have hproj := congrArg (fun L : ℂ →L[ℂ] ℂ => L t) (hs q)
    change mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ) r₁.toFun x (σ q t) = t at hproj
    rw [hproj] at hcoord
    exact hcoord.trans ((tangentCoordinate D.curve i (r₁.toFun x)).apply_symm_apply 1)
  have hkernel : fderiv ℂ (A.coordinate r i p) w V = 0 := by
    rw [A.coordinate_derivative_apply r i p hw hb V, hinv, hk q t, map_zero]
  have hsecond : V.2 = -fderiv ℂ (A.coordinate r i p) w (1, 0) /
      fderiv ℂ (A.coordinate r i p) w (0, 1) := by
    rw [NormalizedDifferentials.covector_apply, hfirst, mul_one] at hkernel
    apply (eq_div_iff hy).mpr
    linear_combination hkernel
  change mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ) (A.chart i p).coordinates x
    (evaluation x σ ((tangentCoordinate D.curve i (r₁.toFun x)).symm 1)) = _
  rw [evaluation_apply σ hxU hd]
  exact Prod.ext hfirst hsecond

/-- A nonzero point of the actual normal slice is off the actual embedded
curve, after restricting to the chart source. -/
 theorem slice_punctured (i p : D.curve) (hi : p ∈ D.curve.chartDomain i) :
    ∀ᶠ y in 𝓝[≠] (0 : ℂ), A.slice i p y ∈ U.domain ∧ A.slice i p y ∉ D.support := by
  filter_upwards [(A.slice_eventually i i p hi hi).filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with y hy hne
  refine ⟨A.source_subset i p hy.2.1, ?_⟩
  rintro ⟨q, hq⟩
  have hcentre := (A.centered i p hi).centre_at q (by
    change D.inclusion q ∈ (A.chart i p).coordinates.source
    rw [hq]
    exact hy.2.1)
  have hcoord : (A.chart i p).coordinates (A.slice i p y) = ((chartAt ℂ i) p, y) :=
    (A.chart i p).coordinates.right_inv hy.1
  change (A.chart i p).coordinates (D.inclusion q) = _ at hcentre
  rw [hq, hcoord] at hcentre
  exact hne (congrArg Prod.snd hcentre)

 theorem normalPartial_nonzero_punctured
    (regularity : CoordinateCalculus.SurfaceAnalyticRegularity)
    (r : D.Retraction U) (ho : A.HasThirdOrder r) (hn : 0 < n)
    (i p : D.curve) (hi : p ∈ D.curve.chartDomain i) :
    ∀ᶠ y in 𝓝[≠] (0 : ℂ), A.normalPartial r i p y ≠ 0 := by
  have hunit : A.derivativeUnit r ho i p 0 ≠ 0 := by
    rw [A.derivativeUnit_zero]
    exact mul_ne_zero (by exact_mod_cast (Nat.ne_of_gt hn)) (A.leading_ne_zero r ho i p hi)
  filter_upwards [(A.normalPartial_third_derivative regularity r i p hi).filter_mono nhdsWithin_le_nhds,
    (A.third_derivative_factor r ho hn i p hi).filter_mono nhdsWithin_le_nhds,
    ((A.derivativeUnit_analytic r ho i p hi).continuousAt.eventually_ne hunit).filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with y hy hdy hunit_y hne
  rw [hy, hdy]
  exact mul_ne_zero (pow_ne_zero _ (show y ≠ 0 from hne)) hunit_y

/-- The actual normal-chart vector of the actual punctured joint inverse is
(1, verticalSplitting); thus its Laurent coefficients are those computed from
actual derivative quotients in `MeromorphicSplittingAverage`. -/
 theorem jointInverse_coordinate_germ
    (regularity : CoordinateCalculus.SurfaceAnalyticRegularity)
    (r : D.Retraction U) (ho : A.HasThirdOrder r) (hn : 0 < n)
    (ht : PuncturedSplittingSections.JointTransverse r₁ r)
    (i p : D.curve) (hi : p ∈ D.curve.chartDomain i) :
    (fun y => chartCoefficient r₁ (A.chart i p).coordinates i ((chartAt ℂ i) p, y)
      (PuncturedSplittingSections.jointInverse r₁ r ht)) =ᶠ[𝓝[≠] 0]
      fun y => (1, A.verticalSplitting r i p y) := by
  have hr : Tendsto (fun y => r.toFun (A.slice i p y)) (𝓝 0) (𝓝 p) := by
    have hc := (r.holomorphic.mdifferentiableAt
      (U.open_domain.mem_nhds (U.contains p))).continuousAt.tendsto
    simpa only [r.retract] using hc.comp (A.slice_tendsto i p hi)
  have hb : ∀ᶠ y in 𝓝 (0 : ℂ), r.toFun (A.slice i p y) ∈ D.curve.chartDomain i :=
    hr ((chartAt ℂ i).open_source.mem_nhds hi)
  filter_upwards [(A.slice_eventually i i p hi hi).filter_mono nhdsWithin_le_nhds,
    A.slice_punctured i p hi, A.normalPartial_nonzero_punctured regularity r ho hn i p hi,
    hb.filter_mono nhdsWithin_le_nhds] with y hy hpun hnorm hb
  exact A.splitting_coordinate r (PuncturedSplittingSections.jointInverse r₁ r ht)
    (PuncturedSplittingSections.jointInverse_splitting r₁ r ht)
    (PuncturedSplittingSections.jointInverse_kernel r₁ r ht)
    i p hy.1 hpun.2 hb hnorm

end Paper27.Geometry.RetractionCoordinateGerms.NormalAtlas
