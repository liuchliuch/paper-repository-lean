import Paper27.Geometry.RetractionCoefficientHolomorphic
import Paper27.Geometry.LeadingNormalTensor
import Paper27.Geometry.IntrinsicDichotomy
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# The intrinsic normal tensor from actual normalized retraction charts

Actual normal-coordinate differentials, applied to honest ambient frames,
produce the leading tensor coefficient. The normal chart may vary at every
point. Powers of its differential are independent of that choice. No global
root of a tangent transition and no normal tensor identity is an input.
-/
noncomputable section
open scoped Manifold Topology
open Filter Polynomial

namespace Paper27.Geometry.RetractionCoefficientHolomorphic.CenteredChart
open RetractionCoordinateGerms RetractionCoefficientHolomorphic EmbeddedFrames

variable {X : CompactComplexSurface} {D : EmbeddedCurve X} {U : D.Neighbourhood}
  {r₁ r₂ : D.Retraction U} {n : ℕ}
  {N : HolomorphicLineCocycle D.curve} {T : TangentLineCocycle D.curve}

variable {i p : D.curve} (c : RetractionCoefficientHolomorphic.CenteredChart D U r₁ r₂ n i p)

/-- The actual derivative of the actual normal chart, as an equivalence. -/
def differential : (ℂ × ℂ) ≃L[ℂ] (ℂ × ℂ) :=
  (show c.chart.coordinates.MDifferentiable 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ) from
    ⟨c.holomorphic, c.inverse_holomorphic⟩).mfderiv c.source_mem

 theorem differential_apply (v : ℂ × ℂ) : c.differential v =
    mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ) c.chart.coordinates (D.inclusion p) v := rfl

 theorem differential_inclusion (hi : p ∈ D.curve.chartDomain i) (w : ℂ) :
    c.differential (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ × ℂ) D.inclusion p w) =
      (tangentCoordinate D.curve i p w, 0) := by
  have hc : MDifferentiableAt 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ)
      c.chart.coordinates (D.inclusion p) :=
    c.holomorphic.mdifferentiableAt (c.chart.coordinates.open_source.mem_nhds c.source_mem)
  have heq : c.chart.coordinates ∘ D.inclusion =ᶠ[𝓝 p]
      fun q => ((chartAt ℂ i) q, (0 : ℂ)) := by
    filter_upwards [D.inclusion.holomorphic.continuous.continuousAt
      (c.chart.coordinates.open_source.mem_nhds c.source_mem)] with q hq
    exact c.centre_at q hq
  have hd := heq.mfderiv_eq (I := 𝓘(ℂ, ℂ)) (I' := 𝓘(ℂ, ℂ × ℂ))
  rw [mfderiv_comp p hc (D.inclusion.holomorphic p)] at hd
  let L : ℂ →L[ℂ] ℂ × ℂ := ContinuousLinearMap.inl ℂ ℂ ℂ
  have hL : MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ × ℂ) L ((chartAt ℂ i) p) :=
    mdifferentiableAt_iff_differentiableAt.mpr L.differentiableAt
  have hr : mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ × ℂ)
      (fun q : D.curve => ((chartAt ℂ i) q, (0 : ℂ))) p =
      L.comp (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (chartAt ℂ i) p) := by
    change mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ × ℂ) (L ∘ chartAt ℂ i) p = _
    rw [mfderiv_comp p hL ((mdifferentiable_chart i).mdifferentiableAt hi),
      mfderiv_eq_fderiv, L.fderiv]
  rw [hr] at hd
  have h := congrArg (fun A : ℂ →L[ℂ] (ℂ × ℂ) => A w) hd
  change c.differential _ = ((mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (chartAt ℂ i) p) w, 0) at h
  rw [← tangentCoordinate_eq_chart D.curve i p hi] at h
  exact h

/-- A normalized chart and an honest frame agree on tangent coordinates. -/
 theorem differential_frame_tangent (F : RawEmbeddedFrames D N T.bundle)
    (hi : p ∈ D.curve.chartDomain i) (z : ℂ) :
    c.differential (F.frame i p (z, 0)) = (z, 0) := by
  rw [F.tangent_adapted i p hi, c.differential_inclusion hi,
    ContinuousLinearEquiv.apply_symm_apply]

/-- The scalar induced by the actual chart differential on the honest normal
quotient frame. It need not be a globally chosen nth root. -/
def frameScalar (F : RawEmbeddedFrames D N T.bundle) : ℂ :=
  (c.differential (F.frame i p (0, 1))).2

 theorem differential_frame_normal (F : RawEmbeddedFrames D N T.bundle)
    (hi : p ∈ D.curve.chartDomain i) (v : ℂ × ℂ) :
    (c.differential (F.frame i p v)).2 = c.frameScalar F * v.2 := by
  have hv : v = (v.1, 0) + v.2 • (0, 1) := by ext <;> simp
  calc
    _ = (c.differential (F.frame i p (v.1, 0))).2 +
        v.2 * (c.differential (F.frame i p (0, 1))).2 := by
      conv_lhs => rw [hv, map_add, map_smul, map_add, map_smul]
      rfl
    _ = _ := by rw [c.differential_frame_tangent F hi]; simp only [zero_add, frameScalar, mul_comm]

 theorem frameScalar_ne_zero (F : RawEmbeddedFrames D N T.bundle)
    (hi : p ∈ D.curve.chartDomain i) : c.frameScalar F ≠ 0 := by
  intro hz
  let v := c.differential (F.frame i p (0, 1))
  have hv : c.differential (F.frame i p (0, 1)) = (v.1, 0) := Prod.ext rfl hz
  have hh := c.differential.injective
    (hv.trans (c.differential_frame_tangent F hi v.1).symm)
  have hp := congrArg Prod.snd ((F.frame i p).injective hh)
  exact one_ne_zero hp

/-- The derivative of a normal slice transition is the actual mixed chart
normal differential, with no transition scalar supplied independently. -/
 theorem cross_derivative {j : D.curve}
    (e : RetractionCoefficientHolomorphic.CenteredChart D U r₁ r₂ n j p) :
    deriv (fun z => (e.chart.coordinates (c.slice z)).2) 0 =
      (e.differential (c.differential.symm (0, 1))).2 := by
  let w : ℂ × ℂ := ((chartAt ℂ i) p, 0)
  have hw : w ∈ c.chart.coordinates.target := by
    rw [show w = c.chart.coordinates (D.inclusion p) from c.centre.symm]
    exact c.chart.coordinates.map_source c.source_mem
  have hzero : c.chart.coordinates.symm w = D.inclusion p := c.slice_zero
  have hinv := c.inverse_holomorphic.mdifferentiableAt
    (c.chart.coordinates.open_target.mem_nhds hw)
  have he := e.holomorphic.mdifferentiableAt
    (e.chart.coordinates.open_source.mem_nhds e.source_mem)
  have he' : MDifferentiableAt 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ)
      e.chart.coordinates (c.chart.coordinates.symm w) := by rw [hzero]; exact he
  let G : ℂ × ℂ → ℂ × ℂ := e.chart.coordinates ∘ c.chart.coordinates.symm
  have hG : DifferentiableAt ℂ G w :=
    mdifferentiableAt_iff_differentiableAt.mp (he'.comp w hinv)
  have hcinv : mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ) c.chart.coordinates.symm w =
      c.differential.symm.toContinuousLinearMap := by
    change _ = mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ)
      c.chart.coordinates.symm (c.chart.coordinates (D.inclusion p))
    rw [c.centre]
  have hDG : fderiv ℂ G w = e.differential.toContinuousLinearMap.comp
      c.differential.symm.toContinuousLinearMap := by
    rw [← mfderiv_eq_fderiv, mfderiv_comp w he' hinv, hzero, hcinv]
    rfl
  have hline : HasDerivAt (fun z : ℂ => ((chartAt ℂ i) p, z)) (0, 1) 0 :=
    (hasDerivAt_const (0 : ℂ) ((chartAt ℂ i) p)).prodMk (hasDerivAt_id (0 : ℂ))
  have hfull := hG.hasFDerivAt.comp_hasDerivAt 0 hline
  have hs := (hasFDerivAt_snd (𝕜 := ℂ) (p := G w)).comp_hasDerivAt 0 hfull
  have h := hs.deriv
  rw [hDG] at h
  exact h

/-- The normal row of a linear map killing the tangent line is scalar. -/
 theorem linear_normal_row (L : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ))
    (hL : ∀ z : ℂ, (L (z, 0)).2 = 0) (v : ℂ × ℂ) :
    (L v).2 = (L (0, 1)).2 * v.2 := by
  have hv : v = (v.1, 0) + v.2 • (0, 1) := by ext <;> simp
  calc
    (L v).2 = (L (v.1, 0)).2 + v.2 * (L (0, 1)).2 := by
      conv_lhs => rw [hv, map_add, map_smul]
      rfl
    _ = _ := by rw [hL]; simp only [zero_add, mul_comm]

/-- Mixed normalized-chart and honest-frame transitions give the actual scalar
law before taking nth powers. Arbitrary frame tangent cross-terms disappear. -/
 theorem frameScalar_transition {j : D.curve}
    (e : RetractionCoefficientHolomorphic.CenteredChart D U r₁ r₂ n j p)
    (F : RawEmbeddedFrames D N T.bundle)
    (hi : p ∈ D.curve.chartDomain i) (hj : p ∈ D.curve.chartDomain j) :
    e.frameScalar F * N.transition i j p =
      deriv (fun z => (e.chart.coordinates (c.slice z)).2) 0 * c.frameScalar F := by
  let L := e.differential.toContinuousLinearMap.comp c.differential.symm.toContinuousLinearMap
  have haxis : ∀ z : ℂ, (L (z, 0)).2 = 0 := by
    intro z
    have hinv : c.differential.symm (z, 0) = F.frame i p (z, 0) := by
      apply c.differential.injective
      rw [ContinuousLinearEquiv.apply_symm_apply, c.differential_frame_tangent F hi]
    change (e.differential (c.differential.symm (z, 0))).2 = 0
    rw [hinv, F.tangent_adapted i p hi, e.differential_inclusion hj]
  have hrow := linear_normal_row L haxis (c.differential (F.frame i p (0, 1)))
  have hleft := e.differential_frame_normal F hj
    ((F.frame j p).symm (F.frame i p (0, 1)))
  rw [ContinuousLinearEquiv.apply_symm_apply, F.normal i j p hi hj, mul_one] at hleft
  have hrow' : (e.differential (F.frame i p (0, 1))).2 =
      (e.differential (c.differential.symm (0, 1))).2 * c.frameScalar F := by
    change (e.differential (c.differential.symm (c.differential (F.frame i p (0, 1))))).2 =
      (e.differential (c.differential.symm (0, 1))).2 * c.frameScalar F at hrow
    rw [ContinuousLinearEquiv.symm_apply_apply] at hrow
    exact hrow
  rw [c.cross_derivative e]
  exact hleft.symm.trans hrow'

/-- A fixed normal coordinate written in one fixed actual ambient chart. -/
def writtenNormal (a : X) (w : ℂ × ℂ) : ℂ :=
  (c.chart.coordinates ((chartAt (ℂ × ℂ) a).symm w)).2

 theorem writtenNormal_mdifferentiableAt (a : X) {w : ℂ × ℂ}
    (hw : w ∈ (chartAt (ℂ × ℂ) a).target)
    (hc : (chartAt (ℂ × ℂ) a).symm w ∈ c.chart.coordinates.source) :
    MDifferentiableAt 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ) (c.writtenNormal a) w := by
  have hci := c.holomorphic.mdifferentiableAt (c.chart.coordinates.open_source.mem_nhds hc)
  have hproj : MDifferentiableAt 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ)
      Prod.snd (c.chart.coordinates ((chartAt (ℂ × ℂ) a).symm w)) :=
    mdifferentiableAt_iff_differentiableAt.mpr differentiableAt_snd
  exact hproj.comp w (hci.comp w ((mdifferentiable_chart a).mdifferentiableAt_symm hw))

 theorem writtenNormal_derivative_eval (a : X) (x : X)
    (ha : x ∈ (chartAt (ℂ × ℂ) a).source) (hc : x ∈ c.chart.coordinates.source)
    (v : ℂ × ℂ) :
    fderiv ℂ (c.writtenNormal a) ((chartAt (ℂ × ℂ) a) x)
      (mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ) (chartAt (ℂ × ℂ) a) x v) =
      (mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ) c.chart.coordinates x v).2 := by
  have hwrite := c.writtenNormal_mdifferentiableAt a ((chartAt (ℂ × ℂ) a).map_source ha)
    (by rwa [(chartAt (ℂ × ℂ) a).left_inv ha])
  have heq : c.writtenNormal a ∘ (chartAt (ℂ × ℂ) a) =ᶠ[𝓝 x]
      fun y => (c.chart.coordinates y).2 := by
    filter_upwards [(chartAt (ℂ × ℂ) a).open_source.mem_nhds ha] with y hy
    change (c.chart.coordinates ((chartAt (ℂ × ℂ) a).symm ((chartAt (ℂ × ℂ) a) y))).2 = _
    rw [(chartAt (ℂ × ℂ) a).left_inv hy]
  have hd := heq.mfderiv_eq (I := 𝓘(ℂ, ℂ × ℂ)) (I' := 𝓘(ℂ, ℂ))
  rw [mfderiv_comp x hwrite ((mdifferentiable_chart a).mdifferentiableAt ha),
    mfderiv_eq_fderiv] at hd
  have hci := c.holomorphic.mdifferentiableAt (c.chart.coordinates.open_source.mem_nhds hc)
  have hproj : MDifferentiableAt 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ) Prod.snd (c.chart.coordinates x) :=
    mdifferentiableAt_iff_differentiableAt.mpr differentiableAt_snd
  have hsnd : mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ)
      (fun y : X => (c.chart.coordinates y).2) x =
      (ContinuousLinearMap.snd ℂ ℂ ℂ).comp
        (mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ) c.chart.coordinates x) := by
    change mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ) (Prod.snd ∘ c.chart.coordinates) x = _
    rw [mfderiv_comp x hproj hci, mfderiv_eq_fderiv, fderiv_snd]
  rw [hsnd] at hd
  exact congrArg (fun L : (ℂ × ℂ) →L[ℂ] ℂ => L v) hd

/-- Actual evaluation of a fixed local holomorphic normal covector on an
honest holomorphic ambient frame. -/
def frameScalarFunction (F : RawEmbeddedFrames D N T.bundle) (q : D.curve) : ℂ :=
  (mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ) c.chart.coordinates (D.inclusion q)
    (F.frame i q (0, 1))).2

 theorem frameScalarFunction_holomorphic (regularity : CoordinateCalculus.SurfaceAnalyticRegularity)
    (F : RawEmbeddedFrames D N T.bundle) (q : D.curve)
    (hi : q ∈ D.curve.chartDomain i) (hc : D.inclusion q ∈ c.chart.coordinates.source) :
    MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (c.frameScalarFunction F) q := by
  let a := D.inclusion q
  let w := (chartAt (ℂ × ℂ) a) a
  have ha : a ∈ (chartAt (ℂ × ℂ) a).source := mem_chart_source (ℂ × ℂ) a
  have ht := (chartAt (ℂ × ℂ) a).map_source ha
  have hto : Tendsto (chartAt (ℂ × ℂ) a).symm (𝓝 w) (𝓝 a) := by
    simpa only [(chartAt (ℂ × ℂ) a).left_inv ha] using
      ((chartAt (ℂ × ℂ) a).continuousAt_symm ht).tendsto
  have hY : AnalyticAt ℂ (c.writtenNormal a) w := by
    apply regularity
    filter_upwards [(chartAt (ℂ × ℂ) a).open_target.mem_nhds ht,
      hto (c.chart.coordinates.open_source.mem_nhds hc)] with z hz hcz
    exact mdifferentiableAt_iff_differentiableAt.mp (c.writtenNormal_mdifferentiableAt a hz hcz)
  have hinc := ((mdifferentiable_chart a).mdifferentiableAt ha).comp q (D.inclusion.holomorphic q)
  have hfield := (mdifferentiableAt_iff_differentiableAt.mpr hY.fderiv.differentiableAt).comp q hinc
  have hopen : IsOpen (D.curve.chartDomain i ∩ D.inclusion ⁻¹' (chartAt (ℂ × ℂ) a).source) :=
    (chartAt ℂ i).open_source.inter
      ((chartAt (ℂ × ℂ) a).open_source.preimage D.inclusion.holomorphic.continuous)
  have hframe := (F.holomorphic_in_ambient_charts i a (0, 1)).mdifferentiableAt
    (hopen.mem_nhds ⟨hi, ha⟩)
  have hvalue := hfield.clm_apply hframe
  apply hvalue.congr_of_eventuallyEq
  have hlocal : ∀ᶠ t in 𝓝 q, D.inclusion t ∈ (chartAt (ℂ × ℂ) a).source ∧
      D.inclusion t ∈ c.chart.coordinates.source := by
    exact D.inclusion.holomorphic.continuous.continuousAt
      (((chartAt (ℂ × ℂ) a).open_source.inter c.chart.coordinates.open_source).mem_nhds ⟨ha, hc⟩)
  filter_upwards [hlocal] with t ht
  exact (c.writtenNormal_derivative_eval a (D.inclusion t) ht.1 ht.2 (F.frame i t (0, 1))).symm

end Paper27.Geometry.RetractionCoefficientHolomorphic.CenteredChart

namespace Paper27.Geometry.RetractionCoordinateGerms.NormalAtlas
open RetractionCoefficientHolomorphic EmbeddedFrames NormalDegreeInvariance

variable {X : CompactComplexSurface} {D : EmbeddedCurve X} {U : D.Neighbourhood}
  {r₁ r₂ : D.Retraction U} {n : ℕ}
  {N : HolomorphicLineCocycle D.curve} {T : TangentLineCocycle D.curve}
  (A : RetractionCoordinateGerms.NormalAtlas D U r₁ r₂ n)
include A

/-- The intrinsic nth leading coefficient in an honest normal quotient frame.
Only its value outside the actual chart domain is made arbitrary. -/
def tensorCoefficient (F : RawEmbeddedFrames D N T.bundle) (i p : D.curve) : ℂ := by
  classical
  exact if hi : p ∈ D.curve.chartDomain i then (A.centered i p hi).frameScalar F ^ n else 0

 theorem tensorCoefficient_spec (F : RawEmbeddedFrames D N T.bundle)
    (i p : D.curve) (hi : p ∈ D.curve.chartDomain i) :
    A.tensorCoefficient F i p = (A.centered i p hi).frameScalar F ^ n := by
  classical
  simp only [tensorCoefficient, dif_pos hi]

 theorem tensorCoefficient_nonzero (F : RawEmbeddedFrames D N T.bundle)
    (i p : D.curve) (hi : p ∈ D.curve.chartDomain i) : A.tensorCoefficient F i p ≠ 0 := by
  rw [A.tensorCoefficient_spec F i p hi]
  exact pow_ne_zero n ((A.centered i p hi).frameScalar_ne_zero F hi)

/-- The actual linear normal transition and the actual retraction normal forms
produce the weighted leading law, with no global nth-root normalization. -/
 theorem tensorCoefficient_transition (F : RawEmbeddedFrames D N T.bundle) (hn : 0 < n)
    (i j p : D.curve) (hi : p ∈ D.curve.chartDomain i) (hj : p ∈ D.curve.chartDomain j) :
    A.tensorCoefficient F j p * N.transition i j p ^ n =
      T.bundle.transition i j p * A.tensorCoefficient F i p := by
  have h := congrArg (fun z : ℂ => z ^ n)
    ((A.centered i p hi).frameScalar_transition (A.centered j p hj) F hi hj)
  have hd : deriv (fun z => ((A.centered j p hj).chart.coordinates
      ((A.centered i p hi).slice z)).2) 0 = deriv (A.normal i j p) 0 := rfl
  dsimp only at h
  rw [mul_pow, mul_pow, hd, A.normal_power_leading hn i j p hi hj] at h
  rw [A.tensorCoefficient_spec F i p hi, A.tensorCoefficient_spec F j p hj,
    T.transition_eq i j p hi hj]
  exact h

/-- Choice independence holds even though the chart is selected independently
at every point. The normal scalar itself can change by a root of unity. -/
 theorem tensorCoefficient_independent_atlas
    (B : RetractionCoordinateGerms.NormalAtlas D U r₁ r₂ n)
    (F : RawEmbeddedFrames D N T.bundle) (hn : 0 < n)
    (i p : D.curve) (hi : p ∈ D.curve.chartDomain i) :
    B.tensorCoefficient F i p = A.tensorCoefficient F i p := by
  let c := A.centered i p hi
  let e := B.centered i p hi
  have hs := c.frameScalar_transition e F hi hi
  rw [N.self i p hi, mul_one] at hs
  have hroot := (rotation_germ hn (c.normal_analytic e).differentiableAt
    (c.normal_zero e) (c.comparison_germs e).1).1
  have h := congrArg (fun z : ℂ => z ^ n) hs
  dsimp only at h
  change deriv (fun z => (e.chart.coordinates (c.slice z)).2) 0 ^ n = 1 at hroot
  rw [mul_pow, hroot, one_mul] at h
  rw [A.tensorCoefficient_spec F i p hi, B.tensorCoefficient_spec F i p hi]
  exact h

 theorem tensorCoefficient_locally_fixed (F : RawEmbeddedFrames D N T.bundle) (hn : 0 < n)
    (i p : D.curve) (hi : p ∈ D.curve.chartDomain i) :
    A.tensorCoefficient F i =ᶠ[𝓝 p]
      fun q => (A.centered i p hi).frameScalarFunction F q ^ n := by
  have hsource : ∀ᶠ q in 𝓝 p, D.inclusion q ∈ (A.chart i p).coordinates.source :=
    D.inclusion.holomorphic.continuous.continuousAt
      ((A.chart i p).coordinates.open_source.mem_nhds (A.source_mem i p hi))
  filter_upwards [(chartAt ℂ i).open_source.mem_nhds hi, hsource] with q hqi hqs
  let c := (A.centered i p hi).recenter q hqs
  let e := A.centered i q hqi
  have hs := c.frameScalar_transition e F hqi hqi
  rw [N.self i q hqi, mul_one] at hs
  have hroot := (rotation_germ hn (c.normal_analytic e).differentiableAt
    (c.normal_zero e) (c.comparison_germs e).1).1
  have h := congrArg (fun z : ℂ => z ^ n) hs
  dsimp only at h
  change deriv (fun z => (e.chart.coordinates (c.slice z)).2) 0 ^ n = 1 at hroot
  rw [mul_pow, hroot, one_mul] at h
  rw [A.tensorCoefficient_spec F i q hqi]
  exact h

/-- The coefficient is holomorphic because locally one fixed actual dy is
applied to the actual holomorphic frame. No coefficient regularity is assumed. -/
 theorem tensorCoefficient_holomorphic
    (regularity : CoordinateCalculus.SurfaceAnalyticRegularity)
    (F : RawEmbeddedFrames D N T.bundle) (hn : 0 < n) (i : D.curve) :
    MDifferentiableOn 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (A.tensorCoefficient F i) (D.curve.chartDomain i) := by
  intro p hi
  have hc := (A.centered i p hi).frameScalarFunction_holomorphic regularity F p hi
    (A.source_mem i p hi)
  have hp : MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
      (fun q => (A.centered i p hi).frameScalarFunction F q ^ n) p := by
    have hpowers : ∀ m : ℕ, MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
        (fun q => (A.centered i p hi).frameScalarFunction F q ^ m) p := by
      intro m
      induction m with
      | zero => exact mdifferentiableAt_const
      | succ m ih => simpa only [pow_succ] using ih.mul hc
    exact hpowers n
  exact (hp.congr_of_eventuallyEq (A.tensorCoefficient_locally_fixed F hn i p hi)).mdifferentiableWithinAt

/-- The intrinsic normal tensor is constructed from actual maps, normalized
normal charts and honest adapted frames. Arbitrary tangent cross-terms of the
frames are allowed; no r-vertical-frame existence theorem is required. -/
def normalTensorGauge (regularity : CoordinateCalculus.SurfaceAnalyticRegularity)
    (F : RawEmbeddedFrames D N T.bundle) (hn : 0 < n) :
    HolomorphicLineGauge (N.tensorPower n) T.bundle where
  coefficient := A.tensorCoefficient F
  holomorphic := A.tensorCoefficient_holomorphic regularity F hn
  nonzero := A.tensorCoefficient_nonzero F
  compatible := A.tensorCoefficient_transition F hn

 theorem normal_tensor_degree (regularity : CoordinateCalculus.SurfaceAnalyticRegularity)
    (F : RawEmbeddedFrames D N T.bundle) (hn : 0 < n)
    (theory : LineBundleDegreeTheory) (invariance : LineBundleDegreeGaugeInvariance theory) :
    (n : ℤ) * theory.degree D.curve N = theory.degree D.curve T.bundle := by
  rw [← theory.tensor_power D.curve N n]
  exact invariance D.curve (N.tensorPower n) T.bundle (A.normalTensorGauge regularity F hn)

 theorem normal_degree_negative (regularity : CoordinateCalculus.SurfaceAnalyticRegularity)
    (F : RawEmbeddedFrames D N T.bundle) (hn : 0 < n)
    (theory : LineBundleDegreeTheory) (invariance : LineBundleDegreeGaugeInvariance theory)
    (hg : D.curve.Hyperbolic) : theory.degree D.curve N < 0 := by
  have hdegree := A.normal_tensor_degree regularity F hn theory invariance
  rw [theory.tangent_degree D.curve T] at hdegree
  have hg' : (2 : ℤ) ≤ D.curve.genus := by exact_mod_cast hg
  have hn' : (0 : ℤ) < n := by exact_mod_cast hn
  have hnegative : (n : ℤ) * theory.degree D.curve N < 0 := by omega
  by_contra h
  exact (not_lt_of_ge (mul_nonneg (le_of_lt hn') (le_of_not_gt h))) hnegative

 theorem normal_hom_degree_negative (regularity : CoordinateCalculus.SurfaceAnalyticRegularity)
    (F : RawEmbeddedFrames D N T.bundle) (hn : 2 ≤ n)
    (theory : LineBundleDegreeTheory) (invariance : LineBundleDegreeGaugeInvariance theory)
    (homLaw : HomDegreeLaw theory) (hg : D.curve.Hyperbolic)
    (H : HomLineCocycle N T.bundle) : theory.degree D.curve H.bundle < 0 :=
  normal_hom_degree theory homLaw D.curve N T.bundle H n hn
    (A.normal_degree_negative regularity F (by omega) theory invariance hg)
    (A.normal_tensor_degree regularity F (by omega) theory invariance)

/-- Package the actual constructed tensor isomorphism and the very same
honest frames for the intrinsic component dichotomy. -/
def componentNormalTensorData (regularity : CoordinateCalculus.SurfaceAnalyticRegularity)
    (F : RawEmbeddedFrames D N T.bundle) (hn : 2 ≤ n) : ComponentNormalTensorData D where
  normal := N
  tangent := T
  exponent := n
  exponent_ge_two := hn
  frames := F
  tensorGauge := A.normalTensorGauge regularity F (by omega)

end Paper27.Geometry.RetractionCoordinateGerms.NormalAtlas
