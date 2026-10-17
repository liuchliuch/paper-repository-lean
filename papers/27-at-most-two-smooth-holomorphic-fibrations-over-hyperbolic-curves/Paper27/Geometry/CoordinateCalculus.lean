import Paper27.Geometry.Objects
import Paper27.Geometry.NormalizedDifferentials
import Paper27.Geometry.RamificationSupport
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Actual coordinate expressions and their differential transport

This file supplies coordinate calculations for actual holomorphic maps, rather
than treating local covectors as unconstrained labels. The coordinate changes
are the actual manifold charts. Their derivatives are invertible by mathlib,
and the derivative of a map in these charts is obtained by the chain rule.
-/
noncomputable section
open scoped Manifold Topology
open Filter
namespace Paper27.Geometry.CoordinateCalculus

section General
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  {M : CompactComplexManifold E} {N : CompactComplexManifold F}

/-- The actual expression of a map in two fixed charts. -/
def coordinateMap (f : HolomorphicMap M N) (a : M) (b : N) : E → F :=
  (chartAt F b) ∘ f ∘ (chartAt E a).symm

/-- The chain-rule hypotheses at any point in the fixed coordinate domains. -/
theorem coordinateMap_mdifferentiableAt (f : HolomorphicMap M N) (a : M) (b : N)
    {z : E} (hz : z ∈ (chartAt E a).target)
    (hb : f ((chartAt E a).symm z) ∈ (chartAt F b).source) :
    MDifferentiableAt 𝓘(ℂ, E) 𝓘(ℂ, F) (coordinateMap f a b) z := by
  exact ((mdifferentiable_chart b).mdifferentiableAt hb).comp z
    ((f.holomorphic _).comp z ((mdifferentiable_chart a).mdifferentiableAt_symm hz))

/-- The complete actual derivative transport formula in fixed charts. -/
theorem coordinateMap_derivative (f : HolomorphicMap M N) (a : M) (b : N)
    {z : E} (hz : z ∈ (chartAt E a).target)
    (hb : f ((chartAt E a).symm z) ∈ (chartAt F b).source) :
    fderiv ℂ (coordinateMap f a b) z =
      (mfderiv 𝓘(ℂ, F) 𝓘(ℂ, F) (chartAt F b) (f ((chartAt E a).symm z))).comp
        ((mfderiv 𝓘(ℂ, E) 𝓘(ℂ, F) f ((chartAt E a).symm z)).comp
          (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E) (chartAt E a).symm z)) := by
  rw [← mfderiv_eq_fderiv]
  unfold coordinateMap
  rw [mfderiv_comp z ((mdifferentiable_chart b).mdifferentiableAt hb)
    ((f.holomorphic _).comp z ((mdifferentiable_chart a).mdifferentiableAt_symm hz)),
    mfderiv_comp z (f.holomorphic _) ((mdifferentiable_chart a).mdifferentiableAt_symm hz)]
  rfl

/-- Chart restrictions and continuity give an actual neighbourhood of the
centre where both fixed chart expressions can be differentiated. -/
theorem coordinateMap_eventually_domains (f : HolomorphicMap M N) (a : M) :
    ∀ᶠ z in 𝓝 ((chartAt E a) a), z ∈ (chartAt E a).target ∧
      f ((chartAt E a).symm z) ∈ (chartAt F (f a)).source := by
  have ha : a ∈ (chartAt E a).source := mem_chart_source E a
  have htarget := (chartAt E a).open_target.mem_nhds ((chartAt E a).map_source ha)
  have hf : ContinuousAt (f ∘ (chartAt E a).symm) ((chartAt E a) a) := by
    apply f.holomorphic.continuous.continuousAt.comp
    exact (chartAt E a).continuousAt_symm ((chartAt E a).map_source ha)
  have hval : (f ∘ (chartAt E a).symm) ((chartAt E a) a) = f a := by
    simp only [Function.comp_apply, (chartAt E a).left_inv ha]
  have hbase := (chartAt F (f a)).open_source.mem_nhds (mem_chart_source F (f a))
  have hforward : Tendsto (f ∘ (chartAt E a).symm) (𝓝 ((chartAt E a) a)) (𝓝 (f a)) := by
    simpa only [hval] using hf.tendsto
  filter_upwards [htarget, hforward hbase] with z hz hb
  exact ⟨hz, hb⟩

/-- Actual coordinate maps are complex differentiable on a neighbourhood of
the centre; in one source dimension, mathlib upgrades this to analyticity. -/
theorem coordinateMap_eventually_differentiable (f : HolomorphicMap M N) (a : M) :
    ∀ᶠ z in 𝓝 ((chartAt E a) a), DifferentiableAt ℂ (coordinateMap f a (f a)) z := by
  filter_upwards [coordinateMap_eventually_domains f a] with z hz
  exact mdifferentiableAt_iff_differentiableAt.mp
    (coordinateMap_mdifferentiableAt f a (f a) hz.1 hz.2)

end General

/-- The source is a curve, so analyticity follows from the already formalized
one-variable Cauchy theorem, even when the target is a surface. -/
theorem curve_coordinateMap_analytic {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [CompleteSpace F] {D : Curve} {N : CompactComplexManifold F}
    (f : HolomorphicMap D N) (p : D) :
    AnalyticAt ℂ (coordinateMap f p (f p)) ((chartAt ℂ p) p) :=
  Complex.analyticAt_iff_eventually_differentiableAt.mpr (coordinateMap_eventually_differentiable f p)

/-- A change of source and two target frames preserves joint surjectivity.
This is the precise linear algebra needed to transport ramification. -/
theorem joint_surjective_iff (L₁ L₂ : (ℂ × ℂ) →L[ℂ] ℂ)
    (A : (ℂ × ℂ) ≃L[ℂ] (ℂ × ℂ)) (B C : ℂ ≃L[ℂ] ℂ) :
    Function.Surjective (fun v => (B (L₁ (A v)), C (L₂ (A v)))) ↔
      Function.Surjective (fun v => (L₁ v, L₂ v)) := by
  constructor
  · intro h ab
    obtain ⟨v, hv⟩ := h (B ab.1, C ab.2)
    exact ⟨A v, Prod.ext (B.injective (congrArg Prod.fst hv))
      (C.injective (congrArg Prod.snd hv))⟩
  · intro h ab
    obtain ⟨v, hv⟩ := h (B.symm ab.1, C.symm ab.2)
    refine ⟨A.symm v, ?_⟩
    apply Prod.ext
    · simpa only [A.apply_symm_apply, B.apply_symm_apply] using congrArg B (congrArg Prod.fst hv)
    · simpa only [A.apply_symm_apply, C.apply_symm_apply] using congrArg C (congrArg Prod.snd hv)

section IndividualTransport

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  {M : CompactComplexManifold E} {N : CompactComplexManifold F}

/-- Evaluating the actual coordinate expression at its centre. -/
theorem coordinateMap_center (f : HolomorphicMap M N) (a : M) :
    coordinateMap f a (f a) ((chartAt E a) a) = (chartAt F (f a)) (f a) := by
  simp only [coordinateMap, Function.comp_apply,
    (chartAt E a).left_inv (mem_chart_source E a)]

/-- Surjectivity of the actual differential is unchanged in any fixed pair of
valid charts, because both chart derivatives are actual linear equivalences. -/
theorem coordinateMap_surjective_iff (f : HolomorphicMap M N) (a : M) (b : N)
    {z : E} (hz : z ∈ (chartAt E a).target)
    (hb : f ((chartAt E a).symm z) ∈ (chartAt F b).source) :
    Function.Surjective (fderiv ℂ (coordinateMap f a b) z) ↔
      Function.Surjective (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, F) f ((chartAt E a).symm z)) := by
  let A : E ≃L[ℂ] E :=
    (mdifferentiable_chart (I := 𝓘(ℂ, E)) a).symm.mfderiv hz
  let B : F ≃L[ℂ] F := (mdifferentiable_chart (I := 𝓘(ℂ, F)) b).mfderiv hb
  let L := mfderiv 𝓘(ℂ, E) 𝓘(ℂ, F) f ((chartAt E a).symm z)
  rw [coordinateMap_derivative f a b hz hb]
  change Function.Surjective (fun v => B (L (A v))) ↔ Function.Surjective L
  constructor
  · intro h y
    obtain ⟨v, hv⟩ := h (B y)
    exact ⟨A v, B.injective hv⟩
  · intro h y
    obtain ⟨v, hv⟩ := h (B.symm y)
    refine ⟨A.symm v, ?_⟩
    simpa only [A.apply_symm_apply, B.apply_symm_apply] using congrArg B hv

/-- The centre version is the individual smoothness transport used below. -/
theorem coordinateMap_center_surjective_iff (f : HolomorphicMap M N) (a : M) :
    Function.Surjective (fderiv ℂ (coordinateMap f a (f a)) ((chartAt E a) a)) ↔
      Function.Surjective (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, F) f a) := by
  have ha := mem_chart_source E a
  have hb : f ((chartAt E a).symm ((chartAt E a) a)) ∈ (chartAt F (f a)).source := by
    rw [(chartAt E a).left_inv ha]
    exact mem_chart_source F (f a)
  have h := coordinateMap_surjective_iff f a (f a) ((chartAt E a).map_source ha) hb
  have heq := congrArg
    (fun q : M => Function.Surjective (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, F) f q))
    ((chartAt E a).left_inv ha)
  exact h.trans (Iff.of_eq heq)

end IndividualTransport

section Pairs

variable {X : CompactComplexSurface}

/-- The actual holomorphic map underlying a fibration. -/
def fibrationMap (f : Fibration X) : HolomorphicMap X f.base where
  toFun := f.map
  holomorphic := f.holomorphic

/-- The actual paired manifold differential is the product of the two actual
component differentials. -/
theorem pairMap_mfderiv (f g : Fibration X) (q : X) :
    mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ) (RamificationSupport.pairMap f g) q =
      (mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ) f q).prod
        (mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ) g q) := by
  simpa only [← modelWithCornersSelf_prod] using
    (f.holomorphic q).mfderiv_prod (g.holomorphic q)

/-- The ramification definition's actual paired map is equivalent to the two
actual covectors, with no independent ramification label. -/
theorem pairMap_surjective_iff (f g : Fibration X) (q : X) :
    Function.Surjective
      (mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ) (RamificationSupport.pairMap f g) q) ↔
    Function.Surjective (fun v =>
      (mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ) f q v,
        mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ) g q v)) := by
  rw [pairMap_mfderiv]
  rfl

/-- Joint surjectivity in the fixed actual surface and base charts is precisely
surjectivity of the actual manifold differential of the actual pair. -/
theorem coordinate_pair_surjective_iff (f g : Fibration X) (a : X)
    (b : f.base) (c : g.base) {z : ℂ × ℂ}
    (hz : z ∈ (chartAt (ℂ × ℂ) a).target)
    (hb : f ((chartAt (ℂ × ℂ) a).symm z) ∈ (chartAt ℂ b).source)
    (hc : g ((chartAt (ℂ × ℂ) a).symm z) ∈ (chartAt ℂ c).source) :
    Function.Surjective (fun v =>
      (fderiv ℂ (coordinateMap (fibrationMap f) a b) z v,
        fderiv ℂ (coordinateMap (fibrationMap g) a c) z v)) ↔
      Function.Surjective (mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ)
        (RamificationSupport.pairMap f g) ((chartAt (ℂ × ℂ) a).symm z)) := by
  let A : (ℂ × ℂ) ≃L[ℂ] (ℂ × ℂ) :=
    (mdifferentiable_chart (I := 𝓘(ℂ, ℂ × ℂ)) a).symm.mfderiv hz
  let B : ℂ ≃L[ℂ] ℂ := (mdifferentiable_chart (I := 𝓘(ℂ, ℂ)) b).mfderiv hb
  let C : ℂ ≃L[ℂ] ℂ := (mdifferentiable_chart (I := 𝓘(ℂ, ℂ)) c).mfderiv hc
  rw [coordinateMap_derivative (fibrationMap f) a b hz hb,
    coordinateMap_derivative (fibrationMap g) a c hz hc]
  change Function.Surjective (fun v =>
      (B (mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ) f ((chartAt (ℂ × ℂ) a).symm z) (A v)),
        C (mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ) g ((chartAt (ℂ × ℂ) a).symm z) (A v)))) ↔ _
  exact (joint_surjective_iff _ _ A B C).trans (pairMap_surjective_iff f g _).symm

/-- The actual restricted holomorphic curve map, not a separate supplied map. -/
def restrictedMap {D : Curve} (f : Fibration X) (ν : HolomorphicMap D X) :
    HolomorphicMap D f.base where
  toFun := fun p => f (ν p)
  holomorphic := f.holomorphic.comp ν.holomorphic

/-- Inserting the normalization coordinate into the ambient coordinate map
recovers the actual written coordinate of the restricted map as a germ. -/
theorem restricted_coordinate_comp_germ {D : Curve} (f : Fibration X)
    (ν : HolomorphicMap D X) (p : D) :
    MetricComparison.writtenCoordinateMap (restrictedMap f ν) p =ᶠ[𝓝 ((chartAt ℂ p) p)]
      coordinateMap (fibrationMap f) (ν p) (f (ν p)) ∘ coordinateMap ν p (ν p) := by
  filter_upwards [coordinateMap_eventually_domains ν p] with z hz
  change (chartAt ℂ (f (ν p))) (f (ν ((chartAt ℂ p).symm z))) =
    (chartAt ℂ (f (ν p)))
      (f ((chartAt (ℂ × ℂ) (ν p)).symm
        ((chartAt (ℂ × ℂ) (ν p)) (ν ((chartAt ℂ p).symm z)))))
  rw [(chartAt (ℂ × ℂ) (ν p)).left_inv hz.2]

/-- Actual image containment in the actual ramification set yields eventual
joint non-surjectivity in the actual fixed coordinates. -/
theorem normalization_joint_not_surjective {D : Curve} (f g : Fibration X)
    (ν : HolomorphicMap D X)
    (himage : ∀ p : D, ν p ∈ RamificationSupport.ramificationSet f g) (p : D) :
    ∀ᶠ z in 𝓝 ((chartAt ℂ p) p), ¬ Function.Surjective (fun v =>
      (fderiv ℂ (coordinateMap (fibrationMap f) (ν p) (f (ν p)))
        (coordinateMap ν p (ν p) z) v,
      fderiv ℂ (coordinateMap (fibrationMap g) (ν p) (g (ν p)))
        (coordinateMap ν p (ν p) z) v)) := by
  filter_upwards [coordinateMap_eventually_domains ν p,
    coordinateMap_eventually_domains (restrictedMap f ν) p,
    coordinateMap_eventually_domains (restrictedMap g ν) p] with z hν hf hg
  have hleft : (chartAt (ℂ × ℂ) (ν p)).symm (coordinateMap ν p (ν p) z) =
      ν ((chartAt ℂ p).symm z) :=
    (chartAt (ℂ × ℂ) (ν p)).left_inv hν.2
  have hz : coordinateMap ν p (ν p) z ∈ (chartAt (ℂ × ℂ) (ν p)).target :=
    (chartAt (ℂ × ℂ) (ν p)).map_source hν.2
  have hb : f ((chartAt (ℂ × ℂ) (ν p)).symm (coordinateMap ν p (ν p) z)) ∈
      (chartAt ℂ (f (ν p))).source := by
    rw [hleft]
    exact hf.2
  have hc : g ((chartAt (ℂ × ℂ) (ν p)).symm (coordinateMap ν p (ν p) z)) ∈
      (chartAt ℂ (g (ν p))).source := by
    rw [hleft]
    exact hg.2
  have hram : ¬ Function.Surjective (mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ)
      (RamificationSupport.pairMap f g)
        ((chartAt (ℂ × ℂ) (ν p)).symm (coordinateMap ν p (ν p) z))) := by
    rw [hleft]
    exact himage ((chartAt ℂ p).symm z)
  exact (coordinate_pair_surjective_iff f g (ν p) (f (ν p)) (g (ν p)) hz hb hc).not.mpr hram

end Pairs

/-- Universal several-variable holomorphic regularity, used only in source
complex dimension two. This is the power-series representation theorem in
J. Lebl, Tasty Bits of Several Complex Variables, version 4.4, Theorem 1.2.1,
printed p.20, https://www.jirka.org/scv/scv.pdf . It mentions no fibration,
normalization, pair, scalar relation, or ramification conclusion. -/
def SurfaceAnalyticRegularity : Prop :=
  ∀ (F : (ℂ × ℂ) → ℂ) (p : ℂ × ℂ),
    (∀ᶠ q in 𝓝 p, DifferentiableAt ℂ F q) → AnalyticAt ℂ F p

section NormalizationData

variable {X : CompactComplexSurface} {D : Curve}

/-- The actual analytic local data are obtained from the manifold maps, their
smoothness, and actual image containment in the ramification set. -/
theorem normalized_actual_covector_data (regularity : SurfaceAnalyticRegularity)
    (f g : Fibration X) (hf : f.Smooth) (hg : g.Smooth) (ν : HolomorphicMap D X)
    (himage : ∀ p : D, ν p ∈ RamificationSupport.ramificationSet f g) (p : D) :
    NormalizedDifferentials.ActualCovectorData
      (coordinateMap (fibrationMap f) (ν p) (f (ν p)))
      (coordinateMap (fibrationMap g) (ν p) (g (ν p)))
      (coordinateMap ν p (ν p)) ((chartAt ℂ p) p) := by
  have hF : AnalyticAt ℂ (coordinateMap (fibrationMap f) (ν p) (f (ν p)))
      (coordinateMap ν p (ν p) ((chartAt ℂ p) p)) := by
    rw [coordinateMap_center]
    exact regularity _ _ (coordinateMap_eventually_differentiable (fibrationMap f) (ν p))
  have hG : AnalyticAt ℂ (coordinateMap (fibrationMap g) (ν p) (g (ν p)))
      (coordinateMap ν p (ν p) ((chartAt ℂ p) p)) := by
    rw [coordinateMap_center]
    exact regularity _ _ (coordinateMap_eventually_differentiable (fibrationMap g) (ν p))
  have hν := curve_coordinateMap_analytic ν p
  have hsF : Function.Surjective
      (fderiv ℂ (coordinateMap (fibrationMap f) (ν p) (f (ν p)))
        (coordinateMap ν p (ν p) ((chartAt ℂ p) p))) := by
    rw [coordinateMap_center]
    exact (coordinateMap_center_surjective_iff (fibrationMap f) (ν p)).mpr (hf (ν p))
  have hsG : Function.Surjective
      (fderiv ℂ (coordinateMap (fibrationMap g) (ν p) (g (ν p)))
        (coordinateMap ν p (ν p) ((chartAt ℂ p) p))) := by
    rw [coordinateMap_center]
    exact (coordinateMap_center_surjective_iff (fibrationMap g) (ν p)).mpr (hg (ν p))
  exact NormalizedDifferentials.actual_covector_data hF hG hν hsF hsG
    (normalization_joint_not_surjective f g ν himage p)

/-- The complete raw data for the actual two restricted curve maps are
constructed, including their chain rules in actual written coordinates. -/
def normalizedCurveCovectorData (regularity : SurfaceAnalyticRegularity)
    (f g : Fibration X) (hf : f.Smooth) (hg : g.Smooth) (ν : HolomorphicMap D X)
    (himage : ∀ p : D, ν p ∈ RamificationSupport.ramificationSet f g) :
    CovectorGauges.CurveCovectorData (restrictedMap f ν) (restrictedMap g ν) where
  A₁ p := NormalizedDifferentials.coefficientOne
    (coordinateMap (fibrationMap f) (ν p) (f (ν p))) (coordinateMap ν p (ν p))
  A₂ p := NormalizedDifferentials.coefficientTwo
    (coordinateMap (fibrationMap f) (ν p) (f (ν p))) (coordinateMap ν p (ν p))
  B₁ p := NormalizedDifferentials.coefficientOne
    (coordinateMap (fibrationMap g) (ν p) (g (ν p))) (coordinateMap ν p (ν p))
  B₂ p := NormalizedDifferentials.coefficientTwo
    (coordinateMap (fibrationMap g) (ν p) (g (ν p))) (coordinateMap ν p (ν p))
  t₁ p := NormalizedDifferentials.tangentOne (coordinateMap ν p (ν p))
  t₂ p := NormalizedDifferentials.tangentTwo (coordinateMap ν p (ν p))
  analytic_A₁ p := (normalized_actual_covector_data regularity f g hf hg ν himage p).analytic_A₁
  analytic_A₂ p := (normalized_actual_covector_data regularity f g hf hg ν himage p).analytic_A₂
  analytic_B₁ p := (normalized_actual_covector_data regularity f g hf hg ν himage p).analytic_B₁
  analytic_B₂ p := (normalized_actual_covector_data regularity f g hf hg ν himage p).analytic_B₂
  nonzero_A p := (normalized_actual_covector_data regularity f g hf hg ν himage p).nonzero_A
  nonzero_B p := (normalized_actual_covector_data regularity f g hf hg ν himage p).nonzero_B
  determinant_zero p :=
    (normalized_actual_covector_data regularity f g hf hg ν himage p).determinant_zero
  chain_u p := (restricted_coordinate_comp_germ f ν p).deriv.trans
    (normalized_actual_covector_data regularity f g hf hg ν himage p).chain_F
  chain_v p := (restricted_coordinate_comp_germ g ν p).deriv.trans
    (normalized_actual_covector_data regularity f g hf hg ν himage p).chain_G

/-- The actual derivative-zero orders of both actual restricted curve maps
agree, with no supplied equality of ramification divisors. -/
theorem normalized_ramification_orders_equal (regularity : SurfaceAnalyticRegularity)
    (f g : Fibration X) (hf : f.Smooth) (hg : g.Smooth) (ν : HolomorphicMap D X)
    (himage : ∀ p : D, ν p ∈ RamificationSupport.ramificationSet f g) :
    ∀ p : D, MetricComparison.ramificationOrder (restrictedMap f ν) p =
      MetricComparison.ramificationOrder (restrictedMap g ν) p := by
  have data := normalizedCurveCovectorData regularity f g hf hg ν himage
  intro p
  apply (data.ramification_orders_equal _ p).symm
  intro q
  exact (curve_coordinateMap_analytic (restrictedMap f ν) q).deriv

/-- With the ordinary finite-support proofs, the actual effective
ramification divisors themselves are equal. -/
theorem normalized_ramification_divisors_equal (regularity : SurfaceAnalyticRegularity)
    (f g : Fibration X) (hf : f.Smooth) (hg : g.Smooth) (ν : HolomorphicMap D X)
    (himage : ∀ p : D, ν p ∈ RamificationSupport.ramificationSet f g)
    (hR₁ : MetricComparison.RamificationSupportFinite (restrictedMap f ν))
    (hR₂ : MetricComparison.RamificationSupportFinite (restrictedMap g ν)) :
    MetricComparison.ramificationDivisor (restrictedMap f ν) hR₁ =
      MetricComparison.ramificationDivisor (restrictedMap g ν) hR₂ := by
  ext p
  exact normalized_ramification_orders_equal regularity f g hf hg ν himage p

/-- The complete initial normalization comparison: finite pair fibres give one
nonconstant restriction, the constructed actual gauges give the other, and the
actual ramification orders agree. The only constancy input is the universally
quantified classical zero-differential theorem. -/
theorem normalized_nonconstant_and_same_ramification
    (regularity : SurfaceAnalyticRegularity) (maps : MetricComparison.ClassicalCurveMapFacts)
    (constant : CovectorGauges.ClassicalZeroDifferentialConstancy)
    (f g : Fibration X) (hf : f.Smooth) (hg : g.Smooth) (ν : HolomorphicMap D X)
    (himage : ∀ p : D, ν p ∈ RamificationSupport.ramificationSet f g)
    (hfinite : Fibration.FinitePair f g) (hν : ∃ p q : D, ν p ≠ ν q) :
    MetricComparison.Nonconstant (restrictedMap f ν) ∧
      MetricComparison.Nonconstant (restrictedMap g ν) ∧
      ∀ p, MetricComparison.ramificationOrder (restrictedMap f ν) p =
        MetricComparison.ramificationOrder (restrictedMap g ν) p := by
  have data := normalizedCurveCovectorData regularity f g hf hg ν himage
  have hone : MetricComparison.Nonconstant (restrictedMap f ν) ∨
      MetricComparison.Nonconstant (restrictedMap g ν) :=
    RamificationCovectors.one_projection_nonconstant D ν f g hfinite hν
  exact data.nonconstant_and_same_ramification maps constant hone

/-- The actual-object chain from a nonconstant normalization in the actual
ramification set to both nonconstant restrictions, the common actual divisor,
hyperbolicity of the source, and equality of the actual pulled-back metrics.
Only the separately named universal classical theorems are parameters. -/
theorem normalized_comparison_complete
    (regularity : SurfaceAnalyticRegularity) (maps : MetricComparison.ClassicalCurveMapFacts)
    (constant : CovectorGauges.ClassicalZeroDifferentialConstancy)
    (pullbacks : MetricComparison.ClassicalPullbackFacts)
    (unique : MetricComparison.TroyanovUniqueness)
    (f g : Fibration X) (hf : f.Smooth) (hg : g.Smooth) (hB : f.Hyperbolic)
    (ν : HolomorphicMap D X)
    (himage : ∀ p : D, ν p ∈ RamificationSupport.ramificationSet f g)
    (hfinite : Fibration.FinitePair f g) (hν : ∃ p q : D, ν p ≠ ν q)
    (gB : MetricComparison.ConformalMetric f.base)
    (gC : MetricComparison.ConformalMetric g.base)
    (hBcone : MetricComparison.HasConeData gB 0)
    (hCcone : MetricComparison.HasConeData gC 0)
    (hBcurv : MetricComparison.HasConstantCurvature gB 0 (-1))
    (hCcurv : MetricComparison.HasConstantCurvature gC 0 (-1)) :
    MetricComparison.Nonconstant (restrictedMap f ν) ∧
      MetricComparison.Nonconstant (restrictedMap g ν) ∧ D.Hyperbolic ∧
      (∀ p, MetricComparison.ramificationOrder (restrictedMap f ν) p =
        MetricComparison.ramificationOrder (restrictedMap g ν) p) ∧
      (∃ (hR₁ : MetricComparison.RamificationSupportFinite (restrictedMap f ν))
        (hR₂ : MetricComparison.RamificationSupportFinite (restrictedMap g ν)),
        MetricComparison.ramificationDivisor (restrictedMap f ν) hR₁ =
          MetricComparison.ramificationDivisor (restrictedMap g ν) hR₂) ∧
      MetricComparison.pullback (restrictedMap f ν) gB =
        MetricComparison.pullback (restrictedMap g ν) gC := by
  obtain ⟨hu, hv, hR⟩ := normalized_nonconstant_and_same_ramification regularity maps
    constant f g hf hg ν himage hfinite hν
  have hD : D.Hyperbolic := MetricComparison.source_hyperbolic maps (restrictedMap f ν) hu hB
  have hR₁ := maps.ramification_finite D f.base (restrictedMap f ν) hu
  have hR₂ := maps.ramification_finite D g.base (restrictedMap g ν) hv
  refine ⟨hu, hv, hD, hR, ⟨hR₁, hR₂, ?_⟩, ?_⟩
  · exact MetricComparison.same_ramification_divisor _ _ hR₁ hR₂ hR
  · exact MetricComparison.pullback_metrics_equal maps pullbacks unique
      (restrictedMap f ν) (restrictedMap g ν) hu hv hB gB gC hBcone hCcone hBcurv hCcurv hR

end NormalizationData

end Paper27.Geometry.CoordinateCalculus
