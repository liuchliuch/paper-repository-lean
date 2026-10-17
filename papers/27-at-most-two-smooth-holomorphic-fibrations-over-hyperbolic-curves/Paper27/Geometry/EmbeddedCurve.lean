import Paper27.Geometry.CoordinateCalculus
import Paper27.Geometry.NormalQuotient
import Paper27.Geometry.CyclicModel

/-!
# Actual embedded compact curves and differential bridges

An embedded curve has an actual compact complex curve as source, an actual
holomorphic inclusion, the topological embedding property, and injective
actual manifold differential. Restrictions, tangency to the actual paired
ramification set, and adapted tangent frames are defined from those maps.
No normal tensor identity, correction vanishing, or fibration bound is included
in the definitions or in an external interface.
-/

noncomputable section

open scoped Manifold Topology

namespace Paper27.Geometry

structure EmbeddedCurve (X : CompactComplexSurface) where
  curve : Curve
  inclusion : HolomorphicMap curve X
  embedding : Topology.IsEmbedding inclusion
  immersion : ∀ p : curve, Function.Injective
    (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ × ℂ) inclusion p)

namespace EmbeddedCurve

variable {X : CompactComplexSurface}

def support (D : EmbeddedCurve X) : Set X := Set.range D.inclusion

def restrictedMap (D : EmbeddedCurve X) (f : Fibration X) : HolomorphicMap D.curve f.base :=
  CoordinateCalculus.restrictedMap f D.inclusion

def Unramified (D : EmbeddedCurve X) (f : Fibration X) : Prop :=
  ∀ p : D.curve, Function.Bijective (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (D.restrictedMap f) p)

def TangentToPair (D : EmbeddedCurve X) (f g : Fibration X) : Prop :=
  D.support ⊆ RamificationSupport.ramificationSet f g

def DisjointFromPair (D : EmbeddedCurve X) (f g : Fibration X) : Prop :=
  Disjoint D.support (RamificationSupport.ramificationSet f g)

@[simp] theorem restrictedMap_apply (D : EmbeddedCurve X) (f : Fibration X) (p : D.curve) :
    D.restrictedMap f p = f (D.inclusion p) := rfl

theorem restrictedMap_mfderiv (D : EmbeddedCurve X) (f : Fibration X) (p : D.curve) :
    mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (D.restrictedMap f) p =
      (mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ) f (D.inclusion p)).comp
        (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ × ℂ) D.inclusion p) :=
  mfderiv_comp p (f.holomorphic _) (D.inclusion.holomorphic p)

theorem restrictedMap_mfderiv_apply (D : EmbeddedCurve X) (f : Fibration X)
    (p : D.curve) (v : ℂ) :
    mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (D.restrictedMap f) p v =
      mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ) f (D.inclusion p)
        (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ × ℂ) D.inclusion p v) := by
  rw [D.restrictedMap_mfderiv]
  rfl

/-- The actual preferred-coordinate derivative coefficient of the restriction. -/
def restrictionDifferential (D : EmbeddedCurve X) (f : Fibration X) (p : D.curve) :
    ℂ →L[ℂ] ℂ := mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (D.restrictedMap f) p

def restrictionCoefficient (D : EmbeddedCurve X) (f : Fibration X) (p : D.curve) : ℂ :=
  D.restrictionDifferential f p (1 : ℂ)

theorem restrictedMap_mfderiv_scalar (D : EmbeddedCurve X) (f : Fibration X)
    (p : D.curve) (z : ℂ) :
    mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (D.restrictedMap f) p z =
      D.restrictionCoefficient f p * z := by
  let L : ℂ →L[ℂ] ℂ := mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (D.restrictedMap f) p
  change L z = L 1 * z
  calc
    L z = L (z • (1 : ℂ)) := by simp
    _ = z * L 1 := by rw [map_smul, smul_eq_mul]
    _ = L 1 * z := mul_comm _ _

theorem restriction_bijective_iff_coefficient_ne_zero (D : EmbeddedCurve X)
    (f : Fibration X) (p : D.curve) :
    Function.Bijective (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (D.restrictedMap f) p) ↔
      D.restrictionCoefficient f p ≠ 0 := by
  change Function.Bijective (D.restrictionDifferential f p) ↔ _
  constructor
  · intro h hz
    have h10 : (1 : ℂ) = 0 := h.1 (by simpa only [restrictionCoefficient, map_zero] using hz)
    exact one_ne_zero h10
  · intro hc
    constructor
    · intro a b hab
      apply mul_left_cancel₀ hc
      exact (D.restrictedMap_mfderiv_scalar f p a).symm.trans
        (hab.trans (D.restrictedMap_mfderiv_scalar f p b))
    · intro y
      refine ⟨y / D.restrictionCoefficient f p, ?_⟩
      change mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (D.restrictedMap f) p _ = y
      rw [D.restrictedMap_mfderiv_scalar]
      exact mul_div_cancel₀ y hc

theorem unramified_iff_coefficient_ne_zero (D : EmbeddedCurve X) (f : Fibration X) :
    D.Unramified f ↔ ∀ p : D.curve, D.restrictionCoefficient f p ≠ 0 := by
  unfold Unramified
  exact forall_congr' fun p => D.restriction_bijective_iff_coefficient_ne_zero f p

/-- An actual open neighbourhood containing the whole embedded curve. -/
structure Neighbourhood (D : EmbeddedCurve X) where
  domain : Set X
  open_domain : IsOpen domain
  contains : ∀ p : D.curve, D.inclusion p ∈ domain

/-- An actual holomorphic retraction on the specified open neighbourhood. Its
arbitrary extension outside that neighbourhood has no regularity requirement. -/
structure Retraction (D : EmbeddedCurve X) (U : D.Neighbourhood) where
  toFun : X → D.curve
  holomorphic : MDifferentiableOn 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ) toFun U.domain
  retract : ∀ p : D.curve, toFun (D.inclusion p) = p

/-- An actual rank-two tangent frame adapted to the actual inclusion tangent
line. The tangent coordinate frame is also an actual linear equivalence. -/
structure TangentFrame (D : EmbeddedCurve X) (p : D.curve) where
  ambient : (ℂ × ℂ) ≃L[ℂ] TangentSpace 𝓘(ℂ, ℂ × ℂ) (D.inclusion p)
  tangent : ℂ ≃L[ℂ] TangentSpace 𝓘(ℂ, ℂ) p
  adapted : ∀ z : ℂ, ambient (z, 0) =
    mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ × ℂ) D.inclusion p (tangent z)

namespace TangentFrame

variable {D : EmbeddedCurve X} {p : D.curve}

def normalCoordinate (A : D.TangentFrame p) :
    TangentSpace 𝓘(ℂ, ℂ × ℂ) (D.inclusion p) →L[ℂ] ℂ :=
  (ContinuousLinearMap.snd ℂ ℂ ℂ).comp A.ambient.symm.toContinuousLinearMap

theorem normalCoordinate_inclusion_zero (A : D.TangentFrame p) (v : ℂ) :
    A.normalCoordinate (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ × ℂ) D.inclusion p v) = 0 := by
  have ha := A.adapted (A.tangent.symm v)
  rw [A.tangent.apply_symm_apply] at ha
  rw [← ha]
  change (A.ambient.symm (A.ambient (A.tangent.symm v, 0))).2 = 0
  rw [A.ambient.symm_apply_apply]

theorem normalized_restriction_identity (A : D.TangentFrame p) (f : Fibration X)
    (normalize : TangentSpace 𝓘(ℂ, ℂ) (f (D.inclusion p)) ≃L[ℂ] ℂ) (z : ℂ) :
    NormalQuotient.normalizedFibrationDifferential f (D.inclusion p) A.ambient normalize (z, 0) =
      normalize (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (D.restrictedMap f) p (A.tangent z)) := by
  rw [NormalQuotient.normalizedFibrationDifferential_apply, A.adapted,
    D.restrictedMap_mfderiv_apply]

end TangentFrame

/-- The normalized-covector equality produced by the normal-quotient argument
forces the actual paired differential to be nonsurjective. -/
theorem ramified_of_normalized_equality (f g : Fibration X) (p : X)
    (frame : (ℂ × ℂ) ≃L[ℂ] TangentSpace 𝓘(ℂ, ℂ × ℂ) p)
    (nf : TangentSpace 𝓘(ℂ, ℂ) (f p) ≃L[ℂ] ℂ)
    (ng : TangentSpace 𝓘(ℂ, ℂ) (g p) ≃L[ℂ] ℂ)
    (heq : NormalQuotient.normalizedFibrationDifferential f p frame nf =
      NormalQuotient.normalizedFibrationDifferential g p frame ng) :
    p ∈ RamificationSupport.ramificationSet f g := by
  intro hsurj
  have hpair := (CoordinateCalculus.pairMap_surjective_iff f g p).mp hsurj
  obtain ⟨v, hv⟩ := hpair (nf.symm 0, ng.symm 1)
  have hvf : mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ) f p v = nf.symm 0 := congrArg Prod.fst hv
  have hvg : mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ) g p v = ng.symm 1 := congrArg Prod.snd hv
  have he := NormalQuotient.actual_differential_equality_of_normalized_equality
    f g p frame nf ng heq v
  have hf : nf (mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ) f p v) = 0 := by
    rw [hvf, nf.apply_symm_apply]
  have hg : ng (mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ) g p v) = 1 := by
    rw [hvg, ng.apply_symm_apply]
  rw [hf, hg] at he
  exact zero_ne_one he

theorem tangentToPair_of_normalized_equality (D : EmbeddedCurve X) (f g : Fibration X)
    (frames : ∀ p : D.curve, D.TangentFrame p)
    (nf : ∀ p : D.curve, TangentSpace 𝓘(ℂ, ℂ) (f (D.inclusion p)) ≃L[ℂ] ℂ)
    (ng : ∀ p : D.curve, TangentSpace 𝓘(ℂ, ℂ) (g (D.inclusion p)) ≃L[ℂ] ℂ)
    (heq : ∀ p : D.curve,
      NormalQuotient.normalizedFibrationDifferential f (D.inclusion p) (frames p).ambient (nf p) =
        NormalQuotient.normalizedFibrationDifferential g (D.inclusion p) (frames p).ambient (ng p)) :
    D.TangentToPair f g := by
  rintro x ⟨p, rfl⟩
  exact ramified_of_normalized_equality f g _ (frames p).ambient (nf p) (ng p) (heq p)

/-- The injectivity of an actual differential is preserved by the actual
source and target coordinate changes. -/
theorem inclusion_coordinate_injective (D : EmbeddedCurve X) (p : D.curve) :
    Function.Injective (fderiv ℂ
      (CoordinateCalculus.coordinateMap D.inclusion p (D.inclusion p)) ((chartAt ℂ p) p)) := by
  have ha := mem_chart_source ℂ p
  have hz := (chartAt ℂ p).map_source ha
  have hb : D.inclusion ((chartAt ℂ p).symm ((chartAt ℂ p) p)) ∈
      (chartAt (ℂ × ℂ) (D.inclusion p)).source := by
    rw [(chartAt ℂ p).left_inv ha]
    exact mem_chart_source (ℂ × ℂ) (D.inclusion p)
  rw [CoordinateCalculus.coordinateMap_derivative D.inclusion p (D.inclusion p) hz hb]
  let A : ℂ ≃L[ℂ] ℂ :=
    (mdifferentiable_chart (I := 𝓘(ℂ, ℂ)) p).symm.mfderiv hz
  let B : (ℂ × ℂ) ≃L[ℂ] (ℂ × ℂ) :=
    (mdifferentiable_chart (I := 𝓘(ℂ, ℂ × ℂ)) (D.inclusion p)).mfderiv hb
  change Function.Injective (fun v => B
    (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ × ℂ) D.inclusion
      ((chartAt ℂ p).symm ((chartAt ℂ p) p)) (A v)))
  rw [(chartAt ℂ p).left_inv ha]
  exact B.injective.comp ((D.immersion p).comp A.injective)

/-- The local differential argument is independent of the chosen curve chart.
An immersed actual curve contained in the normal axis of a cyclic model has
bijective differentials for both restrictions, when the original second
projection is a submersion at the ramification point. -/
theorem cyclic_restriction_differentials_bijective
    {F G : ℂ × ℂ → ℂ} {ν : ℂ → ℂ × ℂ} {z : ℂ}
    (B : CyclicModel.CyclicNormalForm F G (ν z))
    (hν : DifferentiableAt ℂ ν z) (hι : Function.Injective (fderiv ℂ ν z))
    (haxis : ∀ᶠ t in 𝓝 z, (B.coordinate.chart (ν t)).2 = 0)
    (hp : ¬ Function.Surjective (fderiv ℂ (fun q => (F q, G q)) (ν z)))
    (hG : Function.Surjective (fderiv ℂ G (ν z))) :
    Function.Bijective (fderiv ℂ (F ∘ ν) z) ∧
      Function.Bijective (fderiv ℂ (G ∘ ν) z) := by
  let L : ℂ →L[ℂ] (ℂ × ℂ) :=
    (fderiv ℂ B.coordinate.chart (ν z)).comp (fderiv ℂ ν z)
  have hL : Function.Injective L :=
    (B.coordinate.differential_bijective _ B.coordinate.source_mem).1.comp hι
  have hchart := (B.coordinate.analytic _ B.coordinate.source_mem).differentiableAt
  have hsnd : HasFDerivAt (fun t => (B.coordinate.chart (ν t)).2)
      ((ContinuousLinearMap.snd ℂ ℂ ℂ).comp L) z :=
    (hasFDerivAt_snd (𝕜 := ℂ) (p := B.coordinate.chart (ν z))).comp z
      (hchart.hasFDerivAt.comp z hν.hasFDerivAt)
  have hsnd0 : (ContinuousLinearMap.snd ℂ ℂ ℂ).comp L = 0 :=
    hsnd.unique ((hasFDerivAt_const (0 : ℂ) z).congr_of_eventuallyEq haxis)
  have hLzero : ∀ v : ℂ, (L v).2 = 0 := fun v => by
    have h := congrArg (fun A : ℂ →L[ℂ] ℂ => A v) hsnd0
    exact h
  have hfirst : ∀ v : ℂ, fderiv ℂ (F ∘ ν) z v = (L v).1 := by
    intro v
    rw [fderiv_comp z (B.hasFDerivAt_first B.coordinate.source_mem).differentiableAt hν,
      (B.hasFDerivAt_first B.coordinate.source_mem).fderiv]
    rfl
  have hfinj : Function.Injective (fderiv ℂ (F ∘ ν) z) := by
    intro a b hab
    apply hL
    apply Prod.ext
    · simpa only [hfirst] using hab
    · rw [hLzero, hLzero]
  have hφ := B.graph_derivative_ne_zero hp B.coordinate.source_mem
    (by rw [B.centre_coordinates]) hG
  have hsecond : ∀ v : ℂ, fderiv ℂ (G ∘ ν) z v =
      deriv B.graph (B.coordinate.chart (ν z)).1 * (L v).1 := by
    intro v
    rw [fderiv_comp z (B.hasFDerivAt_second B.coordinate.source_mem).differentiableAt hν,
      (B.hasFDerivAt_second B.coordinate.source_mem).fderiv]
    change localSecondDifferential B.exponent (B.coordinate.chart (ν z)).2
      (deriv B.graph (B.coordinate.chart (ν z)).1) (L v) = _
    simp only [localSecondDifferential_apply, hLzero, mul_zero, zero_add]
  have hginj : Function.Injective (fderiv ℂ (G ∘ ν) z) := by
    intro a b hab
    apply hfinj
    rw [hfirst, hfirst]
    apply mul_left_cancel₀ hφ
    simpa only [hsecond] using hab
  exact ⟨⟨hfinj, LinearMap.injective_iff_surjective.mp hfinj⟩,
    ⟨hginj, LinearMap.injective_iff_surjective.mp hginj⟩⟩

/-- A cyclic normal form for the two actual fibration coordinate functions at
an actual point of the embedded curve. The centre is the value of the actual
inclusion coordinate function, equal to the ambient chart centre. -/
abbrev CyclicAt (D : EmbeddedCurve X) (f g : Fibration X) (p : D.curve) :=
  CyclicModel.CyclicNormalForm
    (CoordinateCalculus.coordinateMap (CoordinateCalculus.fibrationMap f)
      (D.inclusion p) (f (D.inclusion p)))
    (CoordinateCalculus.coordinateMap (CoordinateCalculus.fibrationMap g)
      (D.inclusion p) (g (D.inclusion p)))
    (CoordinateCalculus.coordinateMap D.inclusion p (D.inclusion p) ((chartAt ℂ p) p))

/-- Transport the actual coordinate restriction differential back to the
actual curve tangent differential. -/
theorem restriction_bijective_of_coordinate_surjective (D : EmbeddedCurve X)
    (f : Fibration X) (p : D.curve)
    (hs : Function.Surjective (fderiv ℂ
      (CoordinateCalculus.coordinateMap (D.restrictedMap f) p (f (D.inclusion p)))
        ((chartAt ℂ p) p))) :
    Function.Bijective (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (D.restrictedMap f) p) := by
  have hm := (CoordinateCalculus.coordinateMap_center_surjective_iff (D.restrictedMap f) p).mp hs
  change Function.Surjective (D.restrictionDifferential f p) at hm
  change Function.Bijective (D.restrictionDifferential f p)
  exact ⟨LinearMap.injective_iff_surjective.mpr hm, hm⟩

/-- A cyclic model and actual ramification containment imply unramified
restrictions at this point. The inclusion's local normal-axis identity is
derived from ramification containment and the cyclic model, not supplied as
an additional assumption. Only the original second fibration is assumed
smooth here. -/
theorem restrictions_bijective_of_cyclicAt (D : EmbeddedCurve X) (f g : Fibration X)
    (hD : D.TangentToPair f g) (p : D.curve) (B : D.CyclicAt f g p)
    (hg : Function.Surjective
      (mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ) g (D.inclusion p))) :
    Function.Bijective (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (D.restrictedMap f) p) ∧
      Function.Bijective (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (D.restrictedMap g) p) := by
  let ν := CoordinateCalculus.coordinateMap D.inclusion p (D.inclusion p)
  let F := CoordinateCalculus.coordinateMap (CoordinateCalculus.fibrationMap f)
    (D.inclusion p) (f (D.inclusion p))
  let G := CoordinateCalculus.coordinateMap (CoordinateCalculus.fibrationMap g)
    (D.inclusion p) (g (D.inclusion p))
  let z := (chartAt ℂ p) p
  have hν : DifferentiableAt ℂ ν z :=
    (CoordinateCalculus.curve_coordinateMap_analytic D.inclusion p).differentiableAt
  have hnot := CoordinateCalculus.normalization_joint_not_surjective f g D.inclusion
    (fun q => hD ⟨q, rfl⟩) p
  change ∀ᶠ t in 𝓝 z, ¬ Function.Surjective
    (fun v => (fderiv ℂ F (ν t) v, fderiv ℂ G (ν t) v)) at hnot
  have hprod : ∀ q ∈ B.coordinate.chart.source,
      fderiv ℂ (fun q => (F q, G q)) q =
        (fderiv ℂ F q).prod (fderiv ℂ G q) := fun q hq =>
    (B.hasFDerivAt_first hq).differentiableAt.fderiv_prodMk
      (B.hasFDerivAt_second hq).differentiableAt
  have hp : ¬ Function.Surjective (fderiv ℂ (fun q => (F q, G q)) (ν z)) := by
    rw [hprod _ B.coordinate.source_mem]
    exact hnot.self_of_nhds
  have hsource : ∀ᶠ t in 𝓝 z, ν t ∈ B.coordinate.chart.source :=
    hν.continuousAt.tendsto (B.coordinate.chart.open_source.mem_nhds B.coordinate.source_mem)
  have haxis : ∀ᶠ t in 𝓝 z, (B.coordinate.chart (ν t)).2 = 0 := by
    filter_upwards [hsource, hnot] with t ht hram
    apply (B.ramification_iff_normal_zero hp ht).mp
    rw [hprod _ ht]
    exact hram
  have hG : Function.Surjective (fderiv ℂ G (ν z)) := by
    change Function.Surjective (fderiv ℂ G
      (CoordinateCalculus.coordinateMap D.inclusion p (D.inclusion p) ((chartAt ℂ p) p)))
    rw [CoordinateCalculus.coordinateMap_center]
    exact (CoordinateCalculus.coordinateMap_center_surjective_iff
      (CoordinateCalculus.fibrationMap g) (D.inclusion p)).mpr hg
  have hbij := cyclic_restriction_differentials_bijective B hν
    (D.inclusion_coordinate_injective p) haxis hp hG
  have hfcoord := (CoordinateCalculus.restricted_coordinate_comp_germ f D.inclusion p).fderiv_eq
    (𝕜 := ℂ)
  have hgcoord := (CoordinateCalculus.restricted_coordinate_comp_germ g D.inclusion p).fderiv_eq
    (𝕜 := ℂ)
  constructor
  · apply D.restriction_bijective_of_coordinate_surjective f p
    rw [show CoordinateCalculus.coordinateMap (D.restrictedMap f) p (f (D.inclusion p)) =
      MetricComparison.writtenCoordinateMap (CoordinateCalculus.restrictedMap f D.inclusion) p
      from rfl, hfcoord]
    exact hbij.1.2
  · apply D.restriction_bijective_of_coordinate_surjective g p
    rw [show CoordinateCalculus.coordinateMap (D.restrictedMap g) p (g (D.inclusion p)) =
      MetricComparison.writtenCoordinateMap (CoordinateCalculus.restrictedMap g D.inclusion) p
      from rfl, hgcoord]
    exact hbij.2.2

/-- Pointwise cyclic normal forms along the actual embedded ramification
curve give both actual unramified restriction maps. -/
theorem unramified_of_cyclicAt (D : EmbeddedCurve X) (f g : Fibration X)
    (hD : D.TangentToPair f g) (models : ∀ p : D.curve, D.CyclicAt f g p)
    (hg : g.Smooth) : D.Unramified f ∧ D.Unramified g := by
  constructor
  · intro p
    exact (D.restrictions_bijective_of_cyclicAt f g hD p (models p) (hg _)).1
  · intro p
    exact (D.restrictions_bijective_of_cyclicAt f g hD p (models p) (hg _)).2

end EmbeddedCurve

end Paper27.Geometry
