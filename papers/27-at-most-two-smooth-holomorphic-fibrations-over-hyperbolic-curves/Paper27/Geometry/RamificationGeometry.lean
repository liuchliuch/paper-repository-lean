import Paper27.Geometry.FibrationBound
import Paper27.Geometry.NormalAtlasRestriction
import Paper27.Geometry.RamificationDivisorOrder

/-!
# Proposition 2.4 from the original pair

The finite disjoint family, its unramified restrictions, its uniform indices,
actual factored retractions, normal tensor isomorphism and faithful cyclic
action are outputs. The action and the normal atlas live on the same actual
neighbourhood. The coefficient of the actual coordinate Jacobian divisor is
proved to be the index minus one in every cyclic chart along the component.
-/
noncomputable section
open scoped Manifold Topology
open Filter
namespace Paper27.Geometry

open RetractionCoordinateGerms RetractionFactorization NormalAtlasAction NormalDegreeInvariance

/-- The geometry constructed for an actual embedded ramification component.
The honest adapted frames identify `normal` with the actual normal quotient;
its degree is the usual self-intersection number of the curve. -/
structure RamificationComponentGeometry (K : ClassicalInputs) {X : CompactComplexSurface}
    (f g : Fibration X) (hfinite : f.FinitePair g) (hsurj : f.PairSurjective g)
    (D : EmbeddedCurve X) where
  index : ℕ
  index_ge_two : 2 ≤ index
  first_unramified : D.Unramified f
  second_unramified : D.Unramified g
  first_covering : IsCoveringMap (D.restrictedMap f)
  second_covering : IsCoveringMap (D.restrictedMap g)
  coefficient : ∀ p : D.curve,
    ∀ A : RamificationIndexConstancy.SurfaceCyclicChart
      (RamificationSupport.finiteSurjectivePair f g hfinite hsurj) (D.inclusion p),
      RamificationDivisorOrder.divisorCoefficient A (D.inclusion p) = index - 1
  neighbourhood : D.Neighbourhood
  first : D.Retraction neighbourhood
  second : D.Retraction neighbourhood
  first_factor : Factorization first f
  second_factor : Factorization second g
  atlas : NormalAtlas D neighbourhood first second index
  normal : HolomorphicLineCocycle D.curve
  tangent : TangentLineCocycle D.curve
  frames : EmbeddedFrames.RawEmbeddedFrames D normal tangent.bundle
  tensor : HolomorphicLineGauge (normal.tensorPower index) tangent.bundle
  normal_degree_formula : (K.degreeTheory.degree D.curve normal : ℚ) =
    - (2 * (D.curve.genus : ℚ) - 2) / (index : ℚ)
  normal_degree_negative : K.degreeTheory.degree D.curve normal < 0
  action : NeighbourhoodSplittings.NeighbourhoodAction (rootsOfUnity index ℂ) first
  generator : rootsOfUnity index ℂ
  generator_scalar : ((generator : ℂˣ) : ℂ) =
    Complex.exp (2 * Real.pi * Complex.I / (index : ℂ))
  faithful : Function.Injective action.permutation
  generator_order : orderOf (action.permutation generator) = index
  fixes_curve : ∀ a p, action.map a (D.inclusion p) = D.inclusion p
  preserves_second : ∀ a x, x ∈ neighbourhood.domain →
    second.toFun (action.map a x) = second.toFun x
  local_rotation : ∀ a p, action.map a =ᶠ[𝓝 (D.inclusion p)]
    localRotation (atlas.chart p p).coordinates ((a : ℂˣ) : ℂ)

namespace ClassicalInputs
variable {X : CompactComplexSurface} (K : ClassicalInputs)
include K

/-- Every actual embedded curve in the paired critical set has all the
geometry asserted in Proposition 2.4. No pair-specific geometric data are
premises beyond the actual component and its inclusion in the critical set. -/
theorem component_geometry (f g : Fibration X) (hf : f.Smooth) (hg : g.Smooth)
    (hB : f.Hyperbolic) (hC : g.Hyperbolic)
    (hfinite : f.FinitePair g) (hsurj : f.PairSurjective g)
    (D : EmbeddedCurve X) (hD : D.TangentToPair f g) (hDh : D.curve.Hyperbolic) :
    Nonempty (RamificationComponentGeometry K f g hfinite hsurj D) := by
  obtain ⟨N₀⟩ := K.normalization X (f.base.productSurface g.base)
    (RamificationSupport.finiteSurjectivePair f g hfinite hsurj)
  have hu := K.toCurveBranchInputs.unramified_of_tangency f g hf hg hB hC
    hfinite hsurj N₀ D hD
  let R := CommonRetractions.pair K.unramifiedCurveCovering K.neighbourhoodLifting
    K.etaleLiftRegularity D f g hu.1 hu.2
  obtain ⟨n, hn, ⟨A⟩, hindex⟩ :=
    RetractionNormalAtlasBridge.normalAtlas_of_original_pair K.toCurveBranchInputs
      K.localDegrees K.dividedDifferences K.localUnitRoots hf hg hB hC hfinite hsurj
      N₀ hD R.first_factor R.second_factor
  letI : NeZero n := ⟨by omega⟩
  let scalar : rootsOfUnity n ℂ →* ℂˣ := (rootsOfUnity n ℂ).subtype
  have hscalar : Function.Injective scalar := Subtype.val_injective
  have hroot : ∀ a : rootsOfUnity n ℂ, (scalar a : ℂ) ^ n = 1 :=
    fun a => (mem_rootsOfUnity' n a.val).mp a.property
  obtain ⟨W, r, action, _hW, hWU, hr, hgerm, hs⟩ := action_from_normalAtlas
    K.normalDivision K.regularity K.mapGermGluing A (by omega) scalar hroot R.neighbourhood
  let s := restrictRetraction R.second W hWU
  let A' := A.restrict r s hr rfl
  obtain ⟨N, T, ⟨F⟩⟩ := K.normalFrames X D
  have hdegree := A.normal_tensor_degree K.regularity F (by omega) K.degreeTheory
    K.degreeGaugeInvariance
  rw [K.degreeTheory.tangent_degree D.curve T] at hdegree
  have hdegreeQ : (n : ℚ) * (K.degreeTheory.degree D.curve N : ℚ) =
      2 - 2 * (D.curve.genus : ℚ) := by exact_mod_cast hdegree
  have hformula : (K.degreeTheory.degree D.curve N : ℚ) =
      -(2 * (D.curve.genus : ℚ) - 2) / (n : ℚ) := by
    apply (eq_div_iff (by exact_mod_cast (show n ≠ 0 by omega) : (n : ℚ) ≠ 0)).mpr
    linarith
  let ζ := Complex.exp (2 * Real.pi * Complex.I / (n : ℂ))
  have hζ : IsPrimitiveRoot ζ n := Complex.isPrimitiveRoot_exp n (NeZero.ne n)
  let a : rootsOfUnity n ℂ := rootsOfUnity.mkOfPowEq ζ hζ.pow_eq_one
  have hfaithful := action_faithful_of_germs A action scalar hscalar hgerm
  let complexScalar : rootsOfUnity n ℂ →* ℂ := (Units.coeHom ℂ).comp scalar
  have hcomplex : Function.Injective complexScalar := Units.val_injective.comp hscalar
  have horder : orderOf (action.permutation a) = n := by
    calc
      orderOf (action.permutation a) = orderOf a :=
        orderOf_injective action.permutation hfaithful a
      _ = orderOf (complexScalar a) := (orderOf_injective complexScalar hcomplex a).symm
      _ = orderOf ζ := rfl
      _ = n := hζ.eq_orderOf.symm
  refine ⟨{
    index := n
    index_ge_two := hn
    first_unramified := hu.1
    second_unramified := hu.2
    first_covering := K.unramifiedCurveCovering D.curve f.base (D.restrictedMap f) hu.1
    second_covering := K.unramifiedCurveCovering D.curve g.base (D.restrictedMap g) hu.2
    coefficient := RamificationDivisorOrder.component_divisorCoefficient D n hD hindex
    neighbourhood := W
    first := r
    second := s
    first_factor := ?_
    second_factor := fun x hx => R.second_factor x (hWU hx)
    atlas := A'
    normal := N
    tangent := T
    frames := F
    tensor := A.normalTensorGauge K.regularity F (by omega)
    normal_degree_formula := hformula
    normal_degree_negative := A.normal_degree_negative K.regularity F (by omega)
      K.degreeTheory K.degreeGaugeInvariance hDh
    action := action
    generator := a
    generator_scalar := rfl
    faithful := hfaithful
    generator_order := horder
    fixes_curve := ?_
    preserves_second := hs
    local_rotation := hgerm
  }⟩
  · intro x hx
    rw [hr]
    exact R.first_factor x (hWU hx)
  · intro b p
    exact (hgerm b p).self_of_nhds.trans (localRotation_fixed (A.chart p p).coordinates
      (scalar b : ℂ) (A.source_mem p p (mem_chart_source ℂ p))
      (by rw [A.centre p p (mem_chart_source ℂ p)]))

/-- Proposition 2.4: all components and all their geometry are constructed
from the actual original smooth inequivalent hyperbolic fibrations. -/
theorem ramification_geometry (f g : Fibration X) (hf : f.Smooth) (hg : g.Smooth)
    (hB : f.Hyperbolic) (hC : g.Hyperbolic) (hne : ¬ Fibration.Equivalent f g) :
    ∃ (hfinite : f.FinitePair g) (hsurj : f.PairSurjective g)
      (F : RamificationCurveFamily f g),
      ∀ i, Nonempty (RamificationComponentGeometry K f g hfinite hsurj (F.member i)) := by
  obtain ⟨hfinite, hsurj⟩ := K.finite_pair f g hf hg hne
  obtain ⟨F⟩ := RamificationFamilies.ramification_family_exists K.toCurveBranchInputs
    K.submanifolds K.nonsingularOpen f g hf hg hB hC hfinite hsurj
  refine ⟨hfinite, hsurj, F, ?_⟩
  intro i
  apply K.component_geometry f g hf hg hB hC hfinite hsurj (F.member i)
  · intro x hx
    rw [← F.support_eq]
    exact Set.mem_iUnion.mpr ⟨i, hx⟩
  · exact F.hyperbolic i

end ClassicalInputs
end Paper27.Geometry
