import Paper27.Geometry.CovectorGauges
import Paper27.Geometry.RamificationSupport

/-!
# Actual fibre curves and their degrees

This file instantiates the fibre and degree inputs of Lemma 2.1 for actual
smooth holomorphic fibrations. Its degree is not an arbitrary natural-number
label: for a nonconstant actual curve map it is `MetricComparison.mapDegree`,
the sum of the actual derivative-zero orders plus one over the target
basepoint; for a constant map it is zero.

The remaining explicit classical inputs are universal. `SmoothProperFibreModels`
is the complex submersion theorem for the actual compact connected fibres.
`EhresmannDegreeInvariance` is the consequence of Ehresmann's proper submersion
theorem, homotopy invariance of oriented topological degree, and identification
of that degree with the holomorphic local-multiplicity sum. It is stated for
every actual holomorphic map on the total space and every honest fibre model,
not for an arbitrary function called degree. `HolomorphicSubmersionSections`
and `BijectiveHolomorphicInverse` are the existing universal classical inputs.

The constancy criterion for this defined degree, the passage between constancy
on a model and on the actual fibre, and the construction of `FibreDegreeFacts`
are proved below. The final theorem has no per-pair degree or fibre premise.
The classical interfaces remain parameters: this file does not formalize
Ehresmann's theorem or the topological-degree comparison itself.
-/

noncomputable section

open scoped Manifold Topology

namespace Paper27.Geometry.FibreGeometry

open MetricComparison

/-- The actual multiplicity-sum degree, extended by zero on constant maps.
The finite fibre used in the sum is supplied by the universal curve-map
theorem; proof irrelevance makes its particular proof immaterial. -/
def curveDegree (maps : ClassicalCurveMapFacts) {D B : Curve}
    (u : HolomorphicMap D B) : ℕ := by
  classical
  exact if hu : Nonconstant u then
    mapDegree u (maps.fibres_finite D B u hu B.basepoint) else 0

theorem curveDegree_eq_mapDegree (maps : ClassicalCurveMapFacts) {D B : Curve}
    (u : HolomorphicMap D B) (hu : Nonconstant u)
    (hf : {p : D | u p = B.basepoint}.Finite) :
    curveDegree maps u = mapDegree u hf := by
  classical
  simp only [curveDegree, dif_pos hu]

theorem curveDegree_positive (maps : ClassicalCurveMapFacts) {D B : Curve}
    (u : HolomorphicMap D B) (hu : Nonconstant u) : 0 < curveDegree maps u := by
  rw [curveDegree_eq_mapDegree maps u hu
    (maps.fibres_finite D B u hu B.basepoint)]
  exact mapDegree_positive u _ (maps.surjective D B u hu)

/-- The zero-degree criterion is proved for the defined multiplicity sum,
rather than supplied as a separate hypothesis about each pair of fibrations. -/
theorem curveDegree_zero_iff_constant (maps : ClassicalCurveMapFacts)
    {D B : Curve} (u : HolomorphicMap D B) :
    curveDegree maps u = 0 ↔ CovectorGauges.IsConstant u := by
  classical
  constructor
  · intro hzero
    by_contra hconstant
    have hu := (CovectorGauges.nonconstant_iff_not_constant u).mpr hconstant
    exact (Nat.ne_of_gt (curveDegree_positive maps u hu)) hzero
  · intro hconstant
    have hu : ¬ Nonconstant u := by
      intro hu
      exact (CovectorGauges.nonconstant_iff_not_constant u).mp hu hconstant
    simp only [curveDegree, dif_neg hu]

/-- The general complex-submersion fibre theorem. Every model is a genuine
compact connected complex curve, homeomorphic to the specified actual fibre,
with holomorphic inclusion. There is no second fibration in this input. -/
def SmoothProperFibreModels : Prop :=
  ∀ (X : CompactComplexSurface) (f : Fibration X),
    IsProperMap f.map → f.Smooth → ∀ b : f.base, Nonempty (FibreCurveModel f b)

/-- Choose actual fibre models from the universal smooth-fibre theorem.
Properness of the actual map follows from its continuity and compact source. -/
def fibreModels (fibres : SmoothProperFibreModels) {X : CompactComplexSurface}
    (f : Fibration X) (hf : f.Smooth) (b : f.base) : FibreCurveModel f b :=
  Classical.choice (fibres X f f.holomorphic.continuous.isProperMap hf b)

/-- A fibration viewed only as its actual holomorphic map. -/
def holomorphicMap {X : CompactComplexSurface} (g : Fibration X) :
    HolomorphicMap X g.base :=
  ⟨g.map, g.holomorphic⟩

/-- Restriction of an arbitrary actual holomorphic map on the total space to
an actual fibre curve. The target need not be the base of another fibration. -/
def restrictionMap {X : CompactComplexSurface} {f : Fibration X} {b : f.base}
    (F : FibreCurveModel f b) {C : Curve} (g : HolomorphicMap X C) :
    HolomorphicMap F.curve C :=
  ⟨fun q => g (F.inclusion q), g.holomorphic.comp F.inclusion.holomorphic⟩

@[simp] theorem restrictionMap_fibration {X : CompactComplexSurface}
    {f : Fibration X} {b : f.base} (F : FibreCurveModel f b) (g : Fibration X) :
    restrictionMap F (holomorphicMap g) = F.restriction g := rfl

/-- The standard degree-invariance consequence of Ehresmann: after the usual
identification of oriented topological degree with the explicitly defined
holomorphic multiplicity sum, the restrictions of any actual holomorphic map
have the same degree on every fibre of a smooth proper family over a connected
curve. The source fibration already includes connected fibres and a connected
base; all chosen fibre identifications have holomorphic inclusions.

This is deliberately a universal, unformalized classical theorem. It does not
assert fibrewise constancy, factorization, equivalence, or finiteness of a pair.
In particular it is not a free degree operation or a per-pair degree record. -/
def EhresmannDegreeInvariance (maps : ClassicalCurveMapFacts) : Prop :=
  ∀ (X : CompactComplexSurface) (f : Fibration X),
    IsProperMap f.map → f.Smooth →
    ∀ (C : Curve) (g : HolomorphicMap X C)
      (models : ∀ b : f.base, FibreCurveModel f b) (b b' : f.base),
      curveDegree maps (restrictionMap (models b) g) =
        curveDegree maps (restrictionMap (models b') g)

/-- Constancy on the actual fibre and on an honest fibre model agree. This
uses the actual homeomorphism and its inclusion, not a constancy label. -/
theorem restriction_constant_iff {X : CompactComplexSurface}
    {f : Fibration X} {b : f.base} (F : FibreCurveModel f b) (g : Fibration X) :
    CovectorGauges.IsConstant (F.restriction g) ↔ f.ConstantOnFibre g b := by
  constructor
  · rintro ⟨c, hc⟩ p q hp hq
    have hp' := hc (F.identify.symm ⟨p, hp⟩)
    have hq' := hc (F.identify.symm ⟨q, hq⟩)
    change g (F.inclusion _) = c at hp' hq'
    rw [F.inclusion_symm p hp] at hp'
    rw [F.inclusion_symm q hq] at hq'
    exact hp'.trans hq'.symm
  · intro hc
    refine ⟨g (F.inclusion F.curve.basepoint), ?_⟩
    intro q
    exact hc (F.inclusion q) (F.inclusion F.curve.basepoint)
      (F.map_inclusion q) (F.map_inclusion F.curve.basepoint)

/-- Construct the record required by the proved factorization argument from
actual restriction degrees and the universal classical inputs. -/
def fibreDegreeFacts (maps : ClassicalCurveMapFacts)
    (fibres : SmoothProperFibreModels) (invariance : EhresmannDegreeInvariance maps)
    {X : CompactComplexSurface} (f g : Fibration X) (hf : f.Smooth) :
    Fibration.FibreDegreeFacts f g where
  degree b := curveDegree maps ((fibreModels fibres f hf b).restriction g)
  degree_independent b b' := by
    simpa only [restrictionMap_fibration] using
      invariance X f f.holomorphic.continuous.isProperMap hf g.base
        (holomorphicMap g) (fibreModels fibres f hf) b b'
  degree_zero_iff_constant b :=
    (curveDegree_zero_iff_constant maps _).trans
      (restriction_constant_iff (fibreModels fibres f hf b) g)

/-- The existing universal compact-curve facts supply exactly the mapping
theorem used in the factorization proof; Riemann--Hurwitz is not used here. -/
theorem compactCurveMapTheorem (maps : ClassicalCurveMapFacts) :
    NonconstantCompactCurveMapTheorem := by
  intro D B u hu
  exact ⟨maps.fibres_finite D B u hu, maps.surjective D B u hu⟩

/-- Lemma 2.1 for actual smooth inequivalent fibrations. The only unformalized
premises are universal classical theorems; neither per-pair fibre-degree facts
nor per-pair fibre models are assumptions of this theorem. -/
theorem finitePair_pairSurjective (maps : ClassicalCurveMapFacts)
    (fibres : SmoothProperFibreModels) (invariance : EhresmannDegreeInvariance maps)
    (sections : HolomorphicSubmersionSections) (inverse : BijectiveHolomorphicInverse)
    {X : CompactComplexSurface} (f g : Fibration X) (hf : f.Smooth) (hg : g.Smooth)
    (hne : ¬ Fibration.Equivalent f g) : f.FinitePair g ∧ f.PairSurjective g := by
  exact Fibration.finitePair_pairSurjective_of_inequivalent
    (compactCurveMapTheorem maps) inverse f g hf hg
    (fun hf => fibreModels fibres f hf)
    (fun hf => fibreDegreeFacts maps fibres invariance f g hf)
    (fun hf => sections X f hf) hne

/-- The preceding theorem supplies the actual proper finite surjective
holomorphic pair map, in the sense required by the ramification argument. -/
def finiteSurjectivePair (maps : ClassicalCurveMapFacts)
    (fibres : SmoothProperFibreModels) (invariance : EhresmannDegreeInvariance maps)
    (sections : HolomorphicSubmersionSections) (inverse : BijectiveHolomorphicInverse)
    {X : CompactComplexSurface} (f g : Fibration X) (hf : f.Smooth) (hg : g.Smooth)
    (hne : ¬ Fibration.Equivalent f g) :
    RamificationSupport.FiniteSurjectiveHolomorphicMap X
      (f.base.productSurface g.base) :=
  let hpair := finitePair_pairSurjective maps fibres invariance sections inverse f g hf hg hne
  RamificationSupport.finiteSurjectivePair f g hpair.1 hpair.2

end Paper27.Geometry.FibreGeometry
