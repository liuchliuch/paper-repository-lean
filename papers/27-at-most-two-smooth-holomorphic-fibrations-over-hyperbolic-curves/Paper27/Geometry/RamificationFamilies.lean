import Paper27.Geometry.CurveBranchInputs

/-!
# Actual ramification components from the original pair of fibrations

The normalization, target uniformizing charts, Euclidean cyclic models, and
embedded components in this file are constructed intermediate data. None is
an assumption on the pair. The only additional classical inputs, beyond
`CurveBranchInputs`, are the general embedded-submanifold decomposition and
the open nonsingular locus. Local-degree theory is needed only for the
uniform index conclusion.

In particular, hyperbolicity of a constructed component is deduced from its
actual unramified restriction to the first hyperbolic base. The general
submanifold decomposition is not asked to supply hyperbolicity or either
unramified restriction.
-/

noncomputable section
open scoped Manifold

namespace Paper27.Geometry.RamificationFamilies

open NormalizedBranchConstruction RamificationIndexConstancy
  SmoothCurveDecomposition

variable {X : CompactComplexSurface} (K : CurveBranchInputs)

include K

/-- The actual finite pair has local cyclic surface charts, once a general
normalization representative has been chosen. The cyclic models and their
critical-axis identities are constructed by the preceding own arguments. -/
theorem surface_charts_with_normalization
    (f g : Fibration X) (hf : f.Smooth) (hg : g.Smooth)
    (hB : f.Hyperbolic) (hC : g.Hyperbolic)
    (hfinite : f.FinitePair g) (hsurj : f.PairSurjective g)
    (N : CriticalCurveNormalization
      (RamificationSupport.finiteSurjectivePair f g hfinite hsurj)) :
    ∀ p ∈ RamificationSupport.ramificationSet f g,
      Nonempty (SurfaceCyclicChart
        (RamificationSupport.finiteSurjectivePair f g hfinite hsurj) p) := by
  intro p hp
  obtain ⟨a, d, B, hn, hvalid⟩ :=
    K.euclidean_model_exists f g hf hg hB hC hfinite hsurj N p hp
  exact ⟨ActualCyclicModels.surfaceChartOfModel hfinite hsurj p hp a d B hn hvalid⟩

/-- An actual ramification family, including both unramified restrictions
and hyperbolicity, constructed from the original maps. -/
theorem family_with_normalization
    (decomposition : EmbeddedSubmanifoldDecomposition)
    (openness : RetractionFactorization.NonsingularJointLocusOpen)
    (f g : Fibration X) (hf : f.Smooth) (hg : g.Smooth)
    (hB : f.Hyperbolic) (hC : g.Hyperbolic)
    (hfinite : f.FinitePair g) (hsurj : f.PairSurjective g)
    (N : CriticalCurveNormalization
      (RamificationSupport.finiteSurjectivePair f g hfinite hsurj)) :
    Nonempty (RamificationCurveFamily f g) := by
  have charts := surface_charts_with_normalization K f g hf hg hB hC hfinite hsurj N
  have axes : ∀ p ∈ RamificationSupport.ramificationSet f g,
      Nonempty (HolomorphicAxisChart X (RamificationSupport.ramificationSet f g) p) := by
    intro p hp
    obtain ⟨A⟩ := charts p hp
    exact ⟨A.axisChart⟩
  obtain ⟨F, hF, htangent⟩ := decompose_ramification decomposition openness f g axes
  have hu : ∀ i, (F.member i).Unramified f ∧ (F.member i).Unramified g := by
    intro i
    exact K.unramified_of_tangency f g hf hg hB hC hfinite hsurj N
      (F.member i) (htangent i)
  exact ⟨ramificationCurveFamilyOfUnramified K.curveMaps f g hB F hF
    (fun i => (hu i).1) (fun i => (hu i).2)⟩

/-- Select only the general normalization of the actual finite pair. No
normalization object or local branch model remains a premise. -/
theorem surface_charts
    (f g : Fibration X) (hf : f.Smooth) (hg : g.Smooth)
    (hB : f.Hyperbolic) (hC : g.Hyperbolic)
    (hfinite : f.FinitePair g) (hsurj : f.PairSurjective g) :
    ∀ p ∈ RamificationSupport.ramificationSet f g,
      Nonempty (SurfaceCyclicChart
        (RamificationSupport.finiteSurjectivePair f g hfinite hsurj) p) := by
  obtain ⟨N⟩ := K.normalization X (f.base.productSurface g.base)
    (RamificationSupport.finiteSurjectivePair f g hfinite hsurj)
  exact surface_charts_with_normalization K f g hf hg hB hC hfinite hsurj N

/-- The finite disjoint compact hyperbolic curve family covering precisely
the actual critical set is a conclusion about the original smooth pair. -/
theorem ramification_family_exists
    (decomposition : EmbeddedSubmanifoldDecomposition)
    (openness : RetractionFactorization.NonsingularJointLocusOpen)
    (f g : Fibration X) (hf : f.Smooth) (hg : g.Smooth)
    (hB : f.Hyperbolic) (hC : g.Hyperbolic)
    (hfinite : f.FinitePair g) (hsurj : f.PairSurjective g) :
    Nonempty (RamificationCurveFamily f g) := by
  obtain ⟨N⟩ := K.normalization X (f.base.productSurface g.base)
    (RamificationSupport.finiteSurjectivePair f g hfinite hsurj)
  exact family_with_normalization K decomposition openness f g hf hg hB hC
    hfinite hsurj N

/-- Every actual connected embedded curve in the critical set has a single
index at least two. Every cyclic chart at every one of its points has this
same exponent. Neither the curve's index nor an atlas on it is a premise. -/
theorem component_index
    (degrees : FiniteLocalDegreeTheory)
    (f g : Fibration X) (hf : f.Smooth) (hg : g.Smooth)
    (hB : f.Hyperbolic) (hC : g.Hyperbolic)
    (hfinite : f.FinitePair g) (hsurj : f.PairSurjective g)
    (D : EmbeddedCurve X) (hD : D.TangentToPair f g) :
    ∃ n : ℕ, 2 ≤ n ∧
      (∀ p : D.curve, degrees.localDegree X
        (f.base.productSurface g.base)
        (RamificationSupport.finiteSurjectivePair f g hfinite hsurj) (D.inclusion p) = n) ∧
      (∀ p : D.curve,
        ∀ A : SurfaceCyclicChart
          (RamificationSupport.finiteSurjectivePair f g hfinite hsurj) (D.inclusion p),
          A.exponent = n) := by
  exact RamificationIndexConstancy.component_index_constant degrees
    (RamificationSupport.finiteSurjectivePair f g hfinite hsurj) D hD
    (surface_charts K f g hf hg hB hC hfinite hsurj)

/-- Assemble the actual ramification family together with uniform indices
of all its members. The single package of general branch inputs supplies
only classical operations; all pair-specific geometry is derived above. -/
theorem ramification_family_with_indices_exists
    (decomposition : EmbeddedSubmanifoldDecomposition)
    (openness : RetractionFactorization.NonsingularJointLocusOpen)
    (degrees : FiniteLocalDegreeTheory)
    (f g : Fibration X) (hf : f.Smooth) (hg : g.Smooth)
    (hB : f.Hyperbolic) (hC : g.Hyperbolic)
    (hfinite : f.FinitePair g) (hsurj : f.PairSurjective g) :
    ∃ F : RamificationCurveFamily f g, ∀ i, ∃ n : ℕ, 2 ≤ n ∧
      (∀ p : (F.member i).curve, degrees.localDegree X
        (f.base.productSurface g.base)
        (RamificationSupport.finiteSurjectivePair f g hfinite hsurj)
          ((F.member i).inclusion p) = n) ∧
      (∀ p : (F.member i).curve,
        ∀ A : SurfaceCyclicChart
          (RamificationSupport.finiteSurjectivePair f g hfinite hsurj)
          ((F.member i).inclusion p), A.exponent = n) := by
  obtain ⟨F⟩ := ramification_family_exists K decomposition openness f g hf hg hB hC
    hfinite hsurj
  refine ⟨F, ?_⟩
  intro i
  have hD : (F.member i).TangentToPair f g := by
    intro p hp
    rw [← F.support_eq]
    exact Set.mem_iUnion.mpr ⟨i, hp⟩
  exact component_index K degrees f g hf hg hB hC hfinite hsurj (F.member i) hD

end Paper27.Geometry.RamificationFamilies
