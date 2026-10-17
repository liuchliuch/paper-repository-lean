import Paper27.Geometry.RetractionFactorization
import Paper27.Geometry.RamificationDichotomy

/-!
# From actual local axis charts to compact embedded curve components

The external submanifold construction is stated for an arbitrary closed
subset of an arbitrary compact complex surface. Its input consists of actual
biholomorphic charts identifying that subset with a coordinate axis. Its
output is only the finite family of compact embedded curve components.
Neither unramified projection restrictions nor hyperbolicity is included.

The own deductions below identify the actual paired critical set, prove its
closedness using the ordinary open nonsingular locus, and transport coverage
to actual tangency of every constructed component.
-/
noncomputable section
open scoped Manifold
namespace Paper27.Geometry.SmoothCurveDecomposition

/-- Actual local holomorphic submanifold coordinates, with both directions
of the local set identity. This is data for a general closed subset. -/
structure HolomorphicAxisChart (X : CompactComplexSurface) (S : Set X) (p : X) where
  coordinates : OpenPartialHomeomorph X (ℂ × ℂ)
  centre_mem : p ∈ coordinates.source
  holomorphic : MDifferentiableOn 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ)
    coordinates coordinates.source
  inverse_holomorphic : MDifferentiableOn 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ)
    coordinates.symm coordinates.target
  axis : ∀ q ∈ coordinates.source, q ∈ S ↔ (coordinates q).2 = 0

/-- The general embedded complex submanifold construction and compact
component decomposition. It has no maps to curves, ramification index,
unramifiedness, normal bundle, or fibration bound in its statement. -/
def EmbeddedSubmanifoldDecomposition : Prop :=
  ∀ (X : CompactComplexSurface) (S : Set X), IsClosed S →
    (∀ p ∈ S, Nonempty (HolomorphicAxisChart X S p)) →
      ∃ F : DisjointCurveFamily X, F.support = S

variable {X : CompactComplexSurface}

theorem ramificationSet_compl_eq (f g : Fibration X) :
    (RamificationSupport.ramificationSet f g)ᶜ =
      {x : X | Function.Bijective
        (RetractionFactorization.jointDifferential (CoordinateCalculus.fibrationMap f)
          (CoordinateCalculus.fibrationMap g) x)} := by
  ext x
  constructor
  · intro hx
    exact RetractionFactorization.joint_bijective_of_not_ramified f g x hx
  · intro hx hr
    apply hr
    apply (CoordinateCalculus.pairMap_surjective_iff f g x).mpr
    exact hx.2

/-- Closedness concerns the actual critical set, independent of coordinate
representatives of the manifold differential. -/
theorem ramificationSet_isClosed (openness : RetractionFactorization.NonsingularJointLocusOpen)
    (f g : Fibration X) : IsClosed (RamificationSupport.ramificationSet f g) := by
  apply isOpen_compl_iff.mp
  rw [ramificationSet_compl_eq]
  exact openness X f.base g.base (CoordinateCalculus.fibrationMap f)
    (CoordinateCalculus.fibrationMap g)

/-- Applying the general submanifold theorem to the actual local normal
charts gives coverage of the actual ramification set. The local axis charts
are a proved intermediate input to this assembly, not an external existence
theorem about the paired fibrations. -/
theorem decompose_ramification
    (decomposition : EmbeddedSubmanifoldDecomposition)
    (openness : RetractionFactorization.NonsingularJointLocusOpen)
    (f g : Fibration X)
    (charts : ∀ p ∈ RamificationSupport.ramificationSet f g,
      Nonempty (HolomorphicAxisChart X (RamificationSupport.ramificationSet f g) p)) :
    ∃ F : DisjointCurveFamily X,
      F.support = RamificationSupport.ramificationSet f g ∧
      ∀ i, (F.member i).TangentToPair f g := by
  obtain ⟨F, hF⟩ := decomposition X (RamificationSupport.ramificationSet f g)
    (ramificationSet_isClosed openness f g) charts
  refine ⟨F, hF, ?_⟩
  intro i p hp
  rw [← hF]
  exact Set.mem_iUnion.mpr ⟨i, hp⟩

/-- Actual bijective differentials rule out a constant actual curve map. -/
theorem unramified_nonconstant {C B : Curve} (u : HolomorphicMap C B)
    (hu : ∀ p : C, Function.Bijective (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) u p)) :
    MetricComparison.Nonconstant u := by
  by_contra h
  change ¬ (∃ p q : C, u p ≠ u q) at h
  push_neg at h
  have heq : u.toFun = fun _ : C => u C.basepoint :=
    funext fun p => h p C.basepoint
  have hs := (hu C.basepoint).2
  obtain ⟨v, hv⟩ := hs (1 : ℂ)
  have hzero : (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) u C.basepoint : ℂ →L[ℂ] ℂ) = 0 := by
    rw [heq]
    exact mfderiv_const
  have hz : (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) u C.basepoint : ℂ →L[ℂ] ℂ) v = (0 : ℂ) :=
    congrArg (fun L : ℂ →L[ℂ] ℂ => L v) hzero
  have hv' : (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) u C.basepoint : ℂ →L[ℂ] ℂ) v = (1 : ℂ) := hv
  exact (zero_ne_one : (0 : ℂ) ≠ 1) (hz.symm.trans hv')

/-- Hyperbolicity is derived from the actual unramified first restriction
and Riemann--Hurwitz, after the local cyclic calculations have supplied both
unramified restrictions. It is not part of the submanifold theorem. -/
def ramificationCurveFamilyOfUnramified
    (maps : MetricComparison.ClassicalCurveMapFacts)
    (f g : Fibration X) (hf : f.Hyperbolic) (F : DisjointCurveFamily X)
    (hF : F.support = RamificationSupport.ramificationSet f g)
    (hfirst : ∀ i, (F.member i).Unramified f)
    (hsecond : ∀ i, (F.member i).Unramified g) : RamificationCurveFamily f g where
  toDisjointCurveFamily := F
  support_eq := hF
  hyperbolic := fun i => MetricComparison.source_hyperbolic maps ((F.member i).restrictedMap f)
    (unramified_nonconstant ((F.member i).restrictedMap f) (hfirst i)) hf
  first_unramified := hfirst
  second_unramified := hsecond

end Paper27.Geometry.SmoothCurveDecomposition
