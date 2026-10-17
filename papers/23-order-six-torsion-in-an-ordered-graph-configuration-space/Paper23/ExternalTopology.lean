import Paper23.GraphGirth
import Paper23.Subdivision
import Paper23.CellularHomology

/-!
# Explicit external topology inputs

This module proves consequences relative to two named external inputs.  It
introduces neither axioms nor `sorry` and does not claim to have formalized
these external results.

* `PrueScrimshawH2Input` is the degree-two integral-homology consequence of
  Prue--Scrimshaw, *Abrams's stable equivalence for graph braid groups*,
  Topology Appl. 178 (2014), 136--145, Theorem 3.2, arXiv:0909.5511v2,
  together with homotopy invariance (Hatcher, Theorem 2.10 / Corollary 2.11).
  Its map is the singular-homology map of the actual ordered inclusion.
  The graph-specific sufficient conditions are proved in `GraphGirth`.
* `OrderedCubicalComparisonInput` includes the standard identification of
  this concrete labelled, oriented cubical chain complex with the cellular
  chains of the ordered discretized subcomplex, and the cellular/singular
  comparison (Hatcher, Theorem 2.35).  That CW-chain identification is part of
  this explicitly unformalized input, not a result claimed by this file.

The original quantifiers, source hypotheses, graph-loop interpretation and
exact specialization are recorded in `external-dependencies.json`.
-/
namespace Paper23.ExternalTopology

open CategoryTheory

noncomputable section

abbrev SubdividedOrderedSpace := OrderedConfiguration 4 subdividedGraph.Realization
abbrev DiscreteSingularH₂ := IntegralHomology 2 DiscretizedSourceSpace
abbrev SubdividedSingularH₂ := IntegralHomology 2 SubdividedOrderedSpace

/-- The actual inclusion of the ordered discretized subspace, retaining all
four particle labels. -/
def discretizedInclusionMap : C(DiscretizedSourceSpace, SubdividedOrderedSpace) :=
  ⟨subdividedGraph.discretizedInclusion 4, subdividedGraph.continuous_discretizedInclusion 4⟩

/-- Its degree-two integral singular-homology morphism in mathlib's functor. -/
def inclusionHomologyMorphism : DiscreteSingularH₂ ⟶ SubdividedSingularH₂ :=
  ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 2).obj
    (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom discretizedInclusionMap)

/-- The underlying additive homomorphism of that specific induced morphism. -/
def inclusionHomologyMap : DiscreteSingularH₂ →+ SubdividedSingularH₂ := by
  letI : Module ℤ DiscreteSingularH₂ := DiscreteSingularH₂.isModule
  letI : Module ℤ SubdividedSingularH₂ := SubdividedSingularH₂.isModule
  exact inclusionHomologyMorphism.hom.toAddMonoidHom

/-- EXTERNAL INPUT E-PS-H2.  This is a specialized corollary of stable
equivalence and homotopy invariance.  Every hypothesis about this paper's
graph is supplied by the kernel theorem `GraphGirth.fourParticleConditions`.
No certificate, cycle or torsion conclusion occurs in this input. -/
def PrueScrimshawH2Input : Prop :=
  GraphGirth.FourParticleConditions → Function.Bijective inclusionHomologyMap

/-- EXTERNAL INPUT E-CUBICAL-CW-H2.  The source is precisely the quotient
homology of the existing free ordered-cube groups and endpoint differential;
the target is actual singular homology of the topological subspace `D₄`.
This includes the standard cubical-CW chain identification and comparison. -/
abbrev OrderedCubicalComparisonInput := DiscreteH₂ ≃+ DiscreteSingularH₂

/-- Instantiate E-PS-H2 with the already proved concrete graph conditions. -/
def discretizationHomologyEquiv (ps : PrueScrimshawH2Input) :
    DiscreteSingularH₂ ≃+ SubdividedSingularH₂ :=
  AddEquiv.ofBijective inclusionHomologyMap (ps GraphGirth.fourParticleConditions)

@[simp] theorem discretizationHomologyEquiv_apply (ps : PrueScrimshawH2Input)
    (x : DiscreteSingularH₂) : discretizationHomologyEquiv ps x = inclusionHomologyMap x := rfl

/-- The full comparison to the paper's original graph.  The last step is the
explicit subdivision homeomorphism already proved in Lean. -/
def comparison (ps : PrueScrimshawH2Input) (cw : OrderedCubicalComparisonInput) :
    DiscreteH₂ ≃+ SourceHomology :=
  cw.trans ((discretizationHomologyEquiv ps).trans Subdivision.sourceHomologyEquiv)

/-- Own algebraic transfer, conditional on the two disclosed external inputs
and on a genuine certificate in the original ordered cubical chain groups. -/
theorem certificate_consequence (ps : PrueScrimshawH2Input)
    (cw : OrderedCubicalComparisonInput) (cert : CubicalCertificate) :
    ∃ z : SourceHomology, addOrderOf z = 6 ∧ addOrderOf ((2 : ℕ) • z) = 3 ∧
      addOrderOf ((3 : ℕ) • z) = 2 :=
  cubical_certificate_transfer (comparison ps cw) cert

/-- The source theorem's exact conclusion relative to the explicitly named
external topology inputs.  The concrete certificate remains an input here. -/
theorem main_of_certificate (ps : PrueScrimshawH2Input)
    (cw : OrderedCubicalComparisonInput) (cert : CubicalCertificate) : MainTheoremStatement := by
  obtain ⟨z, hz, _, _⟩ := certificate_consequence ps cw cert
  exact ⟨z, hz⟩

end
end Paper23.ExternalTopology
