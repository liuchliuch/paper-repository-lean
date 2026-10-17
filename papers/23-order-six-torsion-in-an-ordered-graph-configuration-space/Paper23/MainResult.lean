import Paper23.CertificateCycle
import Paper23.CertificateCocycle
import Paper23.Bounding
import Paper23.ExternalTopology
import Paper23.SimplePresentation

/-!
# The concrete order-six class

The four certificate fields below use the actual labelled cubical chain
groups, endpoint differential, explicit integer chains and full mod-six
detector.  No certificate hypothesis is added to any result in this file.

The discrete homology conclusions are unconditional.  The conclusions in
the original space's singular homology have exactly the two established
external topology inputs registered in `external-dependencies.json`.
The alternative certificate's support counts differ from the source's
reported construction; that discrepancy is recorded in `README.md`.
-/
namespace Paper23
open Cubical CertificateChecks CertificateAlgebra

theorem concrete_ordered_cycle : differential 1 zChain = 0 := by
  apply Subtype.ext
  exact CertificateChecks.cycle

theorem concrete_ordered_cocycle (c : Chains 3) :
    phiChain (differential 2 c) = 0 :=
  CertificateChecks.cocycle c.val c.property

/-- All four checked identities on the genuine, unreduced ordered complex. -/
noncomputable def concreteCertificate : CubicalCertificate where
  z := zChain
  b := Bounding.bChain
  phi := phiChain.toAddMonoidHom
  cycle := concrete_ordered_cycle
  bounding := Bounding.ordered_bounding
  cocycle := concrete_ordered_cocycle
  evaluation := CertificateChecks.ordered_evaluation

/-- The class of the explicitly listed cycle in the actual cycles/boundaries quotient. -/
noncomputable def discreteClass : DiscreteH₂ := concreteCertificate.homologyElement

theorem discreteClass_exact_order_six : addOrderOf discreteClass = 6 :=
  concreteCertificate.exact_order_six

theorem twice_discreteClass_exact_order_three :
    addOrderOf ((2 : ℕ) • discreteClass) = 3 :=
  concreteCertificate.twice_exact_order_three

theorem thrice_discreteClass_exact_order_two :
    addOrderOf ((3 : ℕ) • discreteClass) = 2 :=
  concreteCertificate.thrice_exact_order_two

/-- The paper's full order assertion in the concrete cubical homology. -/
theorem discrete_result :
    ∃ z : DiscreteH₂, addOrderOf z = 6 ∧
      addOrderOf ((2 : ℕ) • z) = 3 ∧ addOrderOf ((3 : ℕ) • z) = 2 :=
  ⟨discreteClass, discreteClass_exact_order_six,
    twice_discreteClass_exact_order_three, thrice_discreteClass_exact_order_two⟩

theorem concrete_failure_saturation :
    (6 : ℕ) • zChain ∈ orderedCubicalComplex.d3.range ∧
      zChain ∈ orderedCubicalComplex.d2.ker ∧
      zChain ∉ orderedCubicalComplex.d3.range :=
  concreteCertificate.failure_saturation

theorem discrete_homology_not_torsion_free : ¬ IsAddTorsionFree DiscreteH₂ :=
  concreteCertificate.homology_not_torsion_free

/-- The explicit homology class transported to the original ordered space. -/
noncomputable def sourceClass (ps : ExternalTopology.PrueScrimshawH2Input)
    (cw : ExternalTopology.OrderedCubicalComparisonInput) : SourceHomology :=
  ExternalTopology.comparison ps cw discreteClass

theorem sourceClass_exact_order_six (ps : ExternalTopology.PrueScrimshawH2Input)
    (cw : ExternalTopology.OrderedCubicalComparisonInput) :
    addOrderOf (sourceClass ps cw) = 6 := by
  change addOrderOf ((ExternalTopology.comparison ps cw) discreteClass) = 6
  rw [(ExternalTopology.comparison ps cw).addOrderOf_eq]
  exact discreteClass_exact_order_six

theorem twice_sourceClass_exact_order_three (ps : ExternalTopology.PrueScrimshawH2Input)
    (cw : ExternalTopology.OrderedCubicalComparisonInput) :
    addOrderOf ((2 : ℕ) • sourceClass ps cw) = 3 := by
  change addOrderOf ((2 : ℕ) • (ExternalTopology.comparison ps cw) discreteClass) = 3
  rw [← map_nsmul, (ExternalTopology.comparison ps cw).addOrderOf_eq]
  exact twice_discreteClass_exact_order_three

theorem thrice_sourceClass_exact_order_two (ps : ExternalTopology.PrueScrimshawH2Input)
    (cw : ExternalTopology.OrderedCubicalComparisonInput) :
    addOrderOf ((3 : ℕ) • sourceClass ps cw) = 2 := by
  change addOrderOf ((3 : ℕ) • (ExternalTopology.comparison ps cw) discreteClass) = 2
  rw [← map_nsmul, (ExternalTopology.comparison ps cw).addOrderOf_eq]
  exact thrice_discreteClass_exact_order_two

/-- Theorem 1, relative only to the two disclosed established topology inputs.
In particular there is no cycle, certificate, detector or torsion premise. -/
theorem main_result (ps : ExternalTopology.PrueScrimshawH2Input)
    (cw : ExternalTopology.OrderedCubicalComparisonInput) :
    ∃ z : SourceHomology, addOrderOf z = 6 ∧
      addOrderOf ((2 : ℕ) • z) = 3 ∧ addOrderOf ((3 : ℕ) • z) = 2 :=
  ⟨sourceClass ps cw, sourceClass_exact_order_six ps cw,
    twice_sourceClass_exact_order_three ps cw, thrice_sourceClass_exact_order_two ps cw⟩

theorem main_theorem_relative (ps : ExternalTopology.PrueScrimshawH2Input)
    (cw : ExternalTopology.OrderedCubicalComparisonInput) : MainTheoremStatement :=
  ExternalTopology.main_of_certificate ps cw concreteCertificate

/-- The same class exists for the explicitly homeomorphic simple presentation. -/
theorem simple_presentation_result (ps : ExternalTopology.PrueScrimshawH2Input)
    (cw : ExternalTopology.OrderedCubicalComparisonInput) :
    ∃ z : IntegralHomology 2 (OrderedConfiguration 4 SimplePresentation.simpleGraph.Realization),
      addOrderOf z = 6 ∧ addOrderOf ((2 : ℕ) • z) = 3 ∧
      addOrderOf ((3 : ℕ) • z) = 2 :=
  cubical_certificate_transfer
    ((ExternalTopology.comparison ps cw).trans SimplePresentation.sourceHomologyEquiv.symm)
    concreteCertificate

end Paper23
