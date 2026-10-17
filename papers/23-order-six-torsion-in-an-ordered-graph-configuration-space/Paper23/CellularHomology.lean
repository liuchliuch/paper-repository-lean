import Paper23.Cubical
import Paper23.CertificateAlgebra

/-!
The degree-two homology quotient of the original ordered cubical model.
The chain groups here are supported on four labelled graph cells with
pairwise disjoint closures. The boundary is the endpoint differential
proved in `Cubical`, with the increasing-moving-edge orientation.
No geometric comparison with singular homology is assumed in its definition.
-/
namespace Paper23
open Cubical CertificateAlgebra

/-- The original cubical chain complex, restricted to degrees three, two, one. -/
noncomputable def orderedCubicalComplex :
    IntegralChainComplex₂ (Chains 3) (Chains 2) (Chains 1) where
  d3 := (differential 2).toAddMonoidHom
  d2 := (differential 1).toAddMonoidHom
  boundary_squared := differential_squared 1

/-- Integral degree-two cellular homology of the ordered discretized space. -/
abbrev DiscreteH₂ := orderedCubicalComplex.Homology₂

/-- This type requires all four identities on the actual unreduced chains. -/
abbrev CubicalCertificate := Certificate orderedCubicalComplex

/-- The explicit algebraic argument applied to the original cubical groups.
This auxiliary result still requires a verified concrete certificate. -/
theorem cubical_certificate_consequence (cert : CubicalCertificate) :
    ∃ x : DiscreteH₂, addOrderOf x = 6 ∧
      addOrderOf ((2 : ℕ) • x) = 3 ∧ addOrderOf ((3 : ℕ) • x) = 2 := by
  exact ⟨cert.homologyElement, cert.exact_order_six,
    cert.twice_exact_order_three, cert.thrice_exact_order_two⟩

/-- Transport through a proved comparison isomorphism. A comparison map is
an explicit hypothesis of this auxiliary lemma, not a substituted main theorem. -/
theorem cubical_certificate_transfer {H : Type*} [AddCommGroup H]
    (comparison : DiscreteH₂ ≃+ H) (cert : CubicalCertificate) :
    ∃ x : H, addOrderOf x = 6 ∧ addOrderOf ((2 : ℕ) • x) = 3 ∧
      addOrderOf ((3 : ℕ) • x) = 2 := by
  refine ⟨comparison cert.homologyElement, ?_, ?_, ?_⟩
  · rw [comparison.addOrderOf_eq]
    exact cert.exact_order_six
  · rw [← map_nsmul, comparison.addOrderOf_eq]
    exact cert.twice_exact_order_three
  · rw [← map_nsmul, comparison.addOrderOf_eq]
    exact cert.thrice_exact_order_two

end Paper23
