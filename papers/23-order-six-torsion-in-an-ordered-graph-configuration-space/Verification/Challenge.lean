import Paper23.CertificateAlgebra
import Paper23.Cubical
import Paper23.UnitCancellation
import Paper23.SourceTopology

/-!
# P23 auxiliary contracts only

These exact statements cover the proved labelled cubical boundary, general
unit cancellation, geometric disjointness test, and algebra after a certificate
has been provided. They neither supply the original graph's certificate nor
assert the paper's main theorem. The challenge uses complete production proofs
too, so no admission is introduced even in this trusted statement module.
-/

namespace P23Auxiliary

open Paper23.CertificateAlgebra

theorem exact_order_six_of_detector {A : Type*} [AddCommGroup A]
    (x : A) (f : A →+ ZMod 6) (annihilated : (6 : ℕ) • x = 0)
    (detected : f x = 1) : addOrderOf x = 6 :=
  Paper23.CertificateAlgebra.exact_order_six_of_detector x f annihilated detected

universe u₃ u₂ u₁
variable {C3 : Type u₃} {C2 : Type u₂} {C1 : Type u₁}
variable [AddCommGroup C3] [AddCommGroup C2] [AddCommGroup C1]
variable {K : IntegralChainComplex₂ C3 C2 C1} (cert : Certificate K)

theorem certificate_exact_order_six : addOrderOf cert.homologyElement = 6 :=
  cert.exact_order_six

theorem certificate_integer_annihilator (k : ℤ) :
    k • cert.homologyElement = 0 ↔ (6 : ℤ) ∣ k :=
  cert.zsmul_element_eq_zero_iff k

theorem certificate_integer_boundaries (k : ℤ) :
    k • cert.z ∈ K.d3.range ↔ (6 : ℤ) ∣ k :=
  cert.zsmul_mem_range_iff k

theorem certificate_odd_torsion :
    addOrderOf ((2 : ℕ) • cert.homologyElement) = 3 :=
  cert.twice_exact_order_three

theorem certificate_failure_saturation :
    (6 : ℕ) • cert.z ∈ K.d3.range ∧
      cert.z ∈ K.d2.ker ∧ cert.z ∉ K.d3.range :=
  cert.failure_saturation

include cert in
theorem certificate_boundaries_not_saturated :
    ¬ (∀ (c : K.Cycles₂) (n : ℕ), n ≠ 0 →
      n • c ∈ K.boundaries₂ → c ∈ K.boundaries₂) :=
  cert.boundaries_not_saturated


/-- The actual endpoint boundary squares to zero before restriction. -/
theorem cubical_boundary_squared (x : Paper23.Cubical.RawChain) :
    Paper23.Cubical.boundary (Paper23.Cubical.boundary x) = 0 :=
  Paper23.Cubical.boundary_squared x

/-- The chain relation on the labelled disjoint-closure subcomplex. -/
theorem cubical_differential_squared (q : ℕ) (x : Paper23.Cubical.Chains (q+2)) :
    Paper23.Cubical.differential q (Paper23.Cubical.differential (q+1) x) = 0 :=
  Paper23.Cubical.differential_squared q x

/-- Source equation (3): moving-edge orientation with all particle labels retained. -/
theorem cubical_boundary_basis_eq_moving_faces (c : Paper23.Cubical.RawCube)
    (hc : c.Pairwise Paper23.Cubical.ClosureDisjoint) :
    Paper23.Cubical.boundary (Paper23.Cubical.basis c) =
      ((Paper23.Cubical.faces c).map Paper23.Cubical.FaceData.movingTerm).sum :=
  Paper23.Cubical.boundary_basis_eq_moving_faces c hc

/-- Source equation (7), for a general ring, with no commutativity premise. -/
theorem unit_boundary_liftSource {R I J : Type*} [Ring R] [Fintype J]
    (M : Option I → Option J → R) (a : Rˣ)
    (hpivot : M none none = ↑a) (x : J → R) :
    Paper23.UnitCancellation.boundary M (Paper23.UnitCancellation.liftSource M a x) =
      Paper23.UnitCancellation.embedTarget (Paper23.UnitCancellation.reducedBoundary M a x) :=
  Paper23.UnitCancellation.boundary_liftSource M a hpivot x

/-- Additive cochain lifting over a general, possibly noncommutative ring. -/
theorem unit_liftCochain_annihilates {R I J : Type*} [Ring R]
    {A : Type*} [AddCommGroup A] [Fintype J]
    (M : Option I → Option J → R) (a : Rˣ)
    (hpivot : M none none = ↑a) (φ : (I → R) →+ A)
    (hφ : ∀ x : J → R, φ (Paper23.UnitCancellation.reducedBoundary M a x) = 0)
    (x : Option J → R) :
    Paper23.UnitCancellation.liftCochain M a φ (Paper23.UnitCancellation.boundary M x) = 0 :=
  Paper23.UnitCancellation.liftCochain_annihilates M a hpivot φ hφ x

/-- The source finite endpoint test is exact for the actual topological carriers. -/
theorem sourceCell_closedCarrier_disjoint_iff
    (c d : Paper23.Cubical.GraphCell) :
    Disjoint (Paper23.subdividedGraph.closedCarrier (Paper23.sourceCell c))
      (Paper23.subdividedGraph.closedCarrier (Paper23.sourceCell d)) ↔
        Paper23.Cubical.ClosureDisjoint c d :=
  Paper23.sourceCell_closedCarrier_disjoint_iff c d

end P23Auxiliary
