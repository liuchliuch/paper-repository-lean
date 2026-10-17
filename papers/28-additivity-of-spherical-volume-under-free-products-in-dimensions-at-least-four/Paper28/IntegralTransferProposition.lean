import Paper28.BassSerreTransferMass

/-! Original Proposition 3.2 on the actual free-product coset tree.
The standard Serre object is instantiated from the exact free-product
property. The concrete homomorphisms, independence, integer formulas,
positive-degree boundary identities and joint mass bound are native
derivations under the disclosed generic PL/AK foundations. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
variable {G : Type} [Group G] [DecidableEq G] [Countable G]
  {M : SphericalQuotientMetricInput G}
  {I : CompactIntegralCurrentAlgebraInput.{0,0} (RegularOrbitQuotient G) M.metric}
  {J : CompactIntegralCurrentAlgebraInput.{0,0} (RegularSphere G) inferInstance}
  (S : SphericalSimplexIntegrationInput M I.toCompactIntegralCurrentSupportInput)
  (L : LiftedSphericalSimplexIntegrationInput (M := M) J) (F : CanonicalGlobalCurrentCalculusInput)
  {A B : Subgroup G}
  (MA : SphericalQuotientMetricInput A) (MB : SphericalQuotientMetricInput B)
  (IA : CompactIntegralCurrentAlgebraInput.{0,0} (RegularOrbitQuotient A) MA.metric)
  (IB : CompactIntegralCurrentAlgebraInput.{0,0} (RegularOrbitQuotient B) MB.metric)
  (Gluing : SphericalCurrentGluingInput S L F)
  (FaithfulA : CurrentMassFaithfulnessInput IA) (FaithfulB : CurrentMassFaithfulnessInput IB)
  (Area : FiniteCoordinateCurrentAreaInput J) (Mass : GeodesicPolyhedralMassInput)

include Area Mass in
theorem proposition_3_2 (Fischer : FischerInput) (Free : IsFreeProductOfSubgroups A B)
    (BS : BassSerreStructureInput) : ∃ T : BassSerreObject A B,
    (∀ k (σ : LiftableSphericalSimplex M (k+1)),
      bassSerreTransferA L F T MA IA S Gluing FaithfulA k (projectedSphericalGenerator S (k+1) σ) =
        (bassSerreShadowFamilyA T MA J IA F FaithfulA k (liftedSphericalGenerator L (k+1) σ)).sum (fun _ C => C) ∧
      bassSerreTransferB L F T MB IB S Gluing FaithfulB k (projectedSphericalGenerator S (k+1) σ) =
        (bassSerreShadowFamilyB T MB J IB F FaithfulB k (liftedSphericalGenerator L (k+1) σ)).sum (fun _ C => C)) ∧
    (∀ k (P : sphericalPolyhedralCurrents S (k+2)),
      IA.boundary (k+1) (bassSerreTransferA L F T MA IA S Gluing FaithfulA (k+1) P) =
        bassSerreTransferA L F T MA IA S Gluing FaithfulA k (sphericalPolyhedralBoundary S L F Gluing (k+1) P) ∧
      IB.boundary (k+1) (bassSerreTransferB L F T MB IB S Gluing FaithfulB (k+1) P) =
        bassSerreTransferB L F T MB IB S Gluing FaithfulB k (sphericalPolyhedralBoundary S L F Gluing (k+1) P)) ∧
    (∀ k, 4 ≤ k+1 → ∀ P : sphericalPolyhedralCurrents S (k+1),
      IA.mass (bassSerreTransferA L F T MA IA S Gluing FaithfulA k P)+
        IB.mass (bassSerreTransferB L F T MB IB S Gluing FaithfulB k P) ≤ I.mass P.val) := by
  obtain ⟨T⟩ := BS.realization A B Free
  refine ⟨T,?_,?_,?_⟩
  · intro k σ
    exact ⟨bassSerreTransferA_simplex L F T MA IA S Gluing FaithfulA k σ,
      bassSerreTransferB_simplex L F T MB IB S Gluing FaithfulB k σ⟩
  · intro k P
    exact ⟨bassSerreTransferA_boundary L F T MA IA S Gluing FaithfulA k P,
      bassSerreTransferB_boundary L F T MB IB S Gluing FaithfulB k P⟩
  · exact bassSerreTransfer_joint_mass L F T MA MB IA IB S Gluing FaithfulA FaithfulB Area Mass Fischer

end Paper28
