import Paper28.SphericalLiftedCurrentPresentation

/-! Standard disjoint integer presentation and mass compatibility for a
finite geodesic polyhedral current in a proper locally round chart cover.
This is common finite PL refinement plus canonical AK integration,
injective/local-isometric area and mass locality. No transfer map, joint
estimate, approximation or filling appears in the general input.
-/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Set
variable {G : Type} [Group G] [DecidableEq G] [Countable G]
  {M : SphericalQuotientMetricInput G}
  {I : CompactIntegralCurrentAlgebraInput.{0,0} (RegularOrbitQuotient G) M.metric}
  {J : CompactIntegralCurrentAlgebraInput.{0,0} (RegularSphere G) inferInstance}
  (S : SphericalSimplexIntegrationInput M I.toCompactIntegralCurrentSupportInput)
  (L : LiftedSphericalSimplexIntegrationInput (M := M) J)

def projectedSphericalGenerator (k : ℕ) (σ : LiftableSphericalSimplex M k) : sphericalPolyhedralCurrents S k :=
  ⟨S.integration k σ,AddSubgroup.subset_closure ⟨σ,rfl⟩⟩

def projectedSphericalSimplexInterior {k : ℕ} (σ : LiftableSphericalSimplex M k) : Set (RegularOrbitQuotient G) :=
  regularQuotientMap '' {u : RegularSphere G | ∃ t : stdSimplex ℝ (Fin (k+1)),
    (∀ i, 0 < t.val i) ∧ u.val = sphericalNormalize (sphericalBarycentricVector (fun i => (σ.vertices i).val) t)}

structure GeodesicPolyhedralMassPresentation (k : ℕ) (P : sphericalPolyhedralCurrents S k) where
  count : ℕ
  simplex : Fin count → LiftableSphericalSimplex M k
  coefficient : Fin count → ℤ
  disjoint_interiors : ∀ i j, i ≠ j → Disjoint (projectedSphericalSimplexInterior (simplex i))
    (projectedSphericalSimplexInterior (simplex j))
  current_formula : P = ∑ i, coefficient i • projectedSphericalGenerator S k (simplex i)
  mass_formula : I.mass P.val = ∑ i, |(coefficient i : ℝ)| * J.mass (L.integration k (simplex i))

/-- Universal standard finite geodesic polychain mass representation.
All chart assumptions are the actual LiftableSphericalSimplex fields;
finite relevant overlaps are the native exact overlap theorem. -/
structure GeodesicPolyhedralMassInput : Prop where
  presentation : ∀ {G : Type} [Group G] [DecidableEq G] [Countable G]
    {M : SphericalQuotientMetricInput G}
    {I : CompactIntegralCurrentAlgebraInput.{0,0} (RegularOrbitQuotient G) M.metric}
    {J : CompactIntegralCurrentAlgebraInput.{0,0} (RegularSphere G) inferInstance}
    (S : SphericalSimplexIntegrationInput M I.toCompactIntegralCurrentSupportInput)
    (L : LiftedSphericalSimplexIntegrationInput (M := M) J)
    (k : ℕ) (P : sphericalPolyhedralCurrents S k), Nonempty (GeodesicPolyhedralMassPresentation S L k P)

end Paper28
