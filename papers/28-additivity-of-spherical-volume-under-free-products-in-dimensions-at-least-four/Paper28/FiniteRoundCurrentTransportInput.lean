import Paper28.FiniteRoundQuotientRealizationInput
import Paper28.SupportedCurrents
import Paper28.SphericalPolyhedralCurrents

/-! Explicit standard AK transport on a finite spherical realization.
Closed-support identification (Lang Proposition 3.3), bi-Lipschitz
push/pull and boundary functoriality, and rectifiable mass locality on the
relative-face partition give the canonical mass-preserving chain
identification. Common geodesic subdivision and change of variables give
polyhedral compatibility, including positive radial vertex rescaling.
This combined standard corollary is not a separately numbered theorem.
No approximation, cycle existence, homology equivalence or filling is an
input field. The AK objects remain disclosed, unformalized foundations.
-/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Set
variable {G : Type} [Group G] [DecidableEq G] [Countable G]
  {M : SphericalQuotientMetricInput G} {K : Set (RegularOrbitQuotient G)}
  {C : FiniteSphericalQuotientPresentation M K}
  (R : FiniteRoundQuotientRealization C)
  (I : CompactIntegralCurrentAlgebraInput.{0,0} (RegularOrbitQuotient G) M.metric)
  (S : SphericalSimplexIntegrationInput M I.toCompactIntegralCurrentSupportInput)

structure FiniteRoundCurrentModel where
  algebra : CompactIntegralCurrentAlgebraInput.{0,0} R.space R.metric
  componentAlgebra : ∀ j : Fin R.polyhedron.componentCount,
    CompactIntegralCurrentAlgebraInput.{0,0} (R.polyhedron.component j) inferInstance
  decomposition : ComponentCurrentDecompositionInput R.polyhedron algebra componentAlgebra
  integration : ∀ j, LipschitzSimplexIntegrationInput inferInstance (componentAlgebra j)
  foundations : ∀ j {e : ℕ} (K₁ : FiniteEuclideanComplex (EuclideanAmbient e))
    (N : SphericalNeighborhoodRealization (R.polyhedron.triangulation j) K₁),
    Nonempty (SphericalPolyhedronCurrentFoundations N (R.polyhedron.point j) (componentAlgebra j) (integration j))
  comparison : ∀ j, LipschitzCurrentHomologyComparisonInput (componentAlgebra j) (integration j)
  identification : ∀ k, algebra.Current k ≃+ supportedCurrents I K k
  boundary_comm : ∀ k (T : algebra.Current (k+1)),
    supportedBoundary I K k (identification (k+1) T) = identification k (algebra.boundary k T)
  mass_compatibility : ∀ k (T : algebra.Current k), I.mass (identification k T).val = algebra.mass T
  polyhedral_compatibility : ∀ k (T : algebra.Current k),
    T ∈ finiteSphericalPolyhedralCurrents R.polyhedron decomposition integration k ↔
      (identification k T).val ∈ sphericalPolyhedralCurrents S k

/-- Universal canonical AK object/transport realization on any finite
proper spherical-chart presentation and its exact geometric realization.
The mass law uses the relative-face local metric identities in R. -/
structure FiniteRoundCurrentTransportInput : Prop where
  transport : ∀ {G : Type} [Group G] [DecidableEq G] [Countable G]
    {M : SphericalQuotientMetricInput G} {K : Set (RegularOrbitQuotient G)}
    {C : FiniteSphericalQuotientPresentation M K} (R : FiniteRoundQuotientRealization C)
    (I : CompactIntegralCurrentAlgebraInput.{0,0} (RegularOrbitQuotient G) M.metric)
    (S : SphericalSimplexIntegrationInput M I.toCompactIntegralCurrentSupportInput),
      Nonempty (FiniteRoundCurrentModel R I S)

variable {R I S} (T : FiniteRoundCurrentModel R I S)

def roundModelPush (k : ℕ) : T.algebra.Current k →+ I.Current k :=
  (supportedCurrents I K k).subtype.comp (T.identification k).toAddMonoidHom

theorem roundModelPush_boundary (k : ℕ) (Z : T.algebra.Current (k+1)) :
    I.boundary k (roundModelPush T (k+1) Z) = roundModelPush T k (T.algebra.boundary k Z) :=
  congrArg Subtype.val (T.boundary_comm k Z)

theorem roundModelPush_mass (k : ℕ) (Z : T.algebra.Current k) :
    I.mass (roundModelPush T k Z) = T.algebra.mass Z := T.mass_compatibility k Z

theorem roundModelPush_polyhedral (k : ℕ) (Z : T.algebra.Current k) :
    Z ∈ finiteSphericalPolyhedralCurrents R.polyhedron T.decomposition T.integration k ↔
      roundModelPush T k Z ∈ sphericalPolyhedralCurrents S k := T.polyhedral_compatibility k Z

theorem roundModelPull_boundary (k : ℕ) (Z : supportedCurrents I K (k+1)) :
    T.algebra.boundary k ((T.identification (k+1)).symm Z) =
      (T.identification k).symm (supportedBoundary I K k Z) := by
  apply (T.identification k).injective
  rw [AddEquiv.apply_symm_apply,← T.boundary_comm,AddEquiv.apply_symm_apply]

end Paper28
