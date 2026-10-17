import Paper28.FiniteLiftableCarrierCover
import Paper28.LiftableSimplexOverlaps
import Paper28.SphericalPolyhedronLemma

/-! Explicit standard finite spherical realization, with its actual chart
identifications. This is the finite geodesic-chart/common-subdivision
corollary of PL realization and the finite-shape spherical metric theory
(Rourke--Sanderson §2; Bridson--Haefliger I.7, 7.49 and 7A.12--13).
It is an unformalized general foundation parameter, not a new axiom.
No current, approximation, homology or filling occurs in this input.
-/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Set
variable {G : Type} [Group G] [DecidableEq G] [Countable G]
  (M : SphericalQuotientMetricInput G)

/-- A finite family of actual proper spherical charts in the native round
orbit quotient. Overlaps retain the actual finite group translates. -/
structure FiniteSphericalQuotientPresentation (K : Set (RegularOrbitQuotient G)) where
  cells : Finset (Σ k : ℕ, LiftableSphericalSimplex M k)
  cover : K = ⋃ τ ∈ cells, τ.2.projectedPatch
  finite_overlap : ∀ τ ∈ cells, ∀ σ ∈ cells,
    τ.2.projectedPatch ∩ σ.2.projectedPatch =
      ⋃ γ ∈ overlapTranslations τ.2.coordinates σ.2.coordinates,
        regularQuotientMap '' (τ.2.liftedPatch ∩ (fun u : RegularSphere G => γ • u) '' σ.2.liftedPatch)

variable {M} {K : Set (RegularOrbitQuotient G)}

/-- Standard realization data only. The ambient local metric identity is
specified on every relative face, including isotropy strata. -/
structure FiniteRoundQuotientRealization (C : FiniteSphericalQuotientPresentation M K) where
  space : Type
  metric : MetricSpace space
  polyhedron : @FiniteSphericalPolyhedron space metric
  identification : space ≃ K
  forward_lipschitz : letI := M.metric; letI := metric
    ∃ L : NNReal, LipschitzWith L (fun x => (identification x).val)
  inverse_lipschitz : letI := M.metric; letI := metric
    ∃ L : NNReal, LipschitzWith L identification.symm
  liftedChart : ∀ j : Fin polyhedron.componentCount, ∀ c : Fin (polyhedron.triangulation j).cellCount,
    EuclideanAmbient ((polyhedron.triangulation j).dimension c) →ₗᵢ[ℝ] CoordinateHilbert G
  chart_unit : ∀ j c u, u ∈ closedSphericalPatch ((polyhedron.triangulation j).vertex c)
      ((polyhedron.triangulation j).cells c) → ‖liftedChart j c u‖ = 1
  chart_formula : ∀ j c u (hu : u ∈ closedSphericalPatch ((polyhedron.triangulation j).vertex c)
      ((polyhedron.triangulation j).cells c)),
    (identification ((polyhedron.triangulation j).chart c u).val).val =
      regularQuotientMap ⟨liftedChart j c u,chart_unit j c u hu⟩
  ambient_round_relative_face : ∀ j c (F : Finset (polyhedron.complex j).VertexIndex),
    F ⊆ (polyhedron.triangulation j).cells c →
    ∀ u ∈ relativeSphericalPatch ((polyhedron.triangulation j).vertex c) F,
      ∃ r : ℝ, 0 < r ∧ ∀ v ∈ relativeSphericalPatch ((polyhedron.triangulation j).vertex c) F,
        ∀ w ∈ relativeSphericalPatch ((polyhedron.triangulation j).vertex c) F,
          dist v u < r → dist w u < r →
          @dist (RegularOrbitQuotient G) M.metric.toDist
            (identification ((polyhedron.triangulation j).chart c v).val).val
            (identification ((polyhedron.triangulation j).chart c w).val).val = angular v w

attribute [instance] FiniteRoundQuotientRealization.metric

/-- Universal finite-chart realization/refinement and ordinary metric
comparison. It applies to arbitrary finite proper geodesic charts, rather
than assuming the approximation or relative filling of any carrier. -/
structure FiniteRoundQuotientRealizationInput : Prop where
  realization : ∀ {G : Type} [Group G] [DecidableEq G] [Countable G]
    (M : SphericalQuotientMetricInput G) (K : Set (RegularOrbitQuotient G))
    (C : FiniteSphericalQuotientPresentation M K), Nonempty (FiniteRoundQuotientRealization C)

theorem finite_carrier_spherical_presentation (families : Finset (Finset G)) :
    Nonempty (FiniteSphericalQuotientPresentation M (quotientFiniteCarrier families)) := by
  obtain ⟨cells,hCells⟩ := finite_carrier_liftable_simplex_cover M families
  exact ⟨⟨cells,hCells,fun τ _ σ _ => projected_liftable_simplex_intersection τ.2 σ.2⟩⟩

end Paper28
