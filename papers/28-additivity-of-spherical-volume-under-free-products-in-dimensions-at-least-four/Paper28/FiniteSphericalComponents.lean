import Paper28.ConnectedSphericalPolyhedronApproximation

/-! A finite spherical polyhedron is a finite clopen disjoint union of
nonempty intrinsic spherical triangulations. The model has no current or
proof-neighborhood data. Generic AK restriction and canonical inclusion
laws on a finite clopen partition are disclosed separately. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Set
variable (Y : Type) [metricY : MetricSpace Y]

structure FiniteSphericalPolyhedron where
  componentCount : ℕ
  component : Fin componentCount → Set Y
  isOpen_component : ∀ j, IsOpen (component j)
  isClosed_component : ∀ j, IsClosed (component j)
  disjoint : ∀ i j, i ≠ j → Disjoint (component i) (component j)
  cover : (⋃ j, component j) = univ
  point : ∀ j, component j
  dimension : Fin componentCount → ℕ
  complex : ∀ j, FiniteEuclideanComplex (EuclideanAmbient (dimension j))
  triangulation : ∀ j, FiniteSphericalTriangulation (complex j) (component j)
  metric : ∀ j, IntrinsicSphericalTriangulationMetric (triangulation j)

variable {Y} (P : FiniteSphericalPolyhedron Y)

abbrev componentInclusionNearLipschitz (j : Fin P.componentCount) :
    LipschitzNearSet inferInstance metricY (fun x : P.component j => (x : Y)) univ :=
  lipschitzNearSet_of_lipschitzWith _ 1 isometry_subtype_coe.lipschitz _

variable (J : CompactIntegralCurrentAlgebraInput.{0,0} Y metricY)
  (Jc : ∀ j : Fin P.componentCount, CompactIntegralCurrentAlgebraInput.{0,0} (P.component j) inferInstance)

structure ComponentCurrentDecompositionInput where
  inclusion : ∀ j : Fin P.componentCount,
    NeighborhoodCurrentPushforwardInput inferInstance metricY (Jc j) J univ
      (fun x : P.component j => (x : Y)) isOpen_univ (componentInclusionNearLipschitz P j)
  restrict : ∀ j k, J.Current k →+ (Jc j).Current k
  restrict_boundary : ∀ j k (C : J.Current (k+1)),
    restrict j k (J.boundary k C) = (Jc j).boundary k (restrict j (k+1) C)
  reconstruction : ∀ k (C : J.Current k), C =
    ∑ j, (inclusion j).push k ⟨restrict j k C,subset_univ _⟩
  mass_sum : ∀ k (C : ∀ j, (Jc j).Current k),
    J.mass (∑ j, (inclusion j).push k ⟨C j,subset_univ _⟩) = ∑ j, (Jc j).mass (C j)
  restrict_self : ∀ j k (C : (Jc j).Current k),
    restrict j k ((inclusion j).push k ⟨C,subset_univ _⟩) = C
  restrict_other : ∀ i j, i ≠ j → ∀ k (C : (Jc j).Current k),
    restrict i k ((inclusion j).push k ⟨C,subset_univ _⟩) = 0

variable {J Jc} (D : ComponentCurrentDecompositionInput P J Jc)

def componentPush (j : Fin P.componentCount) (k : ℕ) : (Jc j).Current k →+ J.Current k where
  toFun C := (D.inclusion j).push k ⟨C,subset_univ _⟩
  map_zero' := by
    have he : (⟨(0 : (Jc j).Current k),subset_univ _⟩ : supportedCurrents (Jc j) univ k) = 0 := rfl
    rw [he,map_zero]
  map_add' C E := by
    have he : (⟨C+E,subset_univ _⟩ : supportedCurrents (Jc j) univ k) =
        ⟨C,subset_univ _⟩+⟨E,subset_univ _⟩ := rfl
    rw [he,map_add]

theorem componentPush_boundary (j : Fin P.componentCount) (k : ℕ) (C : (Jc j).Current (k+1)) :
    J.boundary k (componentPush P D j (k+1) C) = componentPush P D j k ((Jc j).boundary k C) :=
  (D.inclusion j).boundary_comm k ⟨C,subset_univ _⟩

variable (A : ∀ j, LipschitzSimplexIntegrationInput inferInstance (Jc j))

def finiteSphericalPolyhedralCurrents (k : ℕ) : AddSubgroup (J.Current k) :=
  AddSubgroup.closure (Set.range (fun s : Σ j : Fin P.componentCount,
    {C : (Jc j).Current k // C ∈ cellwiseSphericalPolyhedralCurrents (P.triangulation j) (A j) k} =>
    componentPush P D s.1 k s.2.val))

theorem component_polyhedral_push_mem {k : ℕ} (j : Fin P.componentCount) (C : (Jc j).Current k)
    (hC : C ∈ cellwiseSphericalPolyhedralCurrents (P.triangulation j) (A j) k) :
    componentPush P D j k C ∈ finiteSphericalPolyhedralCurrents P D A k :=
  AddSubgroup.subset_closure ⟨⟨j,⟨C,hC⟩⟩,rfl⟩

theorem component_restrict_polyhedral {k : ℕ} (j : Fin P.componentCount) (C : J.Current k)
    (hC : C ∈ finiteSphericalPolyhedralCurrents P D A k) :
    D.restrict j k C ∈ cellwiseSphericalPolyhedralCurrents (P.triangulation j) (A j) k := by
  have hle : finiteSphericalPolyhedralCurrents P D A k ≤
      (cellwiseSphericalPolyhedralCurrents (P.triangulation j) (A j) k).comap (D.restrict j k) := by
    apply (AddSubgroup.closure_le _).mpr
    rintro _ ⟨⟨l,Q,hQ⟩,rfl⟩
    change D.restrict j k ((D.inclusion l).push k ⟨Q,subset_univ _⟩) ∈
      cellwiseSphericalPolyhedralCurrents (P.triangulation j) (A j) k
    by_cases he : j = l
    · subst l
      rw [D.restrict_self]
      exact hQ
    · rw [D.restrict_other j l he]
      exact AddSubgroup.zero_mem _
  exact hle hC

end Paper28
