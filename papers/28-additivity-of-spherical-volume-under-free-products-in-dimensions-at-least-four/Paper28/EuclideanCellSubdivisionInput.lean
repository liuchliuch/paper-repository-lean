import Paper28.EuclideanPolyhedralCurrents
import Paper28.SupportedCurrents

/-! The classical common affine subdivision object, together with standard
additivity of canonical affine integration. The input is universal on
finite Euclidean convex cells; it contains no spherical map, retraction,
approximation, mass, homology, cycle or filling conclusion. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Set

structure AffineCellCurrentDecomposition {d k : ℕ}
    {I : CompactIntegralCurrentAlgebraInput.{0,0} (EuclideanAmbient d) inferInstance}
    (S : EuclideanSimplexIntegrationInput d I) {Idx : Type} (pieces : Idx → Set (EuclideanAmbient d))
    (U : Set (EuclideanAmbient d)) (Q : I.Current k) where
  count : ℕ
  coefficient : Fin count → ℤ
  simplex : Fin count → AffineSimplexVertices d k
  cell : Fin count → Idx
  location : ∀ i, convexHull ℝ (Set.range (simplex i)) ⊆ U ∩ pieces (cell i)
  eq_sum : Q = ∑ i, coefficient i • S.integration k (simplex i)

structure EuclideanPolyhedralCellSubdivisionInput {d : ℕ}
    (I : CompactIntegralCurrentAlgebraInput.{0,0} (EuclideanAmbient d) inferInstance)
    (S : EuclideanSimplexIntegrationInput d I) : Prop where
  subdivision : ∀ {Idx : Type} [Fintype Idx] (vertices : Idx → Set (EuclideanAmbient d)),
    (∀ j, (vertices j).Finite) → ∀ (U : Set (EuclideanAmbient d)), IsOpen U →
    U ⊆ ⋃ j, convexHull ℝ (vertices j) →
    ∀ k (Q : supportedCurrents I U k), Q.val ∈ euclideanPolyhedralCurrents S k →
      Nonempty (AffineCellCurrentDecomposition S (fun j => convexHull ℝ (vertices j)) U Q.val)

end Paper28
