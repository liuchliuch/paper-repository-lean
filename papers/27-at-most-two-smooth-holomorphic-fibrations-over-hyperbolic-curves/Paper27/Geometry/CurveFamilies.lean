import Paper27.Geometry.EmbeddedCurve
import Mathlib.Topology.Connected.Clopen

/-!
# Connected curves in finite disjoint curve families

The supports are ranges of actual holomorphic embeddings. Compactness makes
them closed. A connected curve contained in their finite disjoint union lies
in one member; the proof constructs the clopen preimage. The generic
submanifold-factorization theorem is kept separate from this own component
argument and from compact-curve surjectivity.
-/
noncomputable section
open scoped Manifold
namespace Paper27.Geometry

variable {X : CompactComplexSurface}

theorem EmbeddedCurve.support_isClosed (D : EmbeddedCurve X) : IsClosed D.support := by
  exact (isCompact_range D.inclusion.holomorphic.continuous).isClosed

/-- The elementary data of a finite disjoint family of actual compact curves.
There is no assertion that a ramification set has such a family here. -/
structure DisjointCurveFamily (X : CompactComplexSurface) where
  Index : Type
  [finite : Finite Index]
  member : Index → EmbeddedCurve X
  disjoint : Pairwise (fun i j => Disjoint (member i).support (member j).support)

attribute [instance] DisjointCurveFamily.finite

namespace DisjointCurveFamily

/-- The actual union of curve supports. -/
def support (F : DisjointCurveFamily X) : Set X := ⋃ i, (F.member i).support

/-- A connected actual curve in a finite disjoint union cannot pass from one
closed component to another. -/
theorem contained_in_member_of_meets (F : DisjointCurveFamily X)
    (D : EmbeddedCurve X) (hsub : D.support ⊆ F.support)
    (j : F.Index) (p : D.curve) (hp : D.inclusion p ∈ (F.member j).support) :
    D.support ⊆ (F.member j).support := by
  let A : Set D.curve := D.inclusion ⁻¹' (F.member j).support
  let J := {i : F.Index // i ≠ j}
  let B : Set D.curve := ⋃ i : J, D.inclusion ⁻¹' (F.member i.val).support
  have hAc : IsClosed A := (F.member j).support_isClosed.preimage
    D.inclusion.holomorphic.continuous
  have hBc : IsClosed B := isClosed_iUnion_of_finite fun i : J =>
    (F.member i.val).support_isClosed.preimage D.inclusion.holomorphic.continuous
  have hcompl : Aᶜ = B := by
    ext x
    constructor
    · intro hx
      have hcov := hsub ⟨x, rfl⟩
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hcov
      have hij : i ≠ j := by
        intro heq
        subst i
        exact hx hi
      exact Set.mem_iUnion.mpr ⟨⟨i, hij⟩, hi⟩
    · intro hx hA
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
      exact Set.disjoint_left.mp (F.disjoint i.property) hi hA
  have hAo : IsOpen A := by
    rw [← isClosed_compl_iff, hcompl]
    exact hBc
  have hAu : A = Set.univ := (show IsClopen A from ⟨hAc, hAo⟩).eq_univ ⟨p, hp⟩
  rintro _ ⟨x, rfl⟩
  have hx : x ∈ A := by rw [hAu]; trivial
  exact hx

end DisjointCurveFamily

/-- The usual map-into-an-embedded-complex-submanifold criterion, for actual
maps and embeddings. This generic analytic input contains no component,
ramification, tangency or degree conclusion. -/
def HolomorphicEmbeddedFactorization : Prop :=
  ∀ (X : CompactComplexSurface) (D E : EmbeddedCurve X), D.support ⊆ E.support →
    ∃ a : HolomorphicMap D.curve E.curve, ∀ p : D.curve,
      E.inclusion (a p) = D.inclusion p

/-- Compactness and the actual nonconstant curve-map theorem turn containment
between compact embedded curves into equality of their actual images. -/
theorem embeddedCurve_support_eq_of_subset (factor : HolomorphicEmbeddedFactorization)
    (maps : NonconstantCompactCurveMapTheorem) (D E : EmbeddedCurve X)
    (hsub : D.support ⊆ E.support) : D.support = E.support := by
  obtain ⟨a, ha⟩ := factor X D E hsub
  have hi : Function.Injective a := by
    intro p q hpq
    apply D.embedding.injective
    rw [← ha p, ← ha q, hpq]
  obtain ⟨p, q, hpq⟩ := D.curve.exists_distinct
  have hnc : ∃ p q : D.curve, a p ≠ a q := ⟨p, q, fun h => hpq (hi h)⟩
  have hs := (maps D.curve E.curve a hnc).2
  apply Set.Subset.antisymm hsub
  rintro _ ⟨e, rfl⟩
  obtain ⟨d, hd⟩ := hs e
  exact ⟨d, by rw [← ha d, hd]⟩

/-- Once actual tangency proves containment in the other ramification set,
this identifies the actual compact component, rather than just one point. -/
theorem DisjointCurveFamily.component_eq_of_meets
    (factor : HolomorphicEmbeddedFactorization) (maps : NonconstantCompactCurveMapTheorem)
    (F : DisjointCurveFamily X) (D : EmbeddedCurve X) (hsub : D.support ⊆ F.support)
    (j : F.Index) (p : D.curve) (hp : D.inclusion p ∈ (F.member j).support) :
    D.support = (F.member j).support :=
  embeddedCurve_support_eq_of_subset factor maps D (F.member j)
    (F.contained_in_member_of_meets D hsub j p hp)

end Paper27.Geometry
