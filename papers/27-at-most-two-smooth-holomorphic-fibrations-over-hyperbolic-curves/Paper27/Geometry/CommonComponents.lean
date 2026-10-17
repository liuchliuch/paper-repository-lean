import Paper27.Geometry.RamificationDichotomy

/-!
# Identifying the actual common compact components

Tangency everywhere first gives containment in the actual ramification set.
Connectedness and finite disjoint compact components then give equality with
one actual component. Equality is proved for the embedded images; an actual
base biholomorphism between the two curve parametrizations is constructed
separately from the general map-into-submanifold and inverse theorems.
-/
noncomputable section
open scoped Manifold
namespace Paper27.Geometry
variable {X : CompactComplexSurface}

theorem common_components_of_tangency (factor : HolomorphicEmbeddedFactorization)
    (curveMaps : NonconstantCompactCurveMapTheorem)
    (f g h : Fibration X) (D : EmbeddedCurve X)
    (F : RamificationCurveFamily f h) (G : RamificationCurveFamily g h)
    (hfh : D.TangentToPair f h) (hgh : D.TangentToPair g h) :
    ∃ (i : F.Index) (j : G.Index),
      D.support = (F.member i).support ∧ D.support = (G.member j).support := by
  let p := D.curve.basepoint
  have hFsub : D.support ⊆ F.toDisjointCurveFamily.support := by
    rw [F.support_eq]
    exact hfh
  have hGsub : D.support ⊆ G.toDisjointCurveFamily.support := by
    rw [G.support_eq]
    exact hgh
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hFsub ⟨p, rfl⟩)
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (hGsub ⟨p, rfl⟩)
  exact ⟨i, j,
    F.toDisjointCurveFamily.component_eq_of_meets factor curveMaps D hFsub i p hi,
    G.toDisjointCurveFamily.component_eq_of_meets factor curveMaps D hGsub j p hj⟩

/-- The common alternative of the actual dichotomy identifies the actual
supports in both other pairs. It is stronger than mere pointwise tangency. -/
theorem ramification_component_disjoint_or_common
    (factor : HolomorphicEmbeddedFactorization) (curveMaps : NonconstantCompactCurveMapTheorem)
    (metrics : MetricTangency.HyperbolicMetricTheory)
    (calculus : EmbeddedFrames.HolomorphicFrameCalculus)
    (theory : LineBundleDegreeTheory) (homLaw : HomDegreeLaw theory)
    (f g h : Fibration X) (hf : f.Smooth) (hg : g.Smooth) (hh : h.Smooth)
    (hB : f.Hyperbolic) (hC : g.Hyperbolic) (hH : h.Hyperbolic)
    (D : EmbeddedCurve X) (A : ComponentNormalData D) (hD : D.curve.Hyperbolic)
    (hDf : D.Unramified f) (hDg : D.Unramified g) (hDfg : D.TangentToPair f g)
    (F : RamificationCurveFamily f h) (G : RamificationCurveFamily g h) :
    (D.DisjointFromPair f h ∧ D.DisjointFromPair g h) ∨
      (D.TangentToPair f h ∧ D.TangentToPair g h ∧
        ∃ (i : F.Index) (j : G.Index),
          D.support = (F.member i).support ∧ D.support = (G.member j).support) := by
  rcases ramification_component_dichotomy metrics calculus theory homLaw f g h hf hg hh
    hB hC hH D A hD hDf hDg hDfg F G with hd | ⟨hfh, hgh⟩
  · exact Or.inl hd
  · exact Or.inr ⟨hfh, hgh, common_components_of_tangency factor curveMaps f g h D F G hfh hgh⟩

/-- Equality of actual embedded images supplies the actual biholomorphism
between their parametrizing curves, with no ambient surface automorphism. -/
theorem embedded_curves_biholomorphic_of_support_eq
    (factor : HolomorphicEmbeddedFactorization) (inverseTheorem : BijectiveHolomorphicInverse)
    (D E : EmbeddedCurve X) (heq : D.support = E.support) :
    ∃ a : Biholomorphism D.curve E.curve,
      ∀ p : D.curve, E.inclusion (a p) = D.inclusion p := by
  obtain ⟨a, ha⟩ := factor X D E heq.subset
  have hi : Function.Injective a := by
    intro p q hpq
    apply D.embedding.injective
    rw [← ha p, ← ha q, hpq]
  have hs : Function.Surjective a := by
    intro q
    have hq : E.inclusion q ∈ D.support := heq.symm ▸ Set.mem_range_self q
    obtain ⟨p, hp⟩ := hq
    refine ⟨p, E.embedding.injective ?_⟩
    exact (ha p).trans hp
  let e := Equiv.ofBijective a ⟨hi, hs⟩
  exact ⟨⟨e, a.holomorphic, inverseTheorem D.curve E.curve e a.holomorphic⟩, ha⟩

end Paper27.Geometry
