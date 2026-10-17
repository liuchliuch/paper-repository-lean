import Paper27.Geometry.MetricTangency
import Paper27.Geometry.EmbeddedFrames
import Paper27.Geometry.CurveFamilies
import Paper27.Geometry.RetractionAtlas

/-!
# The actual third-fibration dichotomy along a ramification component

The records below are intermediate geometric OUTPUT data, not new external
theorems. In particular no dichotomy, covector equality, or negative-degree
conclusion is a field. Raw normal-transition jets give the normal tensor and
negative Hom degree; intersection metric rigidity gives the third unramified
restriction; the constructed quotient section then gives actual tangency.
-/
noncomputable section
open scoped Manifold
open Polynomial
namespace Paper27.Geometry

variable {X : CompactComplexSurface}

/-- Raw normal-frame Taylor data for a compact embedded curve. The nth tensor
and negative-degree conclusions are derived below, not supplied as fields. -/
structure ComponentNormalData (D : EmbeddedCurve X) where
  normal : HolomorphicLineCocycle D.curve
  tangent : TangentLineCocycle D.curve
  exponent : ℕ
  exponent_ge_two : 2 ≤ exponent
  frames : EmbeddedFrames.RawEmbeddedFrames D normal tangent.bundle
  Y : D.curve → D.curve → D.curve → ℂ[X]
  H : D.curve → D.curve → D.curve → ℂ[X]
  F : D.curve → D.curve → D.curve → ℂ[X]
  normal_jet : ∀ i j p, p ∈ D.curve.chartDomain i → p ∈ D.curve.chartDomain j →
    Y i j p = NormalJets.normalChange exponent (normal.transition i j p) (H i j p)
  base_jet : ∀ i j p, p ∈ D.curve.chartDomain i → p ∈ D.curve.chartDomain j →
    (F i j p).coeff 1 = D.curve.chartJacobian i j p
  raw_power : ∀ i j p, p ∈ D.curve.chartDomain i → p ∈ D.curve.chartDomain j →
    (Y i j p ^ exponent).coeff exponent =
      ((F i j p).comp (Polynomial.X ^ exponent) - C ((F i j p).coeff 0)).coeff exponent

namespace ComponentNormalData

theorem degree_facts (theory : LineBundleDegreeTheory) {D : EmbeddedCurve X}
    (A : ComponentNormalData D) (hD : D.curve.Hyperbolic) :
    (A.exponent : ℤ) * theory.degree D.curve A.normal =
      theory.degree D.curve A.tangent.bundle ∧ theory.degree D.curve A.normal < 0 := by
  obtain ⟨_, ht, hn⟩ := RetractionAtlas.normal_tensor_degree_from_raw_jets theory
    D.curve A.normal A.tangent A.exponent A.exponent_ge_two hD A.Y A.H A.F
    A.normal_jet A.base_jet A.raw_power
  exact ⟨ht.trans (theory.tangent_degree D.curve A.tangent).symm, hn⟩

end ComponentNormalData

/-- The smooth/disjoint/covering part of the ramification geometry. This is
output data to be constructed from finite analytic germs, not an external
replacement for Proposition 2.4. -/
structure RamificationCurveFamily (f g : Fibration X) extends DisjointCurveFamily X where
  support_eq : toDisjointCurveFamily.support = RamificationSupport.ramificationSet f g
  hyperbolic : ∀ i, (member i).curve.Hyperbolic
  first_unramified : ∀ i, (member i).Unramified f
  second_unramified : ∀ i, (member i).Unramified g

namespace EmbeddedCurve

/-- Symmetry follows from swapping the two actual coordinate values. -/
theorem tangentToPair_symm (D : EmbeddedCurve X) (f g : Fibration X)
    (h : D.TangentToPair f g) : D.TangentToPair g f := by
  intro p hp hsurj
  apply h hp
  apply (CoordinateCalculus.pairMap_surjective_iff f g p).mpr
  have hs := (CoordinateCalculus.pairMap_surjective_iff g f p).mp hsurj
  intro ab
  obtain ⟨v, hv⟩ := hs (ab.2, ab.1)
  exact ⟨v, Prod.ext (congrArg Prod.snd hv) (congrArg Prod.fst hv)⟩

/-- Two actual tangencies sharing a nonzero covector imply the third one. -/
theorem tangentToPair_trans (D : EmbeddedCurve X) (f g h : Fibration X)
    (hf : f.Smooth) (hg : g.Smooth) (hh : h.Smooth)
    (hfg : D.TangentToPair f g) (hfh : D.TangentToPair f h) : D.TangentToPair g h := by
  intro p hp hsurj
  let lf : (ℂ × ℂ) →L[ℂ] ℂ := mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ) f p
  let lg : (ℂ × ℂ) →L[ℂ] ℂ := mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ) g p
  let lh : (ℂ × ℂ) →L[ℂ] ℂ := mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ) h p
  have nfg : ¬ Function.Surjective (fun v : ℂ × ℂ => (lf v, lg v)) :=
    fun hs => hfg hp ((CoordinateCalculus.pairMap_surjective_iff f g p).mpr hs)
  have nfh : ¬ Function.Surjective (fun v : ℂ × ℂ => (lf v, lh v)) :=
    fun hs => hfh hp ((CoordinateCalculus.pairMap_surjective_iff f h p).mpr hs)
  obtain ⟨a, ⟨ha0, ha⟩, _⟩ := RamificationCovectors.existsUnique_nonzero_slope
    lf.toLinearMap lg.toLinearMap (hf p) (hg p) nfg
  obtain ⟨b, ⟨_, hb⟩, _⟩ := RamificationCovectors.existsUnique_nonzero_slope
    lf.toLinearMap lh.toLinearMap (hf p) (hh p) nfh
  have hcoord : Function.Surjective (fun v : ℂ × ℂ => (lg v, lh v)) :=
    (CoordinateCalculus.pairMap_surjective_iff g h p).mp hsurj
  obtain ⟨v, hv⟩ := hcoord ((0 : ℂ), (1 : ℂ))
  have hgv : lg v = 0 := congrArg Prod.fst hv
  have hhv : lh v = 1 := congrArg Prod.snd hv
  have hfv : lf v = 0 := (mul_eq_zero.mp ((ha v).symm.trans hgv)).resolve_left ha0
  have hbv : lh v = b * lf v := hb v
  rw [hfv, mul_zero, hhv] at hbv
  exact one_ne_zero hbv

end EmbeddedCurve

/-- The substantive intersection-to-everywhere implication in Lemma 3.1.
Neither an unramified third restriction nor covector equality is an input. -/
theorem tangency_from_intersection
    (metrics : MetricTangency.HyperbolicMetricTheory)
    (calculus : EmbeddedFrames.HolomorphicFrameCalculus)
    (theory : LineBundleDegreeTheory) (homLaw : HomDegreeLaw theory)
    (f h : Fibration X) (hf : f.Smooth) (hh : h.Smooth)
    (hB : f.Hyperbolic) (hC : h.Hyperbolic)
    (D E : EmbeddedCurve X) (A : ComponentNormalData D)
    (hD : D.curve.Hyperbolic) (hE : E.curve.Hyperbolic)
    (hDf : D.Unramified f) (hEf : E.Unramified f) (hEh : E.Unramified h)
    (hEtangent : E.TangentToPair f h)
    (p : D.curve) (q : E.curve) (hpq : D.inclusion p = E.inclusion q) :
    D.TangentToPair f h := by
  have hDh : D.Unramified h := MetricTangency.third_restriction_unramified_of_intersection
    metrics f h hf hh hB hC D.inclusion E.inclusion hD hE p q hpq
    (hEtangent ⟨q, rfl⟩) hDf hEf hEh
  obtain ⟨ht, hn⟩ := A.degree_facts theory hD
  exact EmbeddedFrames.tangentToPair_from_normal_tensor calculus theory homLaw A.frames
    f h hDf hDh A.exponent A.exponent_ge_two hn ht

/-- The actual set-theoretic alternatives of Lemma 3.1. All geometric data is
explicit; the new metric/normal-quotient argument is carried out in the proof. -/
theorem ramification_component_dichotomy
    (metrics : MetricTangency.HyperbolicMetricTheory)
    (calculus : EmbeddedFrames.HolomorphicFrameCalculus)
    (theory : LineBundleDegreeTheory) (homLaw : HomDegreeLaw theory)
    (f g h : Fibration X) (hf : f.Smooth) (hg : g.Smooth) (hh : h.Smooth)
    (hB : f.Hyperbolic) (hC : g.Hyperbolic) (hH : h.Hyperbolic)
    (D : EmbeddedCurve X) (A : ComponentNormalData D) (hD : D.curve.Hyperbolic)
    (hDf : D.Unramified f) (hDg : D.Unramified g) (hDfg : D.TangentToPair f g)
    (F : RamificationCurveFamily f h) (G : RamificationCurveFamily g h) :
    (D.DisjointFromPair f h ∧ D.DisjointFromPair g h) ∨
      (D.TangentToPair f h ∧ D.TangentToPair g h) := by
  classical
  by_cases hd : D.DisjointFromPair f h ∧ D.DisjointFromPair g h
  · exact Or.inl hd
  right
  have hm : (∃ p : D.curve, D.inclusion p ∈ RamificationSupport.ramificationSet f h) ∨
      (∃ p : D.curve, D.inclusion p ∈ RamificationSupport.ramificationSet g h) := by
    by_contra hm
    apply hd
    push_neg at hm
    constructor
    · apply Set.disjoint_left.mpr
      rintro x ⟨p, rfl⟩ hx
      exact hm.1 p hx
    · apply Set.disjoint_left.mpr
      rintro x ⟨p, rfl⟩ hx
      exact hm.2 p hx
  rcases hm with ⟨p, hp⟩ | ⟨p, hp⟩
  · rw [← F.support_eq] at hp
    obtain ⟨i, q, hq⟩ := Set.mem_iUnion.mp hp
    have hE : (F.member i).TangentToPair f h := by
      intro x hx
      rw [← F.support_eq]
      exact Set.mem_iUnion.mpr ⟨i, hx⟩
    have hfh := tangency_from_intersection metrics calculus theory homLaw f h hf hh hB hH
      D (F.member i) A hD (F.hyperbolic i) hDf (F.first_unramified i)
      (F.second_unramified i) hE p q hq.symm
    exact ⟨hfh, D.tangentToPair_trans f g h hf hg hh hDfg hfh⟩
  · rw [← G.support_eq] at hp
    obtain ⟨i, q, hq⟩ := Set.mem_iUnion.mp hp
    have hE : (G.member i).TangentToPair g h := by
      intro x hx
      rw [← G.support_eq]
      exact Set.mem_iUnion.mpr ⟨i, hx⟩
    have hgh := tangency_from_intersection metrics calculus theory homLaw g h hg hh hC hH
      D (G.member i) A hD (G.hyperbolic i) hDg (G.first_unramified i)
      (G.second_unramified i) hE p q hq.symm
    exact ⟨D.tangentToPair_trans g f h hg hf hh (D.tangentToPair_symm f g hDfg) hgh, hgh⟩

end Paper27.Geometry
