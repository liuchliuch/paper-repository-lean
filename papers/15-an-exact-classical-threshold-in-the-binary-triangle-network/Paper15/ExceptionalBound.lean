import Paper15.Boundary
import Paper15.Lagrange

/-! # Global exceptional-orbit bound from the finite gap

Compactness supplies a maximum. Boundary exclusion supplies strict positivity,
and the actual Lagrange theorem then identifies its value with the threshold.
-/
noncomputable section
namespace Paper15
open Finset BigOperators Set Filter Topology

/-- Coordinates define honest source laws throughout the probability triangle. -/
def simplexOf (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : x+y ≤ 1) : Simplex2 where
  v := law3 x y (1-x-y)
  nonneg i := by
    fin_cases i
    · exact hx
    · exact hy
    · change 0 ≤ 1-x-y; linarith
  sum_eq := by simp only [Fin.sum_univ_three, law3_zero, law3_one, law3_two]; ring

lemma lawOf_simplexOf (x y : Fin 3 → ℝ) (a : Fin 3)
    (hx : 0 ≤ x a) (hy : 0 ≤ y a) (hxy : x a+y a ≤ 1) :
    lawOf x y a = (simplexOf (x a) (y a) hx hy hxy : Fin 3 → ℝ) := by
  funext i
  fin_cases i <;> simp [lawOf, simplexOf, law3, zOf]

lemma simplex_coordinates (q : Simplex2) : q 2 = 1-q 0-q 1 := by
  have hs := q.sum_eq
  rw [Fin.sum_univ_three] at hs
  linarith

/-- Strict physical interior is an open neighborhood in all six coordinates. -/
def SourceInterior : Set SourceCoords :=
  {p | ∀ i, 0 < p.1 i ∧ 0 < p.2 i ∧ p.1 i+p.2 i < 1}

lemma isOpen_SourceInterior : IsOpen SourceInterior := by
  have he : SourceInterior = ⋂ i : Fin 3,
      ({p : SourceCoords | 0 < p.1 i} ∩ {p | 0 < p.2 i} ∩ {p | p.1 i+p.2 i < 1}) := by
    ext p
    simp only [SourceInterior, mem_setOf_eq, mem_iInter, mem_inter_iff]
    aesop
  rw [he]
  apply isOpen_iInter_of_finite
  intro i
  exact ((isOpen_lt continuous_const (by fun_prop)).inter
    (isOpen_lt continuous_const (by fun_prop))).inter
    (isOpen_lt (by fun_prop) continuous_const)

/-- A maximum on the physical simplex is a constrained local maximum at
any interior point. -/
lemma physical_max_isLocalMax {x y : Fin 3 → ℝ}
    (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i) (hz : ∀ i, x i+y i < 1)
    (hglobal : ∀ (u v : Fin 3 → ℝ),
      (∀ i, 0 ≤ u i ∧ 0 ≤ v i ∧ u i+v i ≤ 1) →
      (momentsOf u v).M1 = (momentsOf x y).M1 →
      (momentsOf u v).M3 = (momentsOf x y).M3 →
      (momentsOf u v).M2 ≤ (momentsOf x y).M2) :
    IsLocalMaxOn (coordM 1)
      {p : SourceCoords | coordM 0 p = coordM 0 (x,y) ∧ coordM 2 p = coordM 2 (x,y)} (x,y) := by
  have hp : (x,y) ∈ SourceInterior := fun i => ⟨hx i, hy i, hz i⟩
  have hn : SourceInterior ∈ 𝓝 (x,y) := isOpen_SourceInterior.mem_nhds hp
  change ∀ᶠ p in 𝓝[{p : SourceCoords | coordM 0 p = coordM 0 (x,y) ∧
      coordM 2 p = coordM 2 (x,y)}] (x,y), coordM 1 p ≤ coordM 1 (x,y)
  filter_upwards [Filter.Eventually.filter_mono nhdsWithin_le_nhds hn, self_mem_nhdsWithin] with p hp hl
  apply hglobal p.1 p.2
  · exact fun i => ⟨(hp i).1.le, (hp i).2.1.le, (hp i).2.2.le⟩
  · exact hl.1
  · exact hl.2

/-- The exceptional table is bounded by tStar. Only the finite gap remains as
an external argument of this intermediate theorem; no optimizer or interiority
assumption is supplied. -/
theorem exceptional_bound_of_gap (hgap : GapHypothesis) :
    ConstrainedBound tStar DetTriangle.exceptional := by
  have hne : (feasibleSet DetTriangle.exceptional).Nonempty := by
    refine ⟨((attLaw : Fin 3 → ℝ), (attLaw : Fin 3 → ℝ), (attLaw : Fin 3 → ℝ)), ?_⟩
    refine ⟨⟨attLaw.nonneg, attLaw.sum_eq⟩, ⟨attLaw.nonneg, attLaw.sum_eq⟩,
      ⟨attLaw.nonneg, attLaw.sum_eq⟩, ?_, ?_⟩
    · exact congrArg AggregateMoments.M1 attaining_moments_tStar
    · exact congrArg AggregateMoments.M3 attaining_moments_tStar
  obtain ⟨p, hp, hmax⟩ := exists_isMaxOn_M2 hne
  let qs : Fin 3 → Simplex2 := ![⟨p.1, hp.1.1, hp.1.2⟩,
    ⟨p.2.1, hp.2.1.1, hp.2.1.2⟩, ⟨p.2.2, hp.2.2.1.1, hp.2.2.1.2⟩]
  have hm1 : (detMoments' DetTriangle.exceptional (qs 0) (qs 1) (qs 2)).M1 = 0 := hp.2.2.2.1
  have hm3 : (detMoments' DetTriangle.exceptional (qs 0) (qs 1) (qs 2)).M3 = 0 := hp.2.2.2.2
  have hhigh : nineTwentyFifths < (detMoments' DetTriangle.exceptional (qs 0) (qs 1) (qs 2)).M2 := by
    have hv := hmax ((attLaw : Fin 3 → ℝ), (attLaw : Fin 3 → ℝ), (attLaw : Fin 3 → ℝ))
      ⟨⟨attLaw.nonneg, attLaw.sum_eq⟩, ⟨attLaw.nonneg, attLaw.sum_eq⟩,
        ⟨attLaw.nonneg, attLaw.sum_eq⟩, congrArg AggregateMoments.M1 attaining_moments_tStar,
        congrArg AggregateMoments.M3 attaining_moments_tStar⟩
    have he2 := congrArg AggregateMoments.M2 attaining_moments_tStar
    change (detMoments DetTriangle.exceptional attLaw.v attLaw.v attLaw.v).M2 = tStar at he2
    rw [he2] at hv
    exact lt_of_lt_of_le nineTwentyFifths_lt_tStar hv
  have hpos : ∀ a i, 0 < qs a i := by
    obtain ⟨hx, hy, hz⟩ := exceptional_positive_of_high hgap (qs 0) (qs 1) (qs 2) hm1 hm3 hhigh
    intro a
    fin_cases a <;> assumption
  let x : Fin 3 → ℝ := fun a => qs a 0
  let y : Fin 3 → ℝ := fun a => qs a 1
  have hxy (a : Fin 3) : x a+y a < 1 := by
    have he := simplex_coordinates (qs a)
    have hz := hpos a 2
    dsimp [x,y]
    linarith
  have hlaw (a : Fin 3) : lawOf x y a = (qs a : Fin 3 → ℝ) := by
    funext i
    fin_cases i
    · rfl
    · rfl
    · exact (simplex_coordinates (qs a)).symm
  have heq : detMoments' DetTriangle.exceptional (qs 0) (qs 1) (qs 2) = momentsOf x y := by
    rw [← detMoments_exceptional_lawOf]
    exact congrArg₂ (fun qx qy => detMoments DetTriangle.exceptional qx qy (qs 2))
      (hlaw 0).symm (hlaw 1).symm |>.trans (by rw [hlaw 2])
  have hglobal : ∀ (u v : Fin 3 → ℝ),
      (∀ i, 0 ≤ u i ∧ 0 ≤ v i ∧ u i+v i ≤ 1) →
      (momentsOf u v).M1 = (momentsOf x y).M1 →
      (momentsOf u v).M3 = (momentsOf x y).M3 →
      (momentsOf u v).M2 ≤ (momentsOf x y).M2 := by
    intro u v huv h1 h3
    have hu (a : Fin 3) : lawOf u v a ∈ stdSimplex ℝ (Fin 3) := by
      rw [lawOf_simplexOf u v a (huv a).1 (huv a).2.1 (huv a).2.2]
      exact ⟨(simplexOf _ _ _ _ _).nonneg, (simplexOf _ _ _ _ _).sum_eq⟩
    have h := hmax (lawOf u v 0, lawOf u v 1, lawOf u v 2)
      ⟨hu 0, hu 1, hu 2, ?_, ?_⟩
    · rw [detMoments_exceptional_lawOf] at h
      exact h.trans_eq (congrArg AggregateMoments.M2 heq)
    · rw [detMoments_exceptional_lawOf, h1]
      exact (congrArg AggregateMoments.M1 heq).symm.trans hm1
    · rw [detMoments_exceptional_lawOf, h3]
      exact (congrArg AggregateMoments.M3 heq).symm.trans hm3
  have hvalue := exceptional_localMax_value (fun i => hpos i 0) (fun i => hpos i 1) hxy
    (by simpa only [heq] using hm1) (by simpa only [heq] using hm3)
    (physical_max_isLocalMax (fun i => hpos i 0) (fun i => hpos i 1) hxy hglobal)
  intro qx qy qz h1 h3
  have h := hmax ((qx : Fin 3 → ℝ), (qy : Fin 3 → ℝ), (qz : Fin 3 → ℝ))
    ⟨⟨qx.nonneg, qx.sum_eq⟩, ⟨qy.nonneg, qy.sum_eq⟩, ⟨qz.nonneg, qz.sum_eq⟩, h1, h3⟩
  exact h.trans_eq ((congrArg AggregateMoments.M2 heq).trans hvalue)

/-- The exceptional-orbit hypothesis is discharged from the finite gap. -/
theorem excHypothesis_of_gap (hgap : GapHypothesis) : ExcHypothesis := by
  intro T hT
  exact constrainedBound_exceptionalOrbit (exceptional_bound_of_gap hgap) hT

theorem theorem1_finite_of_gap_only (hgap : GapHypothesis) :
    ∀ (T : DetTriangle) (qx qy qz : Simplex2),
      (detMoments' T qx qy qz).M1 = 0 → (detMoments' T qx qy qz).M3 = 0 →
      (detMoments' T qx qy qz).M2 ≤ tStar :=
  theorem1_finite_of_gap hgap (excHypothesis_of_gap hgap)

end Paper15
