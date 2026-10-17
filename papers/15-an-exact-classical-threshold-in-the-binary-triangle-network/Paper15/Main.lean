import Paper15.Basic
import Paper15.Threshold
import Paper15.Attainment
import Paper15.Regularity
import Paper15.Stationary
import Paper15.Reduction
import Paper15.FiniteGap

/-!
# Theorem 1 and Corollary 2

Independently readable statements of the paper's main results.

*Attainment* (the existence half of Theorem 1 and the easy half of
Corollary 2 at `t = t_*`) is proved outright from `Paper15.Attainment`.

*Sharp upper bound (still incomplete).* The finite ternary maximizer exists,
and certificate-tree soundness is proved. The full general-model reduction,
the exhaustive Lean verification for Lemma 5, and the optimization/boundary
argument on the exceptional orbit remain missing. The statements suffixed
`of_gap` below are conditional scaffolding and are not counted as proofs of
the paper's Theorem 1. Neither `GapHypothesis` nor `ExcHypothesis` is an
external-theorem exemption: both are obligations within this paper.

`Paper15.OutputLaw` proves the sufficiency direction of Corollary 2 for the
actual output distribution, including measurable kernels and independent noise.
-/

noncomputable section

namespace Paper15

open Real

/-- `exceptionalM2Final y = 1/y + 2y - 3`. -/
lemma exceptionalM2Final_eq (y : ℝ) : exceptionalM2Final y = 1 / y + 2 * y - 3 := rfl

/-- The attained value `1/y + 2y - 3` at the unique quartic root `y` equals `t_*`. -/
theorem attained_value_eq_tStar : 1 / yRoot + 2 * yRoot - 3 = tStar := by
  have hmem : (1 / yRoot + 2 * yRoot - 3) ∈ Set.Ioo nineTwentyFifths (37 / 100 : ℝ) := by
    simpa [nineTwentyFifths] using attained_t_bounds
  have hrt : thresholdPoly (1 / yRoot + 2 * yRoot - 3) = 0 := thresholdPoly_yRoot
  exact tStar_unique hmem hrt

/-- Attainment: the exceptional table with law (8) produces moments `(0,t_*,0)`. -/
theorem attaining_moments_tStar :
    detMoments DetTriangle.exceptional (law3 xAtt yAtt zAtt) (law3 xAtt yAtt zAtt)
        (law3 xAtt yAtt zAtt) = AggregateMoments.mk 0 tStar 0 := by
  rw [attaining_moments]
  congr 1
  rw [exceptionalM2Final_eq]
  show (1 / yAtt + 2 * yAtt - 3) = tStar
  have hy : yAtt = yRoot := rfl
  rw [hy]
  exact attained_value_eq_tStar

/-- For every `t ≥ 0`, independent sign noise of mean `√(t/t_*)` maps
the attaining moments `(0,t_*,0)` to `(0,t,0)`. -/
theorem scale_attains (t : ℝ) (ht : 0 ≤ t) :
    (AggregateMoments.mk 0 tStar 0).scaleSigns (sqrt (t / tStar))
      = AggregateMoments.mk 0 t 0 :=
  scaleSigns_attains_p_t tStar_pos ht rfl

/-- Attaining source law as a point of `Δ₂`. -/
def attLaw : Simplex2 where
  v := law3 xAtt yAtt zAtt
  nonneg i := by
    fin_cases i <;> simp [law3, xAtt_pos.le, yAtt_pos.le, zAtt_pos.le]
  sum_eq := by
    have h := xAtt_add_yAtt_add_zAtt
    rw [Fin.sum_univ_three]
    simp [law3]
    linarith

/-- The attaining finite model has moments `(0,t_*,0)`. -/
theorem attaining_fin_local : IsFinTriangleLocal tStar := by
  refine ⟨DetTriangle.exceptional, attLaw, attLaw, attLaw, ?_, ?_, ?_⟩
  · have h := attaining_moments_tStar
    have h1 := congrArg AggregateMoments.M1 h
    simpa [detMoments', attLaw] using h1
  · have h := attaining_moments_tStar
    have h2 := congrArg AggregateMoments.M2 h
    simpa [detMoments', attLaw] using h2
  · have h := attaining_moments_tStar
    have h3 := congrArg AggregateMoments.M3 h
    simpa [detMoments', attLaw] using h3

/-- **Theorem 1, attainment half.**  The bound `t_*` is attained by a finite
deterministic ternary model, hence is sharp. -/
theorem theorem1_attained : IsFinTriangleLocal tStar :=
  attaining_fin_local

/-- `t_*` is the unique root of `thresholdPoly` in `(9/25, 37/100)`. -/
theorem tStar_characterization :
    thresholdPoly tStar = 0 ∧
      tStar ∈ Set.Ioo nineTwentyFifths (37 / 100 : ℝ) ∧
      ∀ t, t ∈ Set.Ioo nineTwentyFifths (37 / 100 : ℝ) →
        thresholdPoly t = 0 → t = tStar :=
  ⟨thresholdPoly_tStar, tStar_mem, fun _t ht h => tStar_unique ht h⟩

/-! ## Finite sharp bound from the certificate gap

`GapHolds T` says every constrained source law for table `T` has
`M2 ≤ 9/25`.  Certificate trees prove `GapHolds` (`gapHolds_of_certTree`).
The exceptional orbit is excluded from that bound (`not_gapHolds_exceptional`)
and is controlled by `tStar` instead.  The two hypotheses below are UNPROVED obligations. The gap is the paper's
own computational result; the exceptional bound is its analytic result.
-/

/-- Hypothesis: every deterministic ternary table outside the exceptional
orbit satisfies the `9/25` gap. -/
def GapHypothesis : Prop :=
  ∀ T : DetTriangle, ¬ inExceptionalOrbit T → GapHolds T

/-- Hypothesis: on the exceptional orbit, every constrained source law has
`M2 ≤ t_*`. -/
def ExcHypothesis : Prop :=
  ∀ (T : DetTriangle), inExceptionalOrbit T →
    ∀ (qx qy qz : Simplex2),
      (detMoments' T qx qy qz).M1 = 0 →
      (detMoments' T qx qy qz).M3 = 0 →
        (detMoments' T qx qy qz).M2 ≤ tStar

/-- **Theorem 1, finite form.**  Given the certificate gap hypotheses, every
deterministic ternary model with `M1 = M3 = 0` satisfies `M2 ≤ t_*`. -/
theorem theorem1_finite_of_gap (hgap : GapHypothesis) (hexc : ExcHypothesis) :
    ∀ (T : DetTriangle) (qx qy qz : Simplex2),
      (detMoments' T qx qy qz).M1 = 0 →
      (detMoments' T qx qy qz).M3 = 0 →
        (detMoments' T qx qy qz).M2 ≤ tStar := by
  intro T qx qy qz h1 h3
  by_cases he : inExceptionalOrbit T
  · exact hexc T he qx qy qz h1 h3
  · have hgapT := hgap T he
    have h9 : (detMoments' T qx qy qz).M2 ≤ nineTwentyFifths := hgapT qx qy qz h1 h3
    exact le_of_lt (lt_of_le_of_lt h9 nineTwentyFifths_lt_tStar)

/-- **Theorem 1, constrained-max form (finite).**  Under the gap hypotheses,
the global maximizer of `M2` on `{M1 = M3 = 0}` produced by Lemma 4 has value
at most `t_*`. -/
theorem theorem1_max_M2_of_gap (hgap : GapHypothesis) (hexc : ExcHypothesis) :
    ∀ (T : DetTriangle) (qx qy qz : Simplex2),
      (detMoments' T qx qy qz).M1 = 0 →
      (detMoments' T qx qy qz).M3 = 0 →
        (detMoments' T qx qy qz).M2 ≤ tStar :=
  theorem1_finite_of_gap hgap hexc

/-- Under the gap hypotheses the finite sharp bound is `t_*`, and it is
attained: `max {M2 | M1 = M3 = 0}` over deterministic ternary models equals
`t_*`. -/
theorem theorem1_finite_sharp (hgap : GapHypothesis) (hexc : ExcHypothesis) :
    IsFinTriangleLocal tStar ∧
      (∀ (T : DetTriangle) (qx qy qz : Simplex2),
        (detMoments' T qx qy qz).M1 = 0 →
        (detMoments' T qx qy qz).M3 = 0 →
          (detMoments' T qx qy qz).M2 ≤ tStar) :=
  ⟨attaining_fin_local, theorem1_finite_of_gap hgap hexc⟩

/-- **Corollary 2, finite upper half.**  Under the gap hypotheses, a finite
deterministic ternary model producing `(0,t,0)` requires `t ≤ t_*`. -/
theorem corollary2_fin_le (hgap : GapHypothesis) (hexc : ExcHypothesis)
    (t : ℝ) (ht : IsFinTriangleLocal t) : t ≤ tStar := by
  obtain ⟨T, qx, qy, qz, h1, h2, h3⟩ := ht
  have := theorem1_finite_of_gap hgap hexc T qx qy qz h1 h3
  linarith

/-- **Corollary 2, attainment at `t_*`.**  The endpoint `t = t_*` is finite
triangle-local. -/
theorem corollary2_fin_attained : IsFinTriangleLocal tStar :=
  attaining_fin_local


end Paper15
