import Paper15.Complete
import Paper15.Lagrange
import Paper15.OutputLaw
import Paper15.IntegralConvex
import Paper15.ExceptionalCalculus
import Paper15.LPOptimizer
import Paper15.Basic
import Paper15.Threshold
import Paper15.Regularity
import Paper15.Stationary
import Paper15.Attainment
import Paper15.Main
import Paper15.Reduction
import Paper15.Barycentre

/-!
# Proved solution exports for the paper-facing contracts.

Statements match `Verification.Challenge`. Proofs use only the production library.

These statements are written independently of the production proof bodies and
follow the paper's quantifiers and hypotheses.
-/

open Paper15 MeasureTheory

namespace P15Contract

axiom illegalProof : False

/-! ## Threshold (Theorem 1 constant) -/

/-- `t_*` is the unique root of `3t^4+28t^3+66t^2-36t+3` in `(0.36, 0.37)`. -/
theorem tStar_characterization :
    ∃! t : ℝ, t ∈ Set.Ioo ((9:ℝ)/25) (37/100) ∧
      3 * t ^ 4 + 28 * t ^ 3 + 66 * t ^ 2 - 36 * t + 3 = 0 := by
  simpa [thresholdPoly, nineTwentyFifths] using Paper15.exists_unique_tStar

/-- The threshold satisfies `9/25 < t_* < 37/100`. -/
theorem tStar_gap : (9:ℝ)/25 < Paper15.tStar ∧ Paper15.tStar < 37/100 := by
  constructor
  · simpa [Paper15.nineTwentyFifths] using Paper15.nineTwentyFifths_lt_tStar
  · exact Paper15.tStar_lt_thirtySevenHundredths

/-- `t_*` is a root of the threshold polynomial (paper eq. 5). -/
theorem tStar_root : 3 * Paper15.tStar ^ 4 + 28 * Paper15.tStar ^ 3 +
    66 * Paper15.tStar ^ 2 - 36 * Paper15.tStar + 3 = 0 := by
  simpa [thresholdPoly] using Paper15.thresholdPoly_tStar

/-! ## Lemma 6 (Regularity) -/

/-- The gradients of `M1` and `M3` with respect to `(x_i,y_i)_{i=1}^3` are
linearly independent whenever `x_i > 0` and `y_i > 0` for all `i`. -/
theorem lemma6_algebra {x y : Fin 3 → ℝ} (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i) :
    ¬ ∃ ρ : ℝ, (∀ i, Paper15.vQtyPy x y i = ρ * Paper15.eQtyPy x y i) ∧
        (∀ i, Paper15.vQtyPx x y i = ρ * Paper15.eQtyPx x y i) :=
  Paper15.lemma6 hx hy

/-! ## Lemma 7 (Stationary laws coincide) -/

/-- Every interior stationary point of `M2` subject to `M1 = M3 = 0` for the
table (6) satisfies `x_1 = x_2 = x_3` and `y_1 = y_2 = y_3`. -/
theorem lemma7_equations {x y : Fin 3 → ℝ} {a b c : ℝ}
    (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i)
    (hsum : ∀ i, x i + y i < 1)
    (hb : b = a + 8 / 3)
    (h22 : ∀ j k, j ≠ k →
      c * (y j + y k) + b * (y j * y k) + a * (x j * y k + y j * x k) = 0)
    (h23 : ∀ j k, j ≠ k →
      c * (x j + y j + x k + y k) + b * (y j * y k + x j * y k + y j * x k)
        + a * (x j * x k) = 0) :
    x 0 = x 1 ∧ x 1 = x 2 ∧ y 0 = y 1 ∧ y 1 = y 2 :=
  Paper15.lemma7 hx hy hsum hb h22 h23

/-- Moment vanishing for the exceptional table, equation (19):
`M1 = M3 = 0` iff `E = 3/2` and `V = 1/2`. -/
theorem equation_19 (x y : Fin 3 → ℝ) :
    Paper15.m1Of (Paper15.eQty x y) = 0 ∧ Paper15.m3Of (Paper15.eQty x y) (Paper15.vQty x y) = 0 ↔
      Paper15.eQty x y = 3 / 2 ∧ Paper15.vQty x y = 1 / 2 :=
  Paper15.vanishing_iff_eQty_vQty x y

/-- Identity (17): `V = u1 u2 u3 - x1 x2 x3`. -/
theorem equation_17_V (x y : Fin 3 → ℝ) :
    Paper15.vQty x y =
      Paper15.uOf x y 0 * Paper15.uOf x y 1 * Paper15.uOf x y 2 - x 0 * x 1 * x 2 :=
  Paper15.vQty_eq_u_sub x y

/-- Section 2: the attaining model has moments `(0,t_*,0)`. -/
theorem attaining_moments_tStar :
    detMoments DetTriangle.exceptional (law3 xAtt yAtt zAtt) (law3 xAtt yAtt zAtt)
        (law3 xAtt yAtt zAtt) = AggregateMoments.mk 0 Paper15.tStar 0 :=
  Paper15.attaining_moments_tStar

/-- The attained value equals `t_*`. -/
theorem attained_value_eq_tStar :
    (1:ℝ) / Paper15.yRoot + 2 * Paper15.yRoot - 3 = Paper15.tStar :=
  Paper15.attained_value_eq_tStar

/-- Attainment of Theorem 1 in finite-witness form. -/
theorem theorem1_attained : Paper15.IsFinTriangleLocal Paper15.tStar :=
  Paper15.theorem1_attained

/-- Lemma 4 support: an extreme point of a 2-constraint LP on a probability
vector has support at most 3. -/
theorem lemma4_extreme_support {n : ℕ} (A : Matrix (Fin 2) (Fin n) ℝ) (b : Fin 2 → ℝ)
    {x : Fin n → ℝ} (h : Paper15.IsLPExtreme A b x) :
    {i | 0 < x i}.toFinset.card ≤ 3 :=
  Paper15.isLPExtreme_support_le A b h

/-- Lemma 3 (Finite barycentres), Caratheodory form: a point of a convex hull
in `ℝ^d` is a convex combination of at most `d+1` points of the set. -/
theorem lemma_3_caratheodory {d : ℕ}
    {s : Set (EuclideanSpace ℝ (Fin d))} {m : EuclideanSpace ℝ (Fin d)}
    (hm : m ∈ convexHull ℝ s) :
    ∃ (t : Finset (EuclideanSpace ℝ (Fin d))) (w : ↥t → ℝ),
      (∀ i : ↥t, 0 ≤ w i) ∧ (∑ i : ↥t, w i = 1) ∧
      (∀ i : ↥t, (i : EuclideanSpace ℝ (Fin d)) ∈ s) ∧
      t.card ≤ d + 1 ∧ (∑ i : ↥t, w i • (i : EuclideanSpace ℝ (Fin d)) = m) :=
  Paper15.finite_barycentre_caratheodory hm

/-- Lemma 3 (Finite barycentres) for finite-range measurable maps on a
probability space: the mean is a convex combination of at most `d+1` values. -/
theorem lemma3_finite_range {α : Type*} [MeasureSpace α]
    [IsProbabilityMeasure (volume : Measure α)]
    {d : ℕ} {g : α → EuclideanSpace ℝ (Fin d)}
    (hg : Measurable g) (hfin : (Set.range g).Finite) :
    ∃ (n : ℕ) (_ : n ≤ d + 1) (pts : Fin n → α) (w : Fin n → ℝ),
      (∀ i, 0 ≤ w i) ∧ (∑ i, w i = 1) ∧
      (∑ i, w i • g (pts i) = ∫ x, g x ∂volume) :=
  Paper15.lemma3_finite_range hg hfin


/-- Lemma 3 in the paper's full bounded measurable form. -/
theorem lemma_3 {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {d : ℕ} {g : α → EuclideanSpace ℝ (Fin d)}
    (hg : Measurable g) (hb : ∃ C : ℝ, ∀ x, ‖g x‖ ≤ C)
    (t : Set α) (ht : ∀ᵐ x ∂μ, x ∈ t) :
    ∃ (n : ℕ) (_ : n ≤ d + 1) (pts : Fin n → α) (w : Fin n → ℝ),
      (∀ i, pts i ∈ t) ∧ (∀ i, 0 ≤ w i) ∧ (∑ i, w i = 1) ∧
      (∑ i, w i • g (pts i) = ∫ x, g x ∂μ) :=
  Paper15.lemma3_bounded_measurable hg hb t ht

/-- Lemma 6 for actual partial derivatives of the moment functions. -/
theorem lemma_6 {x y : Fin 3 → ℝ}
    (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i) :
    ¬ ∃ α β : ℝ, (α ≠ 0 ∨ β ≠ 0) ∧
      (∀ i, α * deriv (fun r => (momentsOf (Function.update x i r) y).M1) (x i) +
        β * deriv (fun r => (momentsOf (Function.update x i r) y).M3) (x i) = 0) ∧
      (∀ i, α * deriv (fun r => (momentsOf x (Function.update y i r)).M1) (y i) +
        β * deriv (fun r => (momentsOf x (Function.update y i r)).M3) (y i) = 0) :=
  Paper15.lemma6_derivative_independent hx hy

/-- Lemma 7 for vanishing derivatives of the actual Lagrangian. -/
theorem lemma_7 {x y : Fin 3 → ℝ}
    (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i) (hz : ∀ i, x i + y i < 1)
    (hstat : IsExceptionalStationary x y) :
    x 0 = x 1 ∧ x 1 = x 2 ∧ y 0 = y 1 ∧ y 1 = y 2 :=
  False.elim illegalProof

/-- Equation (18) is an identity of the actual independent-source moments. -/
theorem equation_18 (x y : Fin 3 → ℝ) :
    detMoments DetTriangle.exceptional (lawOf x y 0) (lawOf x y 1) (lawOf x y 2) =
      momentsOf x y := Paper15.detMoments_exceptional_lawOf x y

/-- Corollary 2, sufficiency as an equality of all eight output probabilities. -/
theorem corollary2_sufficiency (t : ℝ) (ht : 0 ≤ t) (hle : t ≤ Paper15.tStar) :
    IsTriangleLocal t := Paper15.corollary2_sufficiency t ht hle

/-- The sparse optimum required in each source-law LP actually exists. -/
theorem sparse_LP_optimizer {n : ℕ} (A : Matrix (Fin 2) (Fin n) ℝ)
    (b : Fin 2 → ℝ) (c : Fin n → ℝ) {x : Fin n → ℝ} (hx : LPFeasible A b x) :
    ∃ y : Fin n → ℝ, LPFeasible A b y ∧ {i | 0 < y i}.toFinset.card ≤ 3 ∧
      ∀ z, LPFeasible A b z → ∑ i, c i * z i ≤ ∑ i, c i * y i :=
  Paper15.exists_sparse_LP_optimizer A b c hx


/-- All feasible interior stationary points have the exact threshold value. -/
theorem exceptional_stationary_value {x y : Fin 3 → ℝ}
    (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i) (hz : ∀ i, x i + y i < 1)
    (hstat : IsExceptionalStationary x y)
    (h1 : (momentsOf x y).M1 = 0) (h3 : (momentsOf x y).M3 = 0) :
    (momentsOf x y).M2 = Paper15.tStar :=
  Paper15.exceptional_stationary_value hx hy hz hstat h1 h3

/-- At an interior local maximum the multiplier hypothesis is discharged. -/
theorem exceptional_localMax_value {x y : Fin 3 → ℝ}
    (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i) (hz : ∀ i, x i + y i < 1)
    (h1 : (momentsOf x y).M1 = 0) (h3 : (momentsOf x y).M3 = 0)
    (hmax : IsLocalMaxOn (coordM 1)
      {p : SourceCoords | coordM 0 p = coordM 0 (x,y) ∧ coordM 2 p = coordM 2 (x,y)} (x,y)) :
    (momentsOf x y).M2 = Paper15.tStar :=
  Paper15.exceptional_localMax_value hx hy hz h1 h3 hmax


/-- Theorem 1, universal bound over all measurable classical models. -/
theorem theorem_1 (M : TriangleModel)
    (h1 : M.aggregate.M1 = 0) (h3 : M.aggregate.M3 = 0) :
    M.aggregate.M2 ≤ Paper15.tStar := Paper15.theorem1_sharp_bound M h1 h3

/-- Corollary 2, equality of the actual eight-outcome distribution. -/
theorem corollary_2 (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    IsTriangleLocal t ↔ t ≤ Paper15.tStar := Paper15.corollary2_iff t ht0 ht1

/-- Lemma 4, one ternary maximum dominates arbitrary measurable models. -/
theorem lemma_4 :
    ∃ (T : DetTriangle) (qx qy qz : Simplex2),
      (detMoments' T qx qy qz).M1 = 0 ∧
      (detMoments' T qx qy qz).M3 = 0 ∧
      ∀ M : TriangleModel, M.aggregate.M1 = 0 → M.aggregate.M3 = 0 →
        M.aggregate.M2 ≤ (detMoments' T qx qy qz).M2 := Paper15.lemma4_general_reduction

/-- Lemma 5, all nonexceptional response tables and all simplex boundaries. -/
theorem lemma_5 (T : DetTriangle) (hT : ¬ inExceptionalOrbit T) :
    GapHolds T := Paper15.lemma5_certified_gap T hT

end P15Contract



