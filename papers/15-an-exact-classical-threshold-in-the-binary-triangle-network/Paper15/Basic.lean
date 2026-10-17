import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Data.Real.Sqrt
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.ProbabilityMassFunction.Basic

/-!
# Core definitions for the binary triangle network threshold

Paper: *An exact classical threshold in the binary triangle network*.

This module defines binary outputs, aggregate moments `M1, M2, M3`, the family
`p_t`, the exceptional response table `F`, the threshold polynomial, and the
finite ternary model used throughout the formalization.
-/

noncomputable section

namespace Paper15

open Finset Real Polynomial BigOperators

/-- Binary outputs are realized as real signs. -/
abbrev Sign := ℝ

/-- The two legal output values. -/
def legalSign (a : Sign) : Prop := a = 1 ∨ a = -1

lemma legalSign.one : legalSign (1 : ℝ) := Or.inl rfl
lemma legalSign.neg_one : legalSign (-1 : ℝ) := Or.inr rfl

@[simp] lemma legalSign_sq {a : Sign} (h : legalSign a) : a ^ 2 = 1 := by
  rcases h with rfl | rfl <;> simp

lemma legalSign_mul {a b : Sign} (ha : legalSign a) (hb : legalSign b) :
    legalSign (a * b) := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp [legalSign]

/-- Aggregate moments of equations (3). -/
structure AggregateMoments where
  /-- `M1 = (E[A] + E[B] + E[C]) / 3` -/
  M1 : ℝ
  /-- `M2 = (E[AB] + E[BC] + E[CA]) / 3` -/
  M2 : ℝ
  /-- `M3 = E[ABC]` -/
  M3 : ℝ

/-- The one-parameter family (2):
`p_t(a,b,c) = (1 + t(ab+bc+ca)) / 8` for `a,b,c ∈ {-1,1}`. -/
def p_t (t : ℝ) (a b c : Sign) : ℝ :=
  (1 + t * (a * b + b * c + c * a)) / 8

/-- Threshold polynomial (5): `3t^4 + 28t^3 + 66t^2 - 36t + 3`. -/
def thresholdPoly (t : ℝ) : ℝ :=
  3 * t ^ 4 + 28 * t ^ 3 + 66 * t ^ 2 - 36 * t + 3

/-- The threshold polynomial as an element of `ℝ[X]`. -/
def thresholdPolyX : ℝ[X] :=
  3 * X ^ 4 + 28 * X ^ 3 + 66 * X ^ 2 - 36 * X + 3

lemma thresholdPoly_eq_eval (t : ℝ) :
    thresholdPoly t = thresholdPolyX.eval t := by
  simp [thresholdPoly, thresholdPolyX]

/-- Numerical bound used throughout: `9/25`. -/
def nineTwentyFifths : ℝ := (9 : ℝ) / 25

lemma nineTwentyFifths_pos : 0 < nineTwentyFifths := by
  norm_num [nineTwentyFifths]

lemma nineTwentyFifths_lt_one : nineTwentyFifths < 1 := by
  norm_num [nineTwentyFifths]

/-! ## Ternary source laws (the simplex `Δ₂`) -/

/-- Probability vectors on three source values. -/
structure Simplex2 where
  v : Fin 3 → ℝ
  nonneg : ∀ i, 0 ≤ v i
  sum_eq : ∑ i, v i = 1

namespace Simplex2

instance : CoeFun Simplex2 (fun _ => Fin 3 → ℝ) := ⟨fun s => s.v⟩

@[simp] lemma coe_apply (s : Simplex2) (i : Fin 3) : s i = s.v i := rfl

lemma apply_nonneg (s : Simplex2) (i : Fin 3) : 0 ≤ s i := s.nonneg i

lemma sum_apply (s : Simplex2) : ∑ i, s i = 1 := s.sum_eq

/-- The uniform law on three values. -/
def uniform : Simplex2 where
  v _ := 1 / 3
  nonneg _ := by norm_num
  sum_eq := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    norm_num

/-- A Dirac law on source value `i`. -/
def dirac (i : Fin 3) : Simplex2 where
  v j := if j = i then 1 else 0
  nonneg j := by by_cases h : j = i <;> simp [h]
  sum_eq := by simp

end Simplex2

/-! ## Deterministic response tables -/

/-- A single party's deterministic response: output sign as a function of the
two incident source values. -/
structure RespTable where
  f : Fin 3 → Fin 3 → Sign
  legal : ∀ j k, legalSign (f j k)

namespace RespTable

instance : CoeFun RespTable (fun _ => Fin 3 → Fin 3 → Sign) := ⟨fun T => T.f⟩

@[simp] lemma coe_apply (T : RespTable) (j k : Fin 3) : T j k = T.f j k := rfl

lemma sq (T : RespTable) (j k : Fin 3) : (T j k) ^ 2 = 1 :=
  legalSign_sq (T.legal j k)

lemma mul_self (T : RespTable) (j k : Fin 3) : T j k * T j k = 1 := by
  rw [← pow_two]; exact T.sq j k

/-- Global sign flip of a table. -/
def flip (T : RespTable) : RespTable where
  f j k := - T j k
  legal j k := by
    rcases T.legal j k with h | h
    · rw [h]; exact legalSign.neg_one
    · rw [h]; simp; exact legalSign.one

lemma legal_eq (T : RespTable) (j k : Fin 3) : T j k = 1 ∨ T j k = -1 :=
  T.legal j k

end RespTable

/-- A fully deterministic ternary triangle response assignment
`A = A(y,z)`, `B = B(z,x)`, `C = C(x,y)`, matching (6). -/
structure DetTriangle where
  A : RespTable
  B : RespTable
  C : RespTable

namespace DetTriangle

/-- The exceptional attaining table `F` of (6), applied to every party:
`F(j,k) = +1` iff `(j,k) ∈ {(0,1),(1,0),(1,1)}`. -/
def exceptionalTable : RespTable where
  f j k := if (j = 0 ∧ k = 1) ∨ (j = 1 ∧ k = 0) ∨ (j = 1 ∧ k = 1) then 1 else (-1 : ℝ)
  legal j k := by
    by_cases h : (j = 0 ∧ k = 1) ∨ (j = 1 ∧ k = 0) ∨ (j = 1 ∧ k = 1)
    · rw [if_pos h]; exact legalSign.one
    · rw [if_neg h]; exact legalSign.neg_one

/-- The exceptional model uses `F` for all three parties. -/
def exceptional : DetTriangle := ⟨exceptionalTable, exceptionalTable, exceptionalTable⟩

@[simp] lemma exceptional_A : exceptional.A = exceptionalTable := rfl
@[simp] lemma exceptional_B : exceptional.B = exceptionalTable := rfl
@[simp] lemma exceptional_C : exceptional.C = exceptionalTable := rfl

/-- Explicit values of `F` on the nine pairs. -/
lemma exceptionalTable_val (j k : Fin 3) :
    exceptionalTable j k =
      if (j = 0 ∧ k = 1) ∨ (j = 1 ∧ k = 0) ∨ (j = 1 ∧ k = 1) then (1 : ℝ) else -1 := rfl

end DetTriangle

/-! ## Aggregate moments of a finite ternary model -/

/-- Moments of a deterministic ternary triangle with source laws `qx qy qz`.
Expectations are over independent source values in `Fin 3`. -/
def detMoments (T : DetTriangle) (qx qy qz : Fin 3 → ℝ) : AggregateMoments :=
  let eA := ∑ x, ∑ y, ∑ z, qx x * qy y * qz z * T.A y z
  let eB := ∑ x, ∑ y, ∑ z, qx x * qy y * qz z * T.B z x
  let eC := ∑ x, ∑ y, ∑ z, qx x * qy y * qz z * T.C x y
  let eAB := ∑ x, ∑ y, ∑ z, qx x * qy y * qz z * (T.A y z * T.B z x)
  let eBC := ∑ x, ∑ y, ∑ z, qx x * qy y * qz z * (T.B z x * T.C x y)
  let eCA := ∑ x, ∑ y, ∑ z, qx x * qy y * qz z * (T.C x y * T.A y z)
  let eABC := ∑ x, ∑ y, ∑ z, qx x * qy y * qz z * (T.A y z * T.B z x * T.C x y)
  { M1 := (eA + eB + eC) / 3
    M2 := (eAB + eBC + eCA) / 3
    M3 := eABC }

/-- Moments for source laws given as `Simplex2`. -/
def detMoments' (T : DetTriangle) (qx qy qz : Simplex2) : AggregateMoments :=
  detMoments T (fun i => qx i) (fun i => qy i) (fun i => qz i)

/-! ## Moment expansions for the exceptional table (equations 10–12)

For i.i.d. laws `(x,y,z)` on the three values.
-/

/-- `M1` for the exceptional model with i.i.d. law, equation (10). -/
def exceptionalM1 (x y : ℝ) : ℝ := -1 + 4 * x * y + 2 * y ^ 2

/-- `M2` for the exceptional model with i.i.d. law, equation (10). -/
def exceptionalM2 (x y : ℝ) : ℝ :=
  1 - 8 * x * y + 4 * x ^ 2 * y - 4 * y ^ 2 + 12 * x * y ^ 2 + 4 * y ^ 3

/-- `M3` for the exceptional model with i.i.d. law, equation (10). -/
def exceptionalM3 (x y : ℝ) : ℝ :=
  -1 + 12 * x * y - 12 * x ^ 2 * y + 6 * y ^ 2 - 12 * x * y ^ 2 - 4 * y ^ 3

/-- After substituting `x = (1-2y²)/(4y)` and `z = 1-x-y`, equation (11):
`M2 = 1/(4y) - 1 + 2y - y³`. -/
def exceptionalM2Sub (y : ℝ) : ℝ := 1 / (4 * y) - 1 + 2 * y - y ^ 3

/-- Equation (12): under (7), `M2 = 1/y + 2y - 3`. -/
def exceptionalM2Final (y : ℝ) : ℝ := 1 / y + 2 * y - 3

/-! ## Section 4 coordinates for possibly different source laws -/

/-- `u_i = x_i + y_i`. -/
def uOf (x y : Fin 3 → ℝ) (i : Fin 3) : ℝ := x i + y i

/-- `E` of (17): `∑_{i<j} (u_i u_j - x_i x_j)`. -/
def eQty (x y : Fin 3 → ℝ) : ℝ :=
  (uOf x y 0 * uOf x y 1 - x 0 * x 1) +
  (uOf x y 0 * uOf x y 2 - x 0 * x 2) +
  (uOf x y 1 * uOf x y 2 - x 1 * x 2)

/-- `T` of (17): `y1 y2 y3 + ∑_i x_i y_j y_k`. -/
def tQty (x y : Fin 3 → ℝ) : ℝ :=
  y 0 * y 1 * y 2 + x 0 * y 1 * y 2 + x 1 * y 0 * y 2 + x 2 * y 0 * y 1

/-- `S` of (17): `∑_i y_i x_j x_k`. -/
def sQty (x y : Fin 3 → ℝ) : ℝ :=
  y 0 * x 1 * x 2 + y 1 * x 0 * x 2 + y 2 * x 0 * x 1

/-- `V = T + S` of (17). -/
def vQty (x y : Fin 3 → ℝ) : ℝ := tQty x y + sQty x y

/-! ## Classical triangle-local distributions

A classical triangle model with arbitrary source spaces.  Response kernels give
`P(A = 1 | y,z) ∈ [0,1]`.  Aggregate moments are the expectations of (3).
-/

/-- A classical triangle model with binary outputs. -/
structure TriangleModel where
  /-- Source spaces with measurable structure. -/
  X : Type
  Y : Type
  Z : Type
  mX : MeasurableSpace X
  mY : MeasurableSpace Y
  mZ : MeasurableSpace Z
  /-- Independent probability laws of the three sources. -/
  μX : @MeasureTheory.Measure X mX
  μY : @MeasureTheory.Measure Y mY
  μZ : @MeasureTheory.Measure Z mZ
  isProbX : @MeasureTheory.IsProbabilityMeasure X mX μX
  isProbY : @MeasureTheory.IsProbabilityMeasure Y mY μY
  isProbZ : @MeasureTheory.IsProbabilityMeasure Z mZ μZ
  /-- Response probabilities `P(A = 1 | y,z)`. -/
  pA : Y → Z → ℝ
  pB : Z → X → ℝ
  pC : X → Y → ℝ
  pA_mem : ∀ y z, pA y z ∈ Set.Icc (0:ℝ) 1
  pB_mem : ∀ z x, pB z x ∈ Set.Icc (0:ℝ) 1
  pC_mem : ∀ x y, pC x y ∈ Set.Icc (0:ℝ) 1
  /-- Joint measurability of each response kernel, as in equation (1). -/
  pA_measurable : letI := mY; letI := mZ; Measurable (Function.uncurry pA)
  pB_measurable : letI := mZ; letI := mX; Measurable (Function.uncurry pB)
  pC_measurable : letI := mX; letI := mY; Measurable (Function.uncurry pC)

namespace TriangleModel

variable (M : TriangleModel)

/-- Conditional mean of party A given `(y,z)`: `E[A|y,z] = 2 pA - 1`. -/
def condA (y : M.Y) (z : M.Z) : ℝ := 2 * M.pA y z - 1
/-- Conditional mean of party B given `(z,x)`. -/
def condB (z : M.Z) (x : M.X) : ℝ := 2 * M.pB z x - 1
/-- Conditional mean of party C given `(x,y)`. -/
def condC (x : M.X) (y : M.Y) : ℝ := 2 * M.pC x y - 1

/-- One-body moment `E[A]`. -/
def eA : ℝ := ∫ y, ∫ z, M.condA y z ∂M.μZ ∂M.μY
/-- One-body moment `E[B]`. -/
def eB : ℝ := ∫ z, ∫ x, M.condB z x ∂M.μX ∂M.μZ
/-- One-body moment `E[C]`. -/
def eC : ℝ := ∫ x, ∫ y, M.condC x y ∂M.μY ∂M.μX

/-- Pair moment `E[AB]`. -/
def eAB : ℝ := ∫ x, ∫ y, ∫ z, M.condA y z * M.condB z x ∂M.μZ ∂M.μY ∂M.μX
/-- Pair moment `E[BC]`. -/
def eBC : ℝ := ∫ x, ∫ y, ∫ z, M.condB z x * M.condC x y ∂M.μZ ∂M.μY ∂M.μX
/-- Pair moment `E[CA]`. -/
def eCA : ℝ := ∫ x, ∫ y, ∫ z, M.condC x y * M.condA y z ∂M.μZ ∂M.μY ∂M.μX

/-- Three-body moment `E[ABC]`. -/
def eABC : ℝ := ∫ x, ∫ y, ∫ z,
    M.condA y z * M.condB z x * M.condC x y ∂M.μZ ∂M.μY ∂M.μX

/-- Aggregate moments (3). -/
def aggregate : AggregateMoments where
  M1 := (M.eA + M.eB + M.eC) / 3
  M2 := (M.eAB + M.eBC + M.eCA) / 3
  M3 := M.eABC

/-- The condition `M1 = M3 = 0` of Theorem 1. -/
def vanishing : Prop := M.aggregate.M1 = 0 ∧ M.aggregate.M3 = 0

end TriangleModel

/-- Output mass of equation (1), using the binary Fourier form of each
response kernel. Only legal signs are used in locality statements. -/
def TriangleModel.output (M : TriangleModel) (a b c : Sign) : ℝ :=
  ∫ x, ∫ y, ∫ z,
    ((1 + a * M.condA y z) / 2) *
    ((1 + b * M.condB z x) / 2) *
    ((1 + c * M.condC x y) / 2) ∂M.μZ ∂M.μY ∂M.μX

/-- Aggregate realizability, a weaker property than equality to `p_t`. -/
def IsAggregateRealizable (t : ℝ) : Prop :=
  ∃ M : TriangleModel, M.aggregate.M1 = 0 ∧ M.aggregate.M2 = t ∧ M.aggregate.M3 = 0

/-- Exact triangle locality of the distribution (2), for all eight outcomes. -/
def IsTriangleLocalAt (t : ℝ) : Prop :=
  ∃ M : TriangleModel, ∀ a b c, legalSign a → legalSign b → legalSign c →
    M.output a b c = p_t t a b c

/-- Finite deterministic witness: a ternary response table with source laws on
`Fin 3` producing moments `(0, t, 0)`. Finite models are classical triangle
models (Lemma 4), and this form is used for explicit constructions. -/
def IsFinTriangleLocal (t : ℝ) : Prop :=
  ∃ (T : DetTriangle) (qx qy qz : Simplex2),
    (detMoments' T qx qy qz).M1 = 0 ∧
    (detMoments' T qx qy qz).M2 = t ∧
    (detMoments' T qx qy qz).M3 = 0

/-- Triangle-locality of `p_t`. -/
def IsTriangleLocal (t : ℝ) : Prop := IsTriangleLocalAt t

end Paper15
