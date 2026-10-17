import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Spectrum
import Mathlib.Topology.Compactness.Compact

/-!
# Classical–quantum channels, density operators, and effects

Finite classical–quantum (cq) channels with output operators on `Matrix (Fin d) (Fin d) ℂ`.
We use the positive-semidefinite order on matrices (`MatrixOrder`).
-/

open scoped MatrixOrder ComplexOrder
open Matrix

noncomputable section

namespace Paper22

/-- An operator `T` on `ℂ^n` is an **effect** when `0 ≤ T ≤ I` in the PSD order. -/
def IsEffect {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  0 ≤ T ∧ T ≤ 1

/-- In the PSD matrix order, `0 ≤ I`. -/
theorem zero_le_one_matrix (n : ℕ) : (0 : Matrix (Fin n) (Fin n) ℂ) ≤ 1 := by
  refine le_iff.mpr ?_
  simpa using (PosSemidef.one (n := Fin n) (R := ℂ))

namespace IsEffect

theorem nonneg {n : ℕ} {T : Matrix (Fin n) (Fin n) ℂ} (h : IsEffect T) : 0 ≤ T := h.1

theorem le_one {n : ℕ} {T : Matrix (Fin n) (Fin n) ℂ} (h : IsEffect T) : T ≤ 1 := h.2

theorem posSemidef {n : ℕ} {T : Matrix (Fin n) (Fin n) ℂ} (h : IsEffect T) : T.PosSemidef :=
  h.1.posSemidef

theorem isHermitian {n : ℕ} {T : Matrix (Fin n) (Fin n) ℂ} (h : IsEffect T) : T.IsHermitian :=
  h.posSemidef.isHermitian

theorem zero {n : ℕ} : IsEffect (0 : Matrix (Fin n) (Fin n) ℂ) :=
  ⟨le_refl 0, zero_le_one_matrix n⟩

theorem one {n : ℕ} : IsEffect (1 : Matrix (Fin n) (Fin n) ℂ) :=
  ⟨zero_le_one_matrix n, le_refl 1⟩

theorem one_sub_nonneg {n : ℕ} {T : Matrix (Fin n) (Fin n) ℂ} (h : IsEffect T) :
    0 ≤ 1 - T :=
  nonneg_iff_posSemidef.mpr (le_iff.mp h.le_one)

theorem one_sub_posSemidef {n : ℕ} {T : Matrix (Fin n) (Fin n) ℂ} (h : IsEffect T) :
    (1 - T).PosSemidef :=
  h.one_sub_nonneg.posSemidef

end IsEffect

/-- A **density operator** on `ℂ^n`: positive semidefinite of trace one. -/
structure IsDensity {n : ℕ} (ρ : Matrix (Fin n) (Fin n) ℂ) : Prop where
  posSemidef : ρ.PosSemidef
  trace_one : ρ.trace = 1

namespace IsDensity

theorem isHermitian {n : ℕ} {ρ : Matrix (Fin n) (Fin n) ℂ} (h : IsDensity ρ) : ρ.IsHermitian :=
  h.posSemidef.isHermitian

theorem nonneg {n : ℕ} {ρ : Matrix (Fin n) (Fin n) ℂ} (h : IsDensity ρ) : 0 ≤ ρ :=
  h.posSemidef.nonneg

theorem trace_nonneg {n : ℕ} {ρ : Matrix (Fin n) (Fin n) ℂ} (h : IsDensity ρ) :
    0 ≤ ρ.trace :=
  h.posSemidef.trace_nonneg

end IsDensity

/-- A finite **classical–quantum channel** `x ↦ ωₓ` with input alphabet `Fin n`
and output dimension `d`. -/
structure CQChannel (n d : ℕ) where
  states : Fin n → Matrix (Fin d) (Fin d) ℂ
  isDensity : ∀ x, IsDensity (states x)

namespace CQChannel

variable {n d : ℕ} (V : CQChannel n d)

/-- Evaluate the channel on an input letter. -/
def apply (x : Fin n) : Matrix (Fin d) (Fin d) ℂ := V.states x

@[simp]
theorem apply_eq (x : Fin n) : V.apply x = V.states x := rfl

theorem density (x : Fin n) : IsDensity (V.apply x) := V.isDensity x

theorem posSemidef (x : Fin n) : (V.apply x).PosSemidef := (V.density x).posSemidef

theorem trace_one (x : Fin n) : (V.apply x).trace = 1 := (V.density x).trace_one

theorem nonneg (x : Fin n) : 0 ≤ V.apply x := (V.density x).nonneg

/-- The channel has **full-rank outputs** when every output state is positive definite. -/
def FullRank : Prop := ∀ x, (V.apply x).PosDef

end CQChannel

/-- Probability distributions on `Fin n`. -/
structure ProbDist (n : ℕ) where
  q : Fin n → ℝ
  nonneg : ∀ i, 0 ≤ q i
  sum_eq_one : ∑ i, q i = 1

namespace ProbDist

variable {n : ℕ}

theorem q_nonneg (p : ProbDist n) (i : Fin n) : 0 ≤ p.q i := p.nonneg i

theorem sum_q (p : ProbDist n) : ∑ i, p.q i = 1 := p.sum_eq_one

/-- Uniform distribution on `Fin n` for `n > 0`. -/
def uniform (n : ℕ) (_hn : 0 < n) : ProbDist n where
  q := fun _ => 1 / (n : ℝ)
  nonneg := fun _ => by positivity
  sum_eq_one := by
    have hn0 : (n : ℝ) ≠ 0 := by positivity
    calc ∑ _i : Fin n, (1 / (n : ℝ))
      _ = (n : ℝ) * (1 / (n : ℝ)) := by rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
      _ = 1 := by field_simp [hn0]

end ProbDist

/-- The **objective** of the cq coding programs:
`∑ₓ qₓ · Re Tr(ωₓ (I - Tₓ))`. -/
def programObjective {n d : ℕ} (ω : Fin n → Matrix (Fin d) (Fin d) ℂ)
    (q : Fin n → ℝ) (T : Fin n → Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  ∑ x, q x * (ω x * (1 - T x)).trace.re

end Paper22

end
