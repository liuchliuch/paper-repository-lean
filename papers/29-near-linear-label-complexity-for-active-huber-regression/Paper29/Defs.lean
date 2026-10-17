import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Matrix.Mul

/-! Definitions for P29, with the width-one normalization of equation (2.1). -/
noncomputable section
open scoped BigOperators

namespace Paper29

def huber (t : ℝ) : ℝ := if |t| ≤ 1 then t ^ 2 / 2 else |t| - 1 / 2

def psi (t : ℝ) : ℝ := Real.sqrt (huber t)

def huberWidth (s t : ℝ) : ℝ := s * huber (t / s)

def objective {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (b : Fin n → ℝ) (x : Fin d → ℝ) : ℝ :=
  ∑ i, huber ((A.mulVec x) i - b i)

def unshifted {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (x : Fin d → ℝ) : ℝ := ∑ i, huber ((A.mulVec x) i)

def weightedHuber {ι : Type*} [Fintype ι] (w y : ι → ℝ) : ℝ :=
  ∑ i, w i * huber (y i)

def majorityObjective (N γ t : ℝ) : ℝ :=
  N * (1 / 2 - γ) * huber (4 * t) +
    N * (1 / 2 + γ) * huber (4 * (t - 1))

def majorityRatio (γ : ℝ) : ℝ := (1 / 2 - γ) / (1 / 2 + γ)

def majorityMinimizer (γ : ℝ) : ℝ := 1 - majorityRatio γ / 4

end Paper29
