import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Real.Basic

/-! Precisely disclosed classical Cauchy--Binet determinant identity. It is
a universal rectangular matrix identity; it contains no tangent, current,
polyhedron, mass bound or paper-owned estimate. -/
set_option autoImplicit false
noncomputable section
namespace Paper28

abbrev PluckerIndex (d k : ℕ) := {s : Finset (Fin d) // s.card = k}

def orderedMinorIndices {d k : ℕ} (s : PluckerIndex d k) : Fin k → Fin d :=
  s.val.orderEmbOfFin s.property

def CauchyBinetInput : Prop :=
  ∀ d k : ℕ, ∀ (M : Matrix (Fin k) (Fin d) ℝ) (N : Matrix (Fin d) (Fin k) ℝ),
    (M*N).det = ∑ s : PluckerIndex d k,
      (M.submatrix id (orderedMinorIndices s)).det * (N.submatrix (orderedMinorIndices s) id).det

end Paper28
