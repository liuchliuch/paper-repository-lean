import Paper25.FullspaceFilter
import Paper25.CircuitRecipe

/-! Precisely scoped inputs for published results whose formalizations are not
available in this project. This file declares no axiom and supplies no proof
of existence of these inputs. Every relative theorem retains its input. -/
noncomputable section
namespace Paper25

/-- Axler, Linear Algebra Done Right, fourth edition, Theorem 7.55 (printed
page 262): every finite-dimensional complex unitary operator admits an
orthonormal eigenbasis with eigenvalues on the unit circle. Only that theorem
is represented here; it contains no circuit, approximation or resource claim. -/
structure UnitarySpectralTheorem : Prop where
  eigenbasis : ∀ (n : Type) [Fintype n] [DecidableEq n] (U : Matrix n n ℂ),
    U ∈ Matrix.unitaryGroup n ℂ → Nonempty (UnitaryEigenbasis U)

end Paper25
