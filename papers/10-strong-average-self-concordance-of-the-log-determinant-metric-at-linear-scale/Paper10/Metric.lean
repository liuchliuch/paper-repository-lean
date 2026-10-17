import Paper10.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The log-determinant barrier and its Hessian metric

For `X > 0`:
* `phi(X) = -log det X`
* `G_X[U,V] = Tr(X^{-1} U X^{-1} V)`
* `g_s(X)[U,V] = s * G_X[U,V]`
-/

noncomputable section

open Matrix

namespace Paper10

variable {q : ℕ}

/-- Log-determinant barrier `phi(X) = -log det X`. -/
def phi (X : Matrix (Fin q) (Fin q) ℝ) : ℝ := -Real.log X.det

/-- The log-determinant Hessian metric `G_X[U,V] = Tr(X^{-1} U X^{-1} V)`. -/
def G (X : Matrix (Fin q) (Fin q) ℝ) (U V : Matrix (Fin q) (Fin q) ℝ) : ℝ :=
  Matrix.trace (X⁻¹ * U * X⁻¹ * V)

/-- The scaled metric `g_s(X)[U,V] = s * G_X[U,V]`. -/
def g (s : ℝ) (X : Matrix (Fin q) (Fin q) ℝ) (U V : Matrix (Fin q) (Fin q) ℝ) : ℝ :=
  s * G X U V

/-- Squared local norm. -/
def localNormSq (s : ℝ) (X H : Matrix (Fin q) (Fin q) ℝ) : ℝ :=
  g s X H H

theorem localNormSq_eq (s : ℝ) (X H : Matrix (Fin q) (Fin q) ℝ) :
    localNormSq s X H = s * Matrix.trace (X⁻¹ * H * X⁻¹ * H) :=
  rfl

theorem G_self_eq (X H : Matrix (Fin q) (Fin q) ℝ) :
    G X H H = Matrix.trace (X⁻¹ * H * X⁻¹ * H) :=
  rfl

theorem g_self_eq (s : ℝ) (X H : Matrix (Fin q) (Fin q) ℝ) :
    g s X H H = s * Matrix.trace (X⁻¹ * H * X⁻¹ * H) :=
  rfl

/-- Congruence operator in inverse form. -/
def congruence (X H : Matrix (Fin q) (Fin q) ℝ) : Matrix (Fin q) (Fin q) ℝ :=
  X⁻¹ * H * X⁻¹

/-- `G_X` is additive in the first slot. -/
theorem G_add (X U₁ U₂ V : Matrix (Fin q) (Fin q) ℝ) :
    G X (U₁ + U₂) V = G X U₁ V + G X U₂ V := by
  unfold G
  have h : X⁻¹ * (U₁ + U₂) * X⁻¹ * V
      = X⁻¹ * U₁ * X⁻¹ * V + X⁻¹ * U₂ * X⁻¹ * V := by
    simp only [Matrix.mul_add, Matrix.add_mul]
  rw [h, Matrix.trace_add]

/-- `G_X` is homogeneous in the first slot. -/
theorem G_smul (X U V : Matrix (Fin q) (Fin q) ℝ) (a : ℝ) :
    G X (a • U) V = a * G X U V := by
  unfold G
  have h : X⁻¹ * (a • U) * X⁻¹ * V = a • (X⁻¹ * U * X⁻¹ * V) := by
    simp only [Matrix.mul_smul, Matrix.smul_mul]
  rw [h, Matrix.trace_smul, smul_eq_mul]

/-- `G_X` is additive in the second slot. -/
theorem G_add_right (X U V₁ V₂ : Matrix (Fin q) (Fin q) ℝ) :
    G X U (V₁ + V₂) = G X U V₁ + G X U V₂ := by
  unfold G
  have h : X⁻¹ * U * X⁻¹ * (V₁ + V₂)
      = X⁻¹ * U * X⁻¹ * V₁ + X⁻¹ * U * X⁻¹ * V₂ := by
    simp only [Matrix.mul_add]
  rw [h, Matrix.trace_add]

/-- `G_X` is homogeneous in the second slot. -/
theorem G_smul_right (X U V : Matrix (Fin q) (Fin q) ℝ) (a : ℝ) :
    G X U (a • V) = a * G X U V := by
  unfold G
  have h : X⁻¹ * U * X⁻¹ * (a • V) = a • (X⁻¹ * U * X⁻¹ * V) := by
    simp only [Matrix.mul_smul]
  rw [h, Matrix.trace_smul, smul_eq_mul]

/-- Helper: `X.PosDef` implies `X.IsSymm` for real matrices. -/
theorem posDef_isSymm {X : Matrix (Fin q) (Fin q) ℝ} (hX : X.PosDef) :
    X.IsSymm :=
  hX.1

/-- Helper: inverse of a positive-definite matrix is symmetric. -/
theorem inv_isSymm {X : Matrix (Fin q) (Fin q) ℝ} (hX : X.PosDef) :
    (X⁻¹).IsSymm := by
  have h1 : (X⁻¹)ᵀ = (Xᵀ)⁻¹ := Matrix.transpose_nonsing_inv X
  have h2 : Xᵀ = X := hX.1
  rw [h2] at h1
  exact h1

/-- `G_X` is symmetric: `Tr(X⁻¹ U X⁻¹ V) = Tr(X⁻¹ V X⁻¹ U)`.
This holds for all matrices `U, V` (no symmetry needed), by cyclicity of the trace. -/
theorem G_eq_swap (X U V : Matrix (Fin q) (Fin q) ℝ) :
    G X U V = G X V U := by
  unfold G
  have e1 : X⁻¹ * U * X⁻¹ * V = (X⁻¹ * U) * (X⁻¹ * V) :=
    Matrix.mul_assoc (X⁻¹ * U) X⁻¹ V
  have e2 : X⁻¹ * V * X⁻¹ * U = (X⁻¹ * V) * (X⁻¹ * U) :=
    Matrix.mul_assoc (X⁻¹ * V) X⁻¹ U
  rw [e1, e2]
  exact Matrix.trace_mul_comm _ _

/-- `G_X` is symmetric on symmetric matrices (paper form). -/
theorem G_symm (X U V : Matrix (Fin q) (Fin q) ℝ)
    (_hU : U.IsSymm) (_hV : V.IsSymm) (_hX : X.PosDef) :
    G X U V = G X V U :=
  G_eq_swap X U V

/-- Bilinearity of `G` as a pair of slots. -/
theorem G_add_add (X U₁ U₂ V₁ V₂ : Matrix (Fin q) (Fin q) ℝ) :
    G X (U₁ + U₂) (V₁ + V₂)
      = G X U₁ V₁ + G X U₁ V₂ + G X U₂ V₁ + G X U₂ V₂ := by
  rw [G_add, G_add_right, G_add_right]
  ring

theorem G_smul_smul (X U V : Matrix (Fin q) (Fin q) ℝ) (a b : ℝ) :
    G X (a • U) (b • V) = (a * b) * G X U V := by
  rw [G_smul, G_smul_right]
  ring

/-- The scaled metric `g` inherits additivity in the first slot. -/
theorem g_add (s : ℝ) (X U₁ U₂ V : Matrix (Fin q) (Fin q) ℝ) :
    g s X (U₁ + U₂) V = g s X U₁ V + g s X U₂ V := by
  unfold g
  rw [G_add]
  ring

/-- The scaled metric `g` inherits homogeneity in the first slot. -/
theorem g_smul (s : ℝ) (X U V : Matrix (Fin q) (Fin q) ℝ) (a : ℝ) :
    g s X (a • U) V = a * g s X U V := by
  unfold g
  rw [G_smul]
  ring

/-- The scaled metric `g` inherits symmetry. -/
theorem g_symm (s : ℝ) (X U V : Matrix (Fin q) (Fin q) ℝ) :
    g s X U V = g s X V U := by
  unfold g
  rw [G_eq_swap]

end Paper10
