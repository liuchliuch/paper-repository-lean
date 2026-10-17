import Paper26.Normalization

/-!
# Reality of the original complex trace energies

These theorems identify the real-valued energy definitions with the full
complex trace expressions of the source. The Bures inverse image is proved
Hermitian from the defining Jordan equation and its uniqueness. This module
does not alter the frozen normalization proof.
-/
noncomputable section
open scoped ComplexOrder

namespace Paper26.EnergyReality

open Paper26.Normalization

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The trace of a product of Hermitian matrices is fixed by conjugation;
the matrices themselves need not commute. -/
theorem trace_hermitian_product_conj (X Y : Matrix ι ι ℂ)
    (hX : X.conjTranspose = X) (hY : Y.conjTranspose = Y) :
    star (Matrix.trace (X * Y)) = Matrix.trace (X * Y) := by
  rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hX, hY,
    Matrix.trace_mul_comm]

/-- Reality of the trace of a Hermitian product, expressed by zero imaginary
part without any commutativity assumption. -/
theorem trace_hermitian_product_im (X Y : Matrix ι ι ℂ)
    (hX : X.conjTranspose = X) (hY : Y.conjTranspose = Y) :
    (Matrix.trace (X * Y)).im = 0 := by
  apply Complex.conj_eq_iff_im.mp
  simpa only [Complex.star_def] using trace_hermitian_product_conj X Y hX hY

/-- Coercing the trace's real part back to complex recovers the entire trace. -/
theorem trace_hermitian_product_real (X Y : Matrix ι ι ℂ)
    (hX : X.conjTranspose = X) (hY : Y.conjTranspose = Y) :
    ((Matrix.trace (X * Y)).re : ℂ) = Matrix.trace (X * Y) := by
  apply Complex.conj_eq_iff_re.mp
  simpa only [Complex.star_def] using trace_hermitian_product_conj X Y hX hY

/-- The actual Jordan inverse preserves Hermitian matrices under A>0.
This follows from its unique defining equation, independently of any
particular eigenbasis or selected witness. -/
theorem jordanInverse_hermitian (A X : Matrix ι ι ℂ)
    (hA : A.PosDef) (hX : X.conjTranspose = X) :
    (jordanInverse A X).conjTranspose = jordanInverse A X := by
  apply jordanInverse_unique_posDef A X _ hA
  have h := congrArg Matrix.conjTranspose (jordanInverse_equation_posDef A X hA)
  simpa only [Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_smul, hA.1.eq, hX, star_ofNat, add_comm] using h

/-- The squared-error trace from the original Bures formula is real. -/
theorem bures_trace_im (ρ A : Matrix ι ι ℂ)
    (hρ : ρ.conjTranspose = ρ) (hA : A.PosDef) :
    (Matrix.trace ((ρ - A) * jordanInverse A (ρ - A))).im = 0 := by
  have hX : (ρ - A).conjTranspose = ρ - A := by
    rw [Matrix.conjTranspose_sub, hρ, hA.1.eq]
  exact trace_hermitian_product_im _ _ hX (jordanInverse_hermitian A _ hA hX)

/-- The squared-error trace using the actual right matrix inverse is real. -/
theorem right_trace_im (ρ A : Matrix ι ι ℂ)
    (hρ : ρ.conjTranspose = ρ) (hA : A.PosDef) :
    (Matrix.trace ((ρ - A) * (ρ - A) * A⁻¹)).im = 0 := by
  have hX : (ρ - A).conjTranspose = ρ - A := by
    rw [Matrix.conjTranspose_sub, hρ, hA.1.eq]
  have hXX : ((ρ - A) * (ρ - A)).conjTranspose = (ρ - A) * (ρ - A) := by
    rw [Matrix.conjTranspose_mul, hX]
  exact trace_hermitian_product_im _ _ hXX hA.1.inv.eq

/-- `standardBuresEnergy` represents the entire original trace, not only
an unrelated projection onto its real part. -/
theorem standardBuresEnergy_coe (ρ A : Matrix ι ι ℂ)
    (hρ : ρ.conjTranspose = ρ) (hA : A.PosDef) :
    (standardBuresEnergy ρ A : ℂ) =
      Matrix.trace ((ρ - A) * jordanInverse A (ρ - A)) := by
  have hX : (ρ - A).conjTranspose = ρ - A := by
    rw [Matrix.conjTranspose_sub, hρ, hA.1.eq]
  exact trace_hermitian_product_real _ _ hX (jordanInverse_hermitian A _ hA hX)

/-- `standardRightEnergy` represents the entire original trace, with the
actual inverse and all off-diagonal entries retained. -/
theorem standardRightEnergy_coe (ρ A : Matrix ι ι ℂ)
    (hρ : ρ.conjTranspose = ρ) (hA : A.PosDef) :
    (standardRightEnergy ρ A : ℂ) =
      Matrix.trace ((ρ - A) * (ρ - A) * A⁻¹) := by
  have hX : (ρ - A).conjTranspose = ρ - A := by
    rw [Matrix.conjTranspose_sub, hρ, hA.1.eq]
  have hXX : ((ρ - A) * (ρ - A)).conjTranspose = (ρ - A) * (ρ - A) := by
    rw [Matrix.conjTranspose_mul, hX]
  exact trace_hermitian_product_real _ _ hXX hA.1.inv.eq

end Paper26.EnergyReality
