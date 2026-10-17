import Paper28.NJacobian
import Mathlib.MeasureTheory.Measure.MeasureSpace

/-! Explicit external object/calculus interface for rectifiable currents on a
finite-dimensional Hilbert unit sphere. These are generic rectifiability,
Rademacher/locality and smooth-chain-rule facts, not paper-owned estimates.
The native AK current construction is an external input authorized by the
user; the interface contains no tree, free product, volume or joint mass bound.
No axiom or sorry is introduced. Actual semantic instantiation must be disclosed
with the published current theory, rather than being counted as a new proof.
-/
set_option autoImplicit false
noncomputable section
namespace Paper28
open MeasureTheory
universe u v

/-- Having a finite global Lipschitz constant. -/
def HasLipschitzConstant {X : Type*} {Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (f : X → Y) : Prop := ∃ K : NNReal, LipschitzWith K f

theorem clm_hasLipschitzConstant {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (P : X →L[ℝ] Y) :
    HasLipschitzConstant P := ⟨‖P‖₊, P.lipschitz⟩

/-- Disclosed external signature: k-currents on S(H), their mass measures,
approximate tangent planes and generic approximate-differential laws. The
opaque Current type is an input object, not a surrogate definition of AK
currents. Every law below is independent of the paper's folding construction. -/
structure RectifiableSphereCalculusInput (H : Type u) [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [FiniteDimensional ℝ H] [MeasurableSpace H] where
  Current : ℕ → Type v
  massMeasure : {n : ℕ} → Current n → Measure H
  plane : {n : ℕ} → Current n → H → Submodule ℝ H
  sphere_ae : ∀ {n} (C : Current n), ∀ᵐ x ∂massMeasure C, ‖x‖ = 1
  dimension_ae : ∀ {n} (C : Current n),
    ∀ᵐ x ∂massMeasure C, Module.finrank ℝ (plane C x) = n
  tangent_ae : ∀ {n} (C : Current n),
    ∀ᵐ x ∂massMeasure C, ∀ w : plane C x, inner ℝ x w.val = 0
  approxDifferential : ∀ {F : Type u} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F], (H → F) → {n : ℕ} → (C : Current n) →
      (x : H) → (plane C x → F)
  smooth_ae : ∀ {F : Type u} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] (f : H → F), HasLipschitzConstant f → ∀ {n} (C : Current n),
    ∀ᵐ x ∂massMeasure C, ∀ (D : H →L[ℝ] F), HasFDerivAt f D x →
      ∀ w : plane C x, approxDifferential f C x w = D w.val
  locality_ae : ∀ {F : Type u} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] (f g : H → F),
    HasLipschitzConstant f → HasLipschitzConstant g → ∀ {n} (C : Current n),
    ∀ᵐ x ∂massMeasure C, f x = g x → ∀ w : plane C x,
      approxDifferential f C x w = approxDifferential g C x w
  linearity_ae : ∀ {F : Type u} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] (f : H → F), HasLipschitzConstant f → ∀ {n} (C : Current n),
    ∀ᵐ x ∂massMeasure C, PreservesFrameSums (approxDifferential f C x)

section Generic
variable {H F : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [FiniteDimensional ℝ H] [MeasurableSpace H]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
variable (I : RectifiableSphereCalculusInput.{u,v} H)

/-- The original approximate tangent Jacobian, realized by the actual
Gram determinant of the externally provided approximate differential. -/
def currentJacobian (f : H → F) {n : ℕ} (C : I.Current n) (x : H) : ℝ :=
  frameJacobian (I.approxDifferential f C x)

/-- Generic tangent locality on a linear zero level set is derived from
smooth differentiation and locality, not postulated for the foldings. -/
theorem linear_kernel_tangent_ae (P : H →L[ℝ] F) {n : ℕ} (C : I.Current n) :
    ∀ᵐ x ∂I.massMeasure C, P x = 0 → ∀ w : I.plane C x, P w.val = 0 := by
  let Z : H →L[ℝ] F := 0
  filter_upwards [I.smooth_ae P (clm_hasLipschitzConstant P) C,
    I.smooth_ae Z (clm_hasLipschitzConstant Z) C,
    I.locality_ae P Z (clm_hasLipschitzConstant P) (clm_hasLipschitzConstant Z) C]
    with x hP hZ hLoc
  intro hx w
  have hEq : P x = Z x := by simpa [Z] using hx
  calc
    P w.val = I.approxDifferential P C x w := (hP P P.hasFDerivAt w).symm
    _ = I.approxDifferential Z C x w := hLoc hEq w
    _ = 0 := by simpa [Z] using hZ Z Z.hasFDerivAt w

/-- Piecewise smooth differentiation across one Lipschitz equality stratum.
Both branches are derived from the generic external calculus laws. -/
theorem approximate_differential_piecewise_ae
    (f : H → F) (hf : HasLipschitzConstant f) (g : H →L[ℝ] F)
    (D : H → H →L[ℝ] F) (regular : H → Prop)
    (hSmooth : ∀ x, regular x → HasFDerivAt f (D x) x)
    (hValue : ∀ x, ¬ regular x → f x = g x)
    (hDerivative : ∀ x, ¬ regular x → ∀ w, D x w = g w)
    {n : ℕ} (C : I.Current n) :
    ∀ᵐ x ∂I.massMeasure C, ∀ w : I.plane C x,
      I.approxDifferential f C x w = D x w.val := by
  classical
  filter_upwards [I.smooth_ae f hf C, I.smooth_ae g (clm_hasLipschitzConstant g) C,
    I.locality_ae f g hf (clm_hasLipschitzConstant g) C] with x hF hG hLoc
  intro w
  by_cases hx : regular x
  · exact hF (D x) (hSmooth x hx) w
  · rw [hDerivative x hx w.val]
    exact (hLoc (hValue x hx) w).trans (hG g g.hasFDerivAt w)

end Generic
end Paper28
