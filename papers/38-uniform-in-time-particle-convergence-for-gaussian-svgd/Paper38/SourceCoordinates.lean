import Paper38.HilbertCoordinates
import Paper38.Specification

/-! Exact bridges between raw source coordinates and intrinsic symmetric Hilbert
coordinates. Positivity, minimizers and source distances retain their definitions. -/
noncomputable section
open scoped Matrix Matrix.Norms.Frobenius

namespace Paper38.SourceCoordinates
open Model HilbertCoordinates
variable {d : ℕ}

/-- Lift an actual positive-definite raw source state. -/
def lift (q : Coordinates d) (hq : q ∈ Model.domain d) : Tangent d :=
  ofModel q (by simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hq.isHermitian.eq)

@[simp] theorem toModel_lift (q : Coordinates d) (hq : q ∈ Model.domain d) :
    toModel d (lift q hq) = q := toModel_ofModel _ _

theorem lift_mem_Domain (q : Coordinates d) (hq : q ∈ Model.domain d) : lift q hq ∈ Domain d := by
  change (toModel d (lift q hq)).2.PosDef
  rw [toModel_lift]
  exact hq

/-- The intrinsic minimizer proposition is just the source energy and domain. -/
def IsMinimizer (V : E d → ℝ) (z : Tangent d) : Prop :=
  z ∈ Domain d ∧ ∀ x ∈ Domain d, HilbertCoordinates.energy V z ≤ HilbertCoordinates.energy V x

theorem isMinimizer_iff (V : E d → ℝ) (z : Tangent d) :
    Specification.IsMinimizer V (toModel d z) ↔ IsMinimizer V z := by
  constructor
  · intro h
    exact ⟨h.1, fun x hx => h.2 (toModel d x) hx⟩
  · rintro ⟨hz, hmin⟩
    refine ⟨hz, ?_⟩
    intro q hq
    simpa only [HilbertCoordinates.energy, toModel_lift] using hmin (lift q hq) (lift_mem_Domain q hq)

/-- Uniqueness of the actual source minimizer is equivalent to uniqueness in the
intrinsic Hilbert space, without imposing any extra state or norm assumptions. -/
theorem isUniqueMinimizer_iff (V : E d → ℝ) (z : Tangent d) :
    Specification.IsUniqueMinimizer V (toModel d z) ↔
      IsMinimizer V z ∧ ∀ y : Tangent d, IsMinimizer V y → y = z := by
  constructor
  · rintro ⟨hz, huniq⟩
    refine ⟨(isMinimizer_iff V z).mp hz, ?_⟩
    intro y hy
    apply toModel_injective d
    exact huniq (toModel d y) ((isMinimizer_iff V y).mpr hy)
  · rintro ⟨hz, huniq⟩
    refine ⟨(isMinimizer_iff V z).mpr hz, ?_⟩
    intro q hq
    let y := lift q hq.1
    have hy : IsMinimizer V y := by
      apply (isMinimizer_iff V y).mp
      simpa only [y, toModel_lift] using hq
    have heq := congrArg (toModel d) (huniq y hy)
    simpa only [y, toModel_lift] using heq

/-- A source minimizer gives exactly the intrinsic minimizer used by the
semiglobal stability theorem. -/
theorem lift_source_minimizer {V : E d → ℝ} {qstar : Coordinates d}
    (hstar : Specification.IsMinimizer V qstar) :
    ∃ z : Tangent d, toModel d z = qstar ∧ z ∈ Domain d ∧
      ∀ x ∈ Domain d, HilbertCoordinates.energy V z ≤ HilbertCoordinates.energy V x := by
  refine ⟨lift qstar hstar.1, toModel_lift _ _, lift_mem_Domain _ _, ?_⟩
  intro x hx
  simpa only [HilbertCoordinates.energy, toModel_lift] using hstar.2 (toModel d x) hx

end Paper38.SourceCoordinates
