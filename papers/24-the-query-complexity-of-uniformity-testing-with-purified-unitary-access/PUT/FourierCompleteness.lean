import PUT.FourierModel

/-!
# Completeness of the actual phase characters

The integer matrix indexing the paper's functions `e n` is equivalent to the
ordinary multi-index on the coordinate torus. Consequently mathlib's proved
density theorem for torus characters gives completeness of the actual family
used in `FourierModel`, with its actual normalized Haar prior. No additional
Fourier theorem is assumed here.
-/
noncomputable section
namespace PUT.FourierModel
open MeasureTheory
open scoped ENNReal InnerProductSpace

attribute [local instance] Real.fact_zero_lt_one
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- Flattening the paper's integer matrix loses no torus frequency. -/
def flattenEquiv (d M : ℕ) : PhaseIndex d M ≃ (Coord d M → ℤ) where
  toFun := flatten
  invFun := fun n i j => n (i,j)
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

theorem flatten_surjective (d M : ℕ) : Function.Surjective (@flatten d M) :=
  (flattenEquiv d M).surjective

/-- The actual `e` family has precisely the full multi-Fourier range. -/
theorem range_e (d M : ℕ) :
    Set.range (@e d M) =
      Set.range (@UnitAddTorus.mFourierLp (Coord d M) _ 2 _) := by
  exact (flatten_surjective d M).range_comp _

/-- The span of the paper's actual phase characters is dense in its null prior. -/
theorem e_dense_span (d M : ℕ) :
    (Submodule.span ℂ (Set.range (@e d M))).topologicalClosure = ⊤ := by
  rw [range_e]
  exact UnitAddTorus.span_mFourierLp_closure_eq_top (by simp)

/-- The paper's `e n` form a Hilbert basis, including completeness. -/
def eBasis (d M : ℕ) : HilbertBasis (PhaseIndex d M) ℂ (NullL2 d M) :=
  HilbertBasis.mk (e_orthonormal d M) (e_dense_span d M).ge

@[simp] theorem coe_eBasis (d M : ℕ) : ⇑(eBasis d M) = @e d M :=
  HilbertBasis.coe_mk _ _

/-- Every null-prior `L²` function has its actual character expansion. -/
theorem e_hasSum {d M : ℕ} (f : NullL2 d M) :
    HasSum (fun n => inner ℂ (e n) f • e n) f := by
  simpa only [HilbertBasis.repr_apply_apply, coe_eBasis] using
    (eBasis d M).hasSum_repr f

end PUT.FourierModel
