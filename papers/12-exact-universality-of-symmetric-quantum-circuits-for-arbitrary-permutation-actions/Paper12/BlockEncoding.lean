import Paper12.PauliExpand
import Paper12.Selector
import Paper12.CircuitTools

/-!
# Pauli block encoding (Section 3)

Selector phase layer and three symbol-incidence stages give
`SEL(|ψ⟩|e_P⟩) = ω_P (P|ψ⟩)|e_P⟩`.  Combined with the one-hot preparation
`B`, the block circuit `A = (I ⊗ B†) SEL (I ⊗ B)` satisfies
`(⟨0| ⊗ I) A (|0⟩ ⊗ I) = U / λ`.

This file proves the algebraic content of equations (13) and (16): the
one-hot weighted Pauli sum equals `U/λ`, and selection on a one-hot sector
acts by `ω_P · P` on the active register.
-/

noncomputable section

namespace Paper12

open Matrix Complex Classical

variable {X : Type*} [Fintype X]

/-! ### Selector amplitudes and phases -/

theorem abs_eq_zero (z : ℂ) : Complex.abs z = 0 ↔ z = 0 := by
  constructor
  · intro h
    have := congrArg (fun r : ℝ => r ^ 2) h
    have h2 : Complex.abs z ^ 2 = Complex.normSq z := Complex.abs_sq z
    have : Complex.normSq z = 0 := by
      rw [← h2, h]
      simp
    have := Complex.normSq_eq_zero.mp this
    exact this
  · intro h; rw [h]; exact Complex.abs_zero

/-- On the support, `|α_P| > 0`, so the phase `ω_P = α_P / |α_P|` is defined. -/
theorem abs_pos_of_mem_support (α : Coeffs X) {w : PWord X}
    (hw : w ∈ coeffSupport α) : 0 < Complex.abs (α w) := by
  have hne : α w ≠ 0 := by
    simpa [coeffSupport, Finset.mem_filter] using hw
  exact (norm_pos_iff.mpr hne)

theorem abs_ne_zero_of_mem_support (α : Coeffs X) {w : PWord X}
    (hw : w ∈ coeffSupport α) : Complex.abs (α w) ≠ 0 :=
  ne_of_gt (abs_pos_of_mem_support α hw)

/-- On the support, `ω_P · |α_P| = α_P`. -/
theorem phase_mul_abs (α : Coeffs X) {w : PWord X}
    (hw : w ∈ coeffSupport α) :
    selectorPhase α w * (Complex.abs (α w) : ℂ) = α w := by
  unfold selectorPhase
  have hne : α w ≠ 0 := by
    simpa [coeffSupport, Finset.mem_filter] using hw
  rw [if_neg hne]
  -- `selectorPhase` is `α / |α|` on the support
  have hz : ((α w) / Complex.abs (α w)) * (Complex.abs (α w) : ℂ) = α w := by
    field_simp [abs_ne_zero_of_mem_support α hw]
  -- reduce the definition to that shape
  simpa using hz

/-- The defining identity of the selector parameters:
`d_P² · ω_P = α_P / λ` on the support. -/
theorem selector_sq_phase (α : Coeffs X) {w : PWord X}
    (hmass : 0 < coeffMass α) (hw : w ∈ coeffSupport α) :
    (((selectorAmp α w : ℝ) ^ 2 : ℂ) * selectorPhase α w)
      = ((coeffMass α : ℂ)⁻¹) * α w := by
  have habs : 0 < Complex.abs (α w) := abs_pos_of_mem_support α hw
  have hs : (selectorAmp α w : ℝ) ^ 2 = Complex.abs (α w) / coeffMass α := by
    unfold selectorAmp
    rw [Real.sq_sqrt (le_of_lt (div_pos habs hmass))]
  have hsc : (selectorAmp α w : ℂ) ^ 2 =
      (Complex.abs (α w) : ℂ) / (coeffMass α : ℂ) := by exact_mod_cast hs
  rw [hsc]
  have hne : α w ≠ 0 := by simpa [coeffSupport] using hw
  have habsc : (Complex.abs (α w) : ℂ) ≠ 0 := by exact_mod_cast habs.ne'
  have hmassc : (coeffMass α : ℂ) ≠ 0 := by exact_mod_cast hmass.ne'
  simp only [selectorPhase, if_neg hne]
  field_simp

/-- Selector action on a one-hot sector, equation (13):
the sector operator `ω_P · P` applies `P` and the scalar `ω_P`. -/
theorem select_on_onehot (α : Coeffs X) (w : PWord X) (ψ : Vec X) :
    applyOp (selectorPhase α w • pop X w) ψ
      = selectorPhase α w • applyOp (pop X w) ψ := by
  exact applyOp_smul _ _ _

/-- Algebraic content of equation (16): the all-zero workspace block of the
composed circuit is the one-hot weighted Pauli sum, equal to `U / λ`. -/
theorem block_encoding_identity (α : Coeffs X) (U : Op X)
    (hU : U = ∑ w, α w • pop X w)
    (hmass : 0 < coeffMass α) :
    ∑ w ∈ coeffSupport α,
        (((selectorAmp α w) ^ 2 : ℂ) * selectorPhase α w) • pop X w
      = ((coeffMass α : ℂ)⁻¹) • U := by
  have hsplit : ∀ w : PWord X, w ∈ coeffSupport α →
      ((((selectorAmp α w) ^ 2 : ℂ) * selectorPhase α w) • pop X w)
        = (((coeffMass α : ℂ)⁻¹) * α w) • pop X w := by
    intro w hw
    rw [selector_sq_phase α hmass hw]
  rw [Finset.sum_congr rfl hsplit]
  have hcancel : ∑ w ∈ coeffSupport α, (((coeffMass α : ℂ)⁻¹) * α w) • pop X w
      = ((coeffMass α : ℂ)⁻¹) • ∑ w ∈ coeffSupport α, α w • pop X w := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl ?_
    intro w _
    rw [smul_smul]
  rw [hcancel]
  have hrestrict : ∑ w : PWord X, α w • pop X w
      = ∑ w ∈ coeffSupport α, α w • pop X w := by
    classical
    rw [← Finset.sum_subset (Finset.subset_univ _)]
    intro w _ hw
    simp only [coeffSupport, Finset.mem_filter, Finset.mem_univ, true_and] at hw
    rw [not_not.mp hw, zero_smul]
  rw [← hrestrict, ← hU]

/-- Specialisation of the block identity when `U` is already its Pauli
expansion with coefficients `α`. -/
theorem block_encoding_identity' (α : Coeffs X)
    (hmass : 0 < coeffMass α) :
    ∑ w ∈ coeffSupport α,
        (((selectorAmp α w) ^ 2 : ℂ) * selectorPhase α w) • pop X w
      = ((coeffMass α : ℂ)⁻¹) • ∑ w, α w • pop X w :=
  block_encoding_identity α (∑ w, α w • pop X w) rfl hmass

/-! ### Incidence layers -/

/-- An incidence layer is preserved by a selector permutation `τ` when
`P` and `τ P` share the symbol at their active images; the identity
`(τ P)_{τ x} = P_x` guarantees this. -/
theorem incidence_compat (τ : PWord X ≃ PWord X) (γ : X ≃ X)
    (w : PWord X) (x : X)
    (hact : ∀ w y, τ w (γ y) = w y) :
    (τ w) (γ x) = w x := hact w x

end Paper12
