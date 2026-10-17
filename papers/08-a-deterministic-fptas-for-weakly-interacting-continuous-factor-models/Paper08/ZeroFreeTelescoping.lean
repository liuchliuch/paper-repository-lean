import Paper08.ZeroFreeMarginal

/-! # Finite occurrence telescoping of proved replacement phase bounds -/
noncomputable section
namespace Paper08.ZeroFreeInduction
open Integral CubeMarginal ComplexSector

variable {n m r c : ℕ} {q θ : ℝ} {z : ℂ}

/-- The finitely many incident occurrences suffice for the entire coordinate
 comparison. The internal replacement premise is discharged by the actual
 interpolation-path theorem in `ZeroFreeInduction.lean`. -/
theorem coordinatePhase_of_replacements (hq : 0 ≤ q)
    (hbudget : 2 * (c : ℝ) * ‖z‖ * q ≤ θ)
    (M : Model n m r c q) (S : Finset (Fin n))
    (hreplace : ∀ (x : Fin n → ℝ), x ∈ cube n → ∀ (j : Fin n), j ∉ S →
      ∀ (a : ℝ) (ha : a ∈ Set.Icc (0 : ℝ) 1),
      ∀ (b : ℝ) (hb : b ∈ Set.Icc (0 : ℝ) 1), ∀ A : Finset (Fin m),
      ∀ e ∈ M.incident j, e ∉ A →
      Phase ((M.freezeSet j A ha hb).partial S z x)
        ((M.freezeSet j (insert e A) ha hb).partial S z x)
        (2 * ‖z‖ * q)) : CoordinatePhase M S z θ := by
  classical
  intro x hx j hj a ha b hb
  let I := M.incident j
  let F : Finset (Fin m) → ℂ := fun A => (M.freezeSet j A ha hb).partial S z x
  have hstep : ∀ A ⊆ I, ∀ e ∈ I, e ∉ A → Phase (F A) (F (insert e A)) (2 * ‖z‖ * q) := by
    intro A hAI e he heA
    exact hreplace x hx j hj a ha b hb A e he heA
  have ht := phase_finset_telescope I F (2 * ‖z‖ * q) hstep
  have hleft : F ∅ = M.partial S z (Function.update x j a) := by
    unfold F Model.partial
    rw [avg_update S (M.exponential z) x j a hj]
    apply avg_congr S _ hx
    intro y hy
    simp only [Model.exponential, Model.freezeSet_empty_total]
  have hright : F I = M.partial S z (Function.update x j b) := by
    unfold F Model.partial
    rw [avg_update S (M.exponential z) x j b hj]
    apply avg_congr S _ hx
    intro y hy
    change Complex.exp (z * ((M.freezeSet j (M.incident j) ha hb).total y : ℂ)) = _
    rw [M.freezeSet_incident_total j ha hb hy]
    rfl
  rw [hleft, hright] at ht
  apply ht.mono
  calc
    (I.card : ℝ) * (2 * ‖z‖ * q) ≤ (c : ℝ) * (2 * ‖z‖ * q) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast M.card_incident_le j) (by positivity)
    _ = 2 * (c : ℝ) * ‖z‖ * q := by ring
    _ ≤ θ := hbudget

end Paper08.ZeroFreeInduction
