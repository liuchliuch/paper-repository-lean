import PsgEst.ConditionalMain
import PsgEst.PaulinProof
import PsgEst.MatrixFreedmanTheorem

/-! Both original concentration inputs and the unconditioned Proposition 1. -/
open Matrix BigOperators Real Classical
namespace PsgEst
variable {d : ℕ}

/-- The originally external probability inputs are genuine proved theorems. -/
theorem externalConcentrationInputs_proved [NeZero d] : ExternalConcentrationInputs d := by
  constructor
  · intro Q st _
    exact PaulinProof.paulin_original Q st
  · intro Q mu _ _
    exact matrixFreedman_proved Q mu

/-- Original quantitative relative-Laplacian concentration, with no
Bernstein, Freedman or other result-level input hypothesis. -/
theorem proposition_1_closed (m : ℕ) (Q : Stoch d) (st : Stationary Q) [NeZero d]
    (τ η : ℝ) (mu0 : Fin d → ℝ)
    (hτ : 0 < τ) (hη : 0 < η) (hη' : η ≤ 1 / 4)
    (hm : (1 : ℝ) ≤ m * gammaPS Q st)
    (hmu : ∀ i, 0 ≤ mu0 i) (hsum : ∑ i, mu0 i = 1) :
    let p := Stationary.star st
    let Γ := gammaPS Q st
    let h := 1 - sigma2 (simil st.mu Q.P)
    pathMeasure Q.P mu0
      (Finset.univ.filter fun Y : Fin (m + 1) → Fin d =>
        ¬ (degPos Y ∧
          |(1 - sigma2 (lHat Y)) - h| ≤ η * (3 * h + τ) / (1 - η)))
      ≤ 4 * d / p * exp (-(m * p * Γ * η ^ 2) / 36)
        + 4 * (d : ℝ) * exp (-(3 * m * p * τ * η ^ 2) / 16) := by
  have hpr := RelativeConcentration.proposition_1_of_external Q st τ η mu0
    hτ hη hη' hm hmu hsum (PaulinProof.paulin_original Q st)
    (matrixFreedman_proved Q mu0)
  convert hpr using 1 <;> congr 1 <;> ext Y <;> simp [RelativeConcentration.good]

end PsgEst
