import Paper25.Resources
import Paper25.SourceSimulation

/-! Concrete positive parameters for the actual coherent filter and its
physical registers. The phase register is the least padded power of two,
and the five additional filter bits are the four block bits and rotation. -/
noncomputable section
namespace Paper25

theorem bias_parameters {J K : ℝ} (hJ : 1 ≤ J) (hK : 1 ≤ K) :
    0 < biasLam J K ∧ biasLam J K / 3 ≤ 1 ∧
      0 < biasEps J K ∧ biasEps J K ≤ 1 := by
  have hJpos : 0 < J := lt_of_lt_of_le zero_lt_one hJ
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hJ2 : 1 ≤ J^2 := one_le_pow₀ hJ
  have hK3 : 1 ≤ K^3 := one_le_pow₀ hK
  have hden : 1 ≤ 100 * J^2 * K^3 := by nlinarith
  have hl : 0 < biasLam J K := biasLam_pos hJpos hKpos
  have hlle : biasLam J K ≤ 1 := by
    unfold biasLam
    exact (div_le_one (by positivity)).2 hden
  refine ⟨hl, by linarith, div_pos hl (by positivity), ?_⟩
  unfold biasEps
  exact (div_le_one (by positivity)).2 (by linarith)

namespace SimulationParameters
open StatePreparation SourceSimulation

def clockBits (T : ℕ) : ℕ := ceilLog2 (T+1)
def phaseBitsFor (ell s : ℕ) : ℕ :=
  phaseBits (Fintype.card (Bits ell)) (Fintype.card (WorkSpace s))
def filterBits (ell s : ℕ) : ℕ := phaseBitsFor ell s + 5

lemma clock_card (T : ℕ) : Fintype.card (Bits (clockBits T)) = clockSize T := by
  simp [Bits, clockBits, clockSize, powerTwoCeil]

lemma clock_valid (T : ℕ) : T+1 ≤ Fintype.card (Bits (clockBits T)) := by
  rw [clock_card]
  exact (clockSize_spec T).1

lemma work_card (s : ℕ) : Fintype.card (WorkSpace s) = 2^(s+1) := by
  simp [WorkSpace, Bits, pow_succ, Nat.mul_comm]

lemma phase_card (ell s : ℕ) :
    2 ^ phaseBitsFor ell s =
      phaseLabels (Fintype.card (Bits ell)) (Fintype.card (WorkSpace s)) := rfl

/-- All interval and phase-resolution requirements are discharged for the
paper's actual resource functions, independently of the catalyst size. -/
theorem filter_parameters (ell s : ℕ) :
    let J := Fintype.card (Bits ell)
    let K := Fintype.card (WorkSpace s)
    let lam := biasLam J K
    let eps := biasEps J K
    0 < lam ∧ lam/3 ≤ 1 ∧ 0 < eps ∧ eps ≤ 1 ∧
      0 < 2 ^ phaseBitsFor ell s ∧
      4096 / ((lam/3)*eps^2) ≤ (2 ^ phaseBitsFor ell s : ℕ) := by
  dsimp only
  have hj : 0 < Fintype.card (Bits ell) := by simp [Bits]
  have hk : 0 < Fintype.card (WorkSpace s) := by rw [work_card]; positivity
  obtain ⟨hl,hll,he,hel⟩ := bias_parameters
    (by exact_mod_cast hj : (1:ℝ) ≤ Fintype.card (Bits ell))
    (by exact_mod_cast hk : (1:ℝ) ≤ Fintype.card (WorkSpace s))
  refine ⟨hl,hll,he,hel,by positivity,?_⟩
  rw [phase_card]
  exact (phaseLabels_spec hj hk).1

/-- The physical readout's actual bit count agrees with the global resource
formula, counting the designated output qubit among initialized work bits. -/
lemma small_qubits (s T : ℕ) :
    smallQubits (clockBits T) s (filterBits (clockBits T) s) =
      simulatorSmallQubits (s+1) T := by
  unfold smallQubits filterBits phaseBitsFor simulatorSmallQubits
  rw [clock_card, work_card]
  unfold clockBits
  omega

end SimulationParameters
end Paper25
