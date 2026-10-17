import Paper12.Main
import Paper12.BlockSymmetry
import Paper12.OuterComplete

noncomputable section
namespace Paper12
open Matrix Classical
variable {X : Type} [Fintype X]

def synthesisProbability (U : Op X) : ℝ := (resourceLambda U)⁻¹ ^ 2

theorem synthesisProbability_pos (U : Op X) (hU : Uᴴ * U = 1) :
    0 < synthesisProbability U := by
  have h : 1 ≤ resourceLambda U := (coeff_mass_bounds U hU).1
  have hl : 0 < resourceLambda U := lt_of_lt_of_le (by norm_num) h
  exact sq_pos_of_pos (inv_pos.mpr hl)

theorem synthesisProbability_sqrt (U : Op X) (hU : Uᴴ * U = 1) :
    Real.sqrt (synthesisProbability U) = (resourceLambda U)⁻¹ := by
  apply Real.sqrt_sq
  have h : 1 ≤ resourceLambda U := (coeff_mass_bounds U hU).1
  exact inv_nonneg.mpr (by linarith)

theorem synthesis_blockEncodes (U : Op X) (hU : Uᴴ * U = 1) :
    BlockEncodes (blockCircuit (pauliCoeff U)).unitary (synthesisProbability U) U := by
  unfold BlockEncodes
  rw [blockCircuit_encoding U hU, synthesisProbability_sqrt U hU]
  simp only [resourceLambda, _root_.Complex.ofReal_inv]

theorem synthesis_ampK_bound (U : Op X) (hU : Uᴴ * U = 1) :
    ampK (synthesisProbability U) ≤ Nat.ceil (resourceLambda U) := by
  unfold ampK
  apply Nat.ceil_mono
  rw [synthesisProbability_sqrt U hU]
  have hl : 0 < resourceLambda U := lt_of_lt_of_le (by norm_num) (coeff_mass_bounds U hU).1
  calc Real.pi / (4 * (resourceLambda U)⁻¹) = (Real.pi / 4) * resourceLambda U := by
         field_simp
      _ ≤ resourceLambda U := by nlinarith [Real.pi_lt_four]

/-- Actual elementary Pauli-selector circuit followed by exact oblivious
amplification, with all M+5 workspace wires returned to zero. -/
theorem theorem_1_1_sufficiency {Γ : Subgroup (X ≃ X)} (U : Op X)
    (hU : Uᴴ * U = 1) (hn : 0 < Fintype.card X) (heq : Equivariant Γ U) :
    HasCleanSymmetricCircuit Γ U (resourceM U + 5) (sizeBound U) := by
  let A := blockCircuit (pauliCoeff U)
  let p := synthesisProbability U
  let C := obliviousCircuit A p
  have hs : Nonempty (Symmetric Γ C) := by
    obtain ⟨hA⟩ := blockCircuit_symmetric U heq
    exact obliviousCircuit_symmetric hA p
  refine ⟨(SelectorWire (pauliCoeff U) ⊕ Fin 3) ⊕ Fin 2, inferInstance, C,
    obliviousCircuit_clean A U p hU (synthesisProbability_pos U hU) (synthesis_blockEncodes U hU),
    ?_, ?_, hs⟩
  · simp only [Fintype.card_sum, Fintype.card_fin, selectorWire_card, resourceM]
    omega
  · have hA := blockCircuit_size (pauliCoeff U) hn
    have hK := synthesis_ampK_bound U hU
    calc C.size ≤ 32 * (A.size + 1) * (ampK p + 1) := obliviousCircuit_size A p
      _ ≤ 32 * (256 * Fintype.card X * (resourceM U + 1)) *
          (Nat.ceil (resourceLambda U) + 1) := Nat.mul_le_mul
            (Nat.mul_le_mul_left 32 hA) (Nat.add_le_add_right hK 1)
      _ = sizeBound U := by unfold sizeBound; ring

theorem theorem_1_1_equivalence {Γ : Subgroup (X ≃ X)} (U : Op X) (hU : Uᴴ * U = 1) :
    (∃ nW s, HasCleanSymmetricCircuit Γ U nW s) ↔ Equivariant Γ U := by
  constructor
  · rintro ⟨nW, s, h⟩
    exact theorem_1_1_necessity h
  · intro heq
    by_cases hn : 0 < Fintype.card X
    · exact ⟨resourceM U + 5, sizeBound U, theorem_1_1_sufficiency U hU hn heq⟩
    · have hz : Fintype.card X = 0 := Nat.eq_zero_of_not_pos hn
      letI : IsEmpty X := Fintype.card_eq_zero_iff.mp hz
      exact ⟨1, 1, theorem_1_1_of_isEmpty Γ U hU⟩

/-- The intermediate O(n M sqrt M) estimate in Theorem 1.1. -/
theorem sizeBound_sqrt (U : Op X) (hU : Uᴴ * U = 1) :
    (sizeBound U : ℝ) ≤ 49152 * (Fintype.card X : ℝ) * resourceM U *
      Real.sqrt (resourceM U) := by
  calc (sizeBound U : ℝ) ≤ 49152 * (Fintype.card X : ℝ) * resourceM U * resourceLambda U :=
      sizeBound_le U hU
    _ ≤ _ := mul_le_mul_of_nonneg_left (coeff_mass_bounds U hU).2 (by positivity)

/-- The workspace bound in equation (1), including M ≤ 4^n. -/
theorem workspaceBound_exponential (U : Op X) :
    workspaceBound U ≤ 4 ^ Fintype.card X + 5 :=
  Nat.add_le_add_right (pauli_support_bound U) 5

theorem corollary_4_2_action {G : Type} [Group G] (ρ : G →* (X ≃ X)) (U : Op X)
    (hU : Uᴴ * U = 1) (heq : ∀ g : G, U * R (ρ g) = R (ρ g) * U) :
    (∃ nW s, HasCleanSymmetricCircuit (Subgroup.map ρ ⊤) U nW s) ∧
    (0 < Fintype.card X → HasCleanSymmetricCircuit (Subgroup.map ρ ⊤) U
      (resourceM U + 5) (sizeBound U)) := by
  have hΓ : Equivariant (Subgroup.map ρ ⊤) U := by
    intro γ hγ
    obtain ⟨g, _, rfl⟩ := hγ
    exact heq g
  exact ⟨(theorem_1_1_equivalence U hU).mpr hΓ,
    fun hn => theorem_1_1_sufficiency U hU hn hΓ⟩
end Paper12
