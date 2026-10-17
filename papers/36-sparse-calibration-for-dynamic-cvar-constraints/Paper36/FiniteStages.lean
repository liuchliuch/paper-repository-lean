import Paper36.StageRisk

/-! Finite stage masses in B.3. Padding outside the H actual risk operators
introduces no hypothesis on an unused stage: any valid finite mass vector has
a valid total extension, and the risk and weights are invariant under padding. -/
namespace Paper36.FiniteStages
open Paper36.Simulation
noncomputable section

/-- Source indices 1,...,H, padded by the expectation operator elsewhere. -/
def extend {H : ℕ} (a : Fin H → ℝ) (j : ℕ) : ℝ :=
  if hj : 1 ≤ j ∧ j ≤ H then a ⟨j-1, by omega⟩ else 1

lemma extend_at {H : ℕ} (a : Fin H → ℝ) {j : ℕ} (hj : 1 ≤ j ∧ j ≤ H) :
    extend a j = a ⟨j-1, by omega⟩ := by simp only [extend, dif_pos hj]

lemma extend_valid {H : ℕ} (a : Fin H → ℝ) (ha : ∀ i, 0 < a i ∧ a i ≤ 1) :
    ∀ j, 0 < extend a j ∧ extend a j ≤ 1 := by
  intro j
  unfold extend
  split_ifs with hj
  · exact ha _
  · exact ⟨by norm_num, le_rfl⟩

variable {S A : Type*} [Fintype S] [Fintype A]

/-- Actual risk only reads masses h+1,...,h+n. -/
theorem risk_mass_congr (a b : ℕ → ℝ) (c : ℕ → S → A → ℝ)
    (π : Policy S A) (p : Kernel S A) (n h : ℕ) (s : S)
    (hab : ∀ j, h+1 ≤ j → j ≤ h+n → a j = b j) :
    StageRisk.risk a c π p n h s = StageRisk.risk b c π p n h s := by
  induction n generalizing h s with
  | zero => rfl
  | succ n ih =>
    rw [StageRisk.risk, StageRisk.risk, hab (h+1) le_rfl (by omega)]
    congr 1
    funext x
    rw [ih (h+1) x.2 (fun j hj hj' => hab j (by omega) (by omega))]

/-- Every source finite mass vector can be used with the total-function APIs
without changing the actual finite-horizon nested-risk functional. -/
theorem finite_mass_representation {H : ℕ} (a : Fin H → ℝ)
    (ha : ∀ i, 0 < a i ∧ a i ≤ 1) :
    (∀ j, 0 < extend a j ∧ extend a j ≤ 1) ∧
    ∀ (b : ℕ → ℝ), (∀ j (hj : 1 ≤ j ∧ j ≤ H), b j = a ⟨j-1, by omega⟩) →
      ∀ (c : ℕ → S → A → ℝ) (π : Policy S A) (p : Kernel S A) (s : S),
        StageRisk.risk b c π p H 0 s = StageRisk.risk (extend a) c π p H 0 s := by
  refine ⟨extend_valid a ha, ?_⟩
  intro b hb c π p s
  apply risk_mass_congr
  intro j hj hj'
  have hj0 : 1 ≤ j ∧ j ≤ H := by constructor <;> omega
  rw [hb j hj0, extend_at a hj0]

/-- The transition-error weights ignore every mass outside their original
finite product ranges, including the last risk-operator mass. -/
theorem finite_weight_representation {H : ℕ} (a : Fin H → ℝ) (b : ℕ → ℝ)
    (hb : ∀ j (hj : 1 ≤ j ∧ j ≤ H), b j = a ⟨j-1, by omega⟩) :
    Weights.stageWsq b H = Weights.stageWsq (extend a) H ∧
    Weights.stagew b H = Weights.stagew (extend a) H := by
  have heq : ∀ j ∈ Finset.Icc 1 (H-1), b j = extend a j := by
    intro j hj
    have hj' : 1 ≤ j ∧ j ≤ H := by have := Finset.mem_Icc.1 hj; omega
    rw [hb j hj', extend_at a hj']
  exact ⟨Weights.stageWsq_congr heq, Weights.stagew_congr heq⟩

end
end Paper36.FiniteStages
