import Paper36.PosteriorAlgorithm

/-! Quantitative range of the automatically induced gap. These bounds allow
the source's parameter-only performance envelope to absorb its budget term
without placing an extra upper bound on the original budget. -/
namespace Paper36.Prior
open Set MeasureTheory Paper36.Regularity Paper36.Nested
noncomputable section
variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]

lemma minimumRisk_le_horizon (α : ℝ) (hα : 0 ≤ α) (H : ℕ)
    (c : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Icc 0 1)
    (s₀ : S) (q : Kernel S A) : minimumRisk α c H 0 s₀ q ≤ H := by
  obtain ⟨π,hπ⟩ := exists_minimumRisk α c H 0 s₀ q
  rw [hπ]
  exact (risk_bounds α hα c hc π q H 0 s₀).2

/-- The actual maximum minimum risk lies in [0,H] for every probability prior. -/
theorem max_minimumRisk_bounds (ν : Measure (Kernel S A)) [IsProbabilityMeasure ν]
    (α : ℝ) (hα : 0 ≤ α) (H : ℕ)
    (c : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Icc 0 1) (s₀ : S) :
    0 ≤ sSup (minimumRisk α c H 0 s₀ '' ν.support) ∧
      sSup (minimumRisk α c H 0 s₀ '' ν.support) ≤ H := by
  have hν : ν ≠ 0 := by
    intro hz
    have hm : ν Set.univ = 1 := measure_univ
    simp [hz] at hm
  obtain ⟨q,hq⟩ := ν.nonempty_support hν
  have hbound : BddAbove (minimumRisk α c H 0 s₀ '' ν.support) := by
    refine ⟨H, ?_⟩
    rintro _ ⟨p,_,rfl⟩
    exact minimumRisk_le_horizon α hα H c hc s₀ p
  constructor
  · exact (Algorithm.minimumRisk_nonneg α hα c hc q H s₀).trans
      (le_csSup hbound (Set.mem_image_of_mem _ hq))
  · apply csSup_le ⟨_, Set.mem_image_of_mem _ hq⟩
    rintro _ ⟨p,_,rfl⟩
    exact minimumRisk_le_horizon α hα H c hc s₀ p

/-- In particular tau <= Delta_*+H: tau is harmless in the source scaling. -/
theorem induced_gap_budget_bounds (ν : Measure (Kernel S A)) [IsProbabilityMeasure ν]
    (α τ : ℝ) (hα : 0 ≤ α) (H : ℕ)
    (c : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Icc 0 1) (s₀ : S) :
    τ - (H:ℝ) ≤ τ - sSup (minimumRisk α c H 0 s₀ '' ν.support) ∧
    τ - sSup (minimumRisk α c H 0 s₀ '' ν.support) ≤ τ ∧
    τ ≤ (τ - sSup (minimumRisk α c H 0 s₀ '' ν.support)) + H := by
  have hb := max_minimumRisk_bounds ν α hα H c hc s₀
  constructor
  · linarith
  · constructor <;> linarith

end
end Paper36.Prior
