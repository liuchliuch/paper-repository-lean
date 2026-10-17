import Paper29.ProcessTools

noncomputable section
open scoped BigOperators
namespace Paper29.ProcessTools

theorem eventMass_mono {Ω : Type*} [Fintype Ω] (p : Ω → ℝ)
    (hp : ∀ ω, 0 ≤ p ω) {E F : Finset Ω} (hEF : E ⊆ F) :
    Sampling.eventMass p E ≤ Sampling.eventMass p F :=
  Finset.sum_le_sum_of_subset_of_nonneg hEF (fun ω _ _ => hp ω)

/-- A true finite-probability event bound, including its good-event complement. -/
theorem good_event_of_expectation {Ω : Type*} [Fintype Ω]
    (p X : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) (htotal : ∑ ω, p ω = 1)
    (hX : ∀ ω, 0 ≤ X ω) {a δ : ℝ} (ha : 0 < a)
    (he : (∑ ω, p ω * X ω) ≤ δ * a) :
    1 - δ ≤ Sampling.eventMass p (Finset.univ.filter (fun ω => X ω ≤ a)) := by
  classical
  have hm := Sampling.finite_markov p X hp hX a ha
  have hsub : Finset.univ.filter (fun ω => a < X ω) ⊆
      Finset.univ.filter (fun ω => a ≤ X ω) := by
    intro ω hω
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hω).2.le⟩
  have hbad := (eventMass_mono p hp hsub).trans hm
  have hbad' : Sampling.eventMass p (Finset.univ.filter (fun ω => a < X ω)) ≤ δ :=
    hbad.trans ((div_le_iff₀ ha).2 he)
  have hsplit : Sampling.eventMass p (Finset.univ.filter (fun ω => X ω ≤ a)) +
      Sampling.eventMass p (Finset.univ.filter (fun ω => a < X ω)) = 1 := by
    simp only [Sampling.eventMass, Finset.sum_filter]
    rw [← Finset.sum_add_distrib]
    convert htotal using 1
    apply Finset.sum_congr rfl
    intro ω _
    by_cases h : X ω ≤ a
    · simp [h, not_lt.mpr h]
    · simp [h, lt_of_not_ge h]
  linarith

end Paper29.ProcessTools
