import Paper29.PilotConclusion

noncomputable section
open scoped BigOperators Classical
namespace Paper29.ProcessTools

/-- Independent product mass on the two ordered finite IID batches. -/
def batchMass {n m₀ m : ℕ} (π₀ π : Fin n → ℝ)
    (ω : (Fin m₀ → Fin n) × (Fin m → Fin n)) : ℝ :=
  Sampling.iidMass π₀ ω.1 * Sampling.iidMass π ω.2

theorem batchMass_nonneg {n m₀ m : ℕ} (π₀ π : Fin n → ℝ)
    (hp₀ : ∀ i, 0 ≤ π₀ i) (hp : ∀ i, 0 ≤ π i)
    (ω : (Fin m₀ → Fin n) × (Fin m → Fin n)) : 0 ≤ batchMass π₀ π ω :=
  mul_nonneg (Sampling.iidMass_nonneg π₀ hp₀ ω.1) (Sampling.iidMass_nonneg π hp ω.2)

theorem batchMass_sum {n m₀ m : ℕ} (π₀ π : Fin n → ℝ)
    (hs₀ : ∑ i, π₀ i = 1) (hs : ∑ i, π i = 1) :
    (∑ ω : (Fin m₀ → Fin n) × (Fin m → Fin n), batchMass π₀ π ω) = 1 := by
  rw [Fintype.sum_prod_type]
  unfold batchMass
  simp_rw [← Finset.mul_sum, Sampling.iidMass_sum π hs, mul_one]
  exact Sampling.iidMass_sum π₀ hs₀

/-- Integrating an actual conditional good-event bound in the finite product
space. The residual may be any pilot-only function; it need not be fixed
uniformly over all labels or depend on the main sample. -/
theorem independent_good_events {Ω₀ Ω : Type*} [Fintype Ω₀] [Fintype Ω]
    (p₀ : Ω₀ → ℝ) (p : Ω → ℝ) (hp₀ : ∀ ω, 0 ≤ p₀ ω) (hp : ∀ ω, 0 ≤ p ω)
    (hs₀ : ∑ ω, p₀ ω = 1) (hs : ∑ ω, p ω = 1)
    (E : Ω₀ → Prop) (F : Ω₀ → Ω → Prop)
    [DecidablePred E] [∀ ω₀, DecidablePred (F ω₀)] {δ₀ δ : ℝ} (hδ : 0 ≤ δ)
    (hE : 1-δ₀ ≤ Sampling.eventMass p₀ (Finset.univ.filter E))
    (hF : ∀ ω₀, E ω₀ → 1-δ ≤ Sampling.eventMass p (Finset.univ.filter (F ω₀))) :
    1-δ₀-δ ≤ Sampling.eventMass (fun ω : Ω₀ × Ω => p₀ ω.1*p ω.2)
      (Finset.univ.filter (fun ω => E ω.1 ∧ F ω.1 ω.2)) := by
  have he : Sampling.eventMass (fun ω : Ω₀ × Ω => p₀ ω.1*p ω.2)
      (Finset.univ.filter (fun ω => E ω.1 ∧ F ω.1 ω.2)) =
      ∑ ω₀ ∈ Finset.univ.filter E, p₀ ω₀ * Sampling.eventMass p (Finset.univ.filter (F ω₀)) := by
    simp only [Sampling.eventMass, Finset.sum_filter, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro ω₀ _
    by_cases h : E ω₀
    · simp only [h, true_and, ite_true]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ω _
      split_ifs <;> simp
    · simp [h]
  rw [he]
  have hmass : Sampling.eventMass p₀ (Finset.univ.filter E) ≤ 1 := by
    simpa only [Sampling.eventMass, hs₀] using
      eventMass_mono p₀ hp₀ (Finset.filter_subset E Finset.univ)
  have hb : (1-δ) * Sampling.eventMass p₀ (Finset.univ.filter E) ≤
      ∑ ω₀ ∈ Finset.univ.filter E, p₀ ω₀ * Sampling.eventMass p (Finset.univ.filter (F ω₀)) := by
    unfold Sampling.eventMass
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro ω₀ hω₀
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left
      (hF ω₀ (Finset.mem_filter.mp hω₀).2) (hp₀ ω₀)
  nlinarith [mul_le_mul_of_nonneg_left hmass hδ]

end Paper29.ProcessTools
