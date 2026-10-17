import Paper29.ProcessComparison
import Paper29.ChainingPullback

noncomputable section
open scoped ENNReal
namespace Paper29.Chaining

/-- Inflating design scores only decreases the actual Huber metric. -/
theorem huberMetric_antitone {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (τ σ : Fin n → ℝ) (hτ : ∀ i, 0 < τ i) (h : ∀ i, τ i ≤ σ i)
    (x y : Fin d → ℝ) : huberMetric A σ x y ≤ huberMetric A τ x y := by
  apply iSup_le
  intro i
  apply le_iSup_of_le i
  apply ENNReal.ofReal_le_ofReal
  apply Real.sqrt_le_sqrt
  exact div_le_div_of_nonneg_left (huber_nonneg _) (hτ i) (h i)

end Paper29.Chaining
namespace Paper29.ProcessTools

theorem ScoreGeometry.mono {n d : ℕ} {A : Matrix (Fin n) (Fin d) ℝ}
    {τ σ : Fin n → ℝ} {G : ℝ} (cover : ScoreGeometry A τ G)
    (hτ : ∀ i, 0 < τ i) (h : ∀ i, τ i ≤ σ i) : ScoreGeometry A σ G := by
  intro R hR
  have hh := Chaining.gamma2_pullback (id : Ball A R → Ball A R)
    (fun x y => Chaining.huberMetric A σ x y)
    (fun x y => Chaining.huberMetric A τ x y)
    (fun x y => Chaining.huberMetric_antitone A τ σ hτ h x y)
  exact hh.trans (cover R hR)

end Paper29.ProcessTools
