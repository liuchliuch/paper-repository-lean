import Paper28.EuclideanAreaInput

/-! Pulling the actual local round metric on a relative spherical face
back along a continuous lift gives the source stratum metric identity. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Set Metric
universe w

theorem roundLiftOn_of_chart {Y : Type w} (metricY : MetricSpace Y) {d m : ℕ}
    (f : EuclideanAmbient d → Y) (g : EuclideanAmbient d → EuclideanAmbient m)
    (chart : EuclideanAmbient m → Y) (A F : Set (EuclideanAmbient d))
    (Q : Set (EuclideanAmbient m)) (hAF : A ⊆ F)
    (hImage : MapsTo g A Q) (hAgree : ∀ x ∈ A, f x = chart (g x))
    (hContinuous : ∀ x ∈ F, ContinuousAt g x)
    (hRound : ∀ u ∈ Q, ∃ r : ℝ, 0 < r ∧ ∀ v ∈ Q, ∀ w ∈ Q,
      dist v u < r → dist w u < r →
        @dist Y metricY.toDist (chart v) (chart w) = angular v w) :
    RoundLiftOn metricY f g A := by
  intro x hx
  obtain ⟨r,hr,hMetric⟩ := hRound (g x) (hImage hx)
  obtain ⟨δ,hδ,hg⟩ := Metric.continuousAt_iff.mp (hContinuous x (hAF hx)) r hr
  refine ⟨δ,hδ,?_⟩
  intro y hy z hz hyδ hzδ
  rw [hAgree y hy,hAgree z hz]
  exact hMetric (g y) (hImage hy) (g z) (hImage hz) (hg hyδ) (hg hzδ)

end Paper28
