import Paper28.StrictEuclideanApproximation
import Paper28.NeighborhoodPushforwardInput

/-! Shrinking support is eventually contained in one compact subset of
the actual retraction domain; the locally Lipschitz map has one finite
Lipschitz constant there. No global retraction estimate is assumed. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Filter Metric Set
open scoped Topology

theorem compact_neighborhood_tail {X : Type*} [MetricSpace X] [ProperSpace X]
    (K U : Set X) (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (Kj : ℕ → Set X) (ρ : ℕ → ℝ) (hρ : Tendsto ρ atTop (𝓝 0))
    (hLoc : ∀ i, Kj i ⊆ thickening (ρ i) K) :
    ∃ N : Set X, IsCompact N ∧ K ⊆ N ∧ N ⊆ U ∧
      ∃ i₀ : ℕ, ∀ i, Kj (i+i₀) ⊆ N := by
  obtain ⟨δ,hδ,hδU⟩ := hK.exists_cthickening_subset_open hU hKU
  have he : ∀ᶠ i in atTop, ρ i < δ := (tendsto_order.mp hρ).2 δ hδ
  obtain ⟨i₀,hi₀⟩ := eventually_atTop.mp he
  refine ⟨cthickening δ K,hK.cthickening,self_subset_cthickening _,hδU,i₀,?_⟩
  intro i
  exact (hLoc (i+i₀)).trans ((thickening_mono (hi₀ (i+i₀) (Nat.le_add_left _ _)).le K).trans
    (thickening_subset_cthickening δ K))

theorem compact_lipschitz_neighborhood_tail {X Y : Type*} [MetricSpace X] [ProperSpace X] [MetricSpace Y]
    (K U : Set X) (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (Kj : ℕ → Set X) (ρ : ℕ → ℝ) (hρ : Tendsto ρ atTop (𝓝 0))
    (hLoc : ∀ i, Kj i ⊆ thickening (ρ i) K)
    (f : X → Y) (hf : LipschitzNearSet inferInstance inferInstance f U) :
    ∃ N : Set X, IsCompact N ∧ K ⊆ N ∧ N ⊆ U ∧
      ∃ L : NNReal, LipschitzOnWith L f N ∧ ∃ i₀ : ℕ, ∀ i, Kj (i+i₀) ⊆ N := by
  obtain ⟨N,hN,hKN,hNU,i₀,hi₀⟩ := compact_neighborhood_tail K U hK hU hKU Kj ρ hρ hLoc
  obtain ⟨L,hL⟩ := LipschitzNearSet.compact_restrict f U N hf hNU hN
  refine ⟨N,hN,hKN,hNU,L,LipschitzOnWith.of_dist_le_mul ?_,i₀,hi₀⟩
  intro x hx y hy
  exact hL.dist_le_mul (⟨x,hx⟩ : N) (⟨y,hy⟩ : N)

end Paper28
