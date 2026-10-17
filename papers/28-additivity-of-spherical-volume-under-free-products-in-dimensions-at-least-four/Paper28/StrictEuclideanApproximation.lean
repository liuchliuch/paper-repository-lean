import Paper28.LocalizedEuclideanCycles
import Paper28.StrictTangentMeasures
import Mathlib.Topology.Order.Bornology

/-! Source (15)--(16) together: the constructed exact polyhedral cycles
have shrinking support, strict mass convergence and actual weak convergence
of their spatial-oriented-tangent measures. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Filter Set
open scoped Topology
universe v

theorem common_compact_of_shrinking_support {X : Type*} [MetricSpace X] [ProperSpace X]
    (K : Set X) (hK : IsCompact K) (Kj : ℕ → Set X) (ρ : ℕ → ℝ)
    (hρ : Tendsto ρ atTop (𝓝 0)) (hLoc : ∀ i, Kj i ⊆ Metric.thickening (ρ i) K) :
    ∃ L : Set X, IsCompact L ∧ K ⊆ L ∧ ∀ i, Kj i ⊆ L := by
  obtain ⟨R,hR⟩ := (Metric.isBounded_range_of_tendsto ρ hρ).bddAbove
  refine ⟨Metric.cthickening R K,hK.cthickening,Metric.self_subset_cthickening _,?_⟩
  intro i
  exact (hLoc i).trans ((Metric.thickening_mono (hR (mem_range_self i)) K).trans
    (Metric.thickening_subset_cthickening R K))

theorem strict_euclidean_polyhedral_approximation (hRes : StrictPolarMeasureContinuityInput.{0}) {d : ℕ}
    (I : CompactIntegralCurrentAlgebraInput.{0,v} (EuclideanAmbient d) inferInstance)
    (S : EuclideanSimplexIntegrationInput d I) (E : EuclideanDeformationInput d I S)
    (R : EuclideanCurrentTangentInput d I) (k : ℕ) (T : I.Current (k+1))
    (hCycle : I.boundary k T = 0) :
    ∃ Ti : ℕ → I.Current (k+1), ∃ Si : ℕ → I.Current (k+2), ∃ ρ : ℕ → ℝ,
      (∀ i, Ti i ∈ euclideanPolyhedralCurrents S (k+1)) ∧
      (∀ i, I.boundary k (Ti i) = 0) ∧
      (∀ i, T-Ti i = I.boundary (k+1) (Si i)) ∧
      Tendsto (fun i => I.mass (Ti i)) atTop (𝓝 (I.mass T)) ∧
      Tendsto (fun i => I.mass (Si i)) atTop (𝓝 0) ∧
      (∀ i, 0 < ρ i) ∧ Tendsto ρ atTop (𝓝 0) ∧
      (∀ i, I.support (Ti i) ∪ I.support (Si i) ⊆ Metric.thickening (ρ i) (I.support T)) ∧
      Tendsto (fun i => orientedTangentMeasure R (Ti i)) atTop (𝓝 (orientedTangentMeasure R T)) := by
  obtain ⟨Ti,Si,ρ,hPoly,hCycles,hHom,hMass,hFill,hρ,hρT,hLoc⟩ :=
    localized_euclidean_cycle_approximation I S E k T hCycle
  obtain ⟨M,hM⟩ := (Metric.isBounded_range_of_tendsto (fun i => I.mass (Ti i)) hMass).bddAbove
  obtain ⟨K,hK,hTK,hTiK⟩ := common_compact_of_shrinking_support (I.support T)
    (I.support_compact T) (fun i => I.support (Ti i)) ρ hρT (fun i _ hx => hLoc i (Or.inl hx))
  exact ⟨Ti,Si,ρ,hPoly,hCycles,hHom,hMass,hFill,hρ,hρT,hLoc,
    strict_tangent_measure_tendsto hRes I R T Ti Si hHom hFill hMass
      ⟨M,fun i => hM (mem_range_self i)⟩ ⟨K,hK,hTK,hTiK⟩⟩

end Paper28
