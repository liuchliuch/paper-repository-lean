import BoundaryReduction.GaussianNormalization
import BoundaryReduction.CompactPrior
import Mathlib.Topology.Connected.Clopen
import Mathlib.Analysis.Normed.Module.FiniteDimension

open Real Set MeasureTheory
open scoped Classical NNReal
namespace BoundaryReduction.Gaussian

variable {d : ℕ} {Γ : Set (Space d)} [CompactSpace Γ]
variable (K : Space d →L[ℝ] Space d) (Z : Measure (Space d)) [ProbabilityTheory.IsGaussian Z]

/-- Existence of a genuine Borel minimizer for the compact-prior entropy integral. -/
theorem exists_entropy_minimizer
    (hΓ : Γ.Nonempty) (R : ℝ≥0) (hR : ∀ r : Γ, ‖(r : Space d)‖ ≤ R)
    (hK : ∀ v : Space d, 0 ≤ inner ℝ v (K v)) :
    ∃ W : ProbabilityMeasure Γ, ∀ V : ProbabilityMeasure Γ,
      mixtureEntropy K Z W ≤ mixtureEntropy K Z V := by
  obtain ⟨r,hr⟩ := hΓ
  let W₀ : ProbabilityMeasure Γ := ⟨Measure.dirac ⟨r,hr⟩, inferInstance⟩
  obtain ⟨W,_,hmin⟩ := (CompactPrior.probabilityMeasure_compact Γ).exists_isMinOn
    (f := mixtureEntropy K Z) ⟨W₀, Set.mem_univ _⟩
    (continuous_mixtureEntropy K Z R hR hK).continuousOn
  exact ⟨W, fun V => hmin (Set.mem_univ V)⟩

/-- The boundary of a bounded open neighborhood is a nonempty compact set (d≥1). -/
lemma compact_nonempty_boundary {B : Set (Space d)} (hd : 1 ≤ d)
    (hB : IsOpen B) (h0 : (0 : Space d) ∈ B) (hb : Bornology.IsBounded B) :
    IsCompact (frontier B) ∧ (frontier B).Nonempty := by
  letI : NeZero d := ⟨by omega⟩
  constructor
  · exact hb.isCompact_closure.of_isClosed_subset isClosed_frontier frontier_subset_closure
  · apply nonempty_frontier_iff.mpr
    refine ⟨⟨0,h0⟩, ?_⟩
    intro heq
    exact NormedSpace.unbounded_univ ℝ (Space d) (heq ▸ hb)

/-- The existence assertion of Section 4.1 on every bounded open neighborhood of zero. -/
theorem exists_boundary_entropy_minimizer {B : Set (Space d)} (hd : 1 ≤ d)
    (hB : IsOpen B) (h0 : (0 : Space d) ∈ B) (hb : Bornology.IsBounded B)
    (hK : ∀ v : Space d, 0 ≤ inner ℝ v (K v)) :
    ∃ W : ProbabilityMeasure (frontier B), ∀ V : ProbabilityMeasure (frontier B),
      mixtureEntropy K Z W ≤ mixtureEntropy K Z V := by
  have hc := compact_nonempty_boundary hd hB h0 hb
  letI : CompactSpace (frontier B) := isCompact_iff_compactSpace.mp hc.1
  obtain ⟨R,hRpos,hR⟩ := hc.1.isBounded.exists_pos_norm_le
  exact exists_entropy_minimizer K Z hc.2 ⟨R,hRpos.le⟩ (fun r => hR r r.2) hK

end BoundaryReduction.Gaussian
