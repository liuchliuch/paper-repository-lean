import BoundaryReduction.FiniteMeanCoordinates

open Real Set BigOperators Filter MeasureTheory
open scoped Classical
namespace BoundaryReduction.FiniteExponential

variable {α : Type} [Fintype α] [Nonempty α] {d : ℕ}
variable (p : FinProb α) (hp : ∀ y, 0 < p.w y) (Y : α → E d)
variable (hminimal : ∀ (a : E d) (b : ℝ), (∀ y, inner ℝ a (Y y) = b) → a = 0)
variable (B : Set (E d)) (hcontained : closure B ⊆ Set.range (mean p hp Y))

noncomputable def boundaryParameter (r : frontier B) : E d :=
  naturalParameter p hp Y ⟨(r : E d),hcontained (frontier_subset_closure r.2)⟩

include hminimal

lemma measurable_boundaryParameter : Measurable (boundaryParameter p hp Y B hcontained) :=
  (measurable_naturalParameter p hp Y hminimal).comp measurable_subtype_coe.subtype_mk

lemma mean_boundaryParameter (r : frontier B) : mean p hp Y (boundaryParameter p hp Y B hcontained r) = (r : E d) :=
  mean_naturalParameter p hp Y hminimal _

noncomputable def boundaryNaturalPrior (W : ProbabilityMeasure (frontier B)) : Measure (E d) :=
  (W : Measure (frontier B)).map (boundaryParameter p hp Y B hcontained)

lemma boundaryNaturalPrior_probability (W : ProbabilityMeasure (frontier B)) : IsProbabilityMeasure (boundaryNaturalPrior p hp Y B hcontained W) :=
  Measure.isProbabilityMeasure_map (measurable_boundaryParameter p hp Y hminimal B hcontained).aemeasurable

noncomputable def meanBoundaryMixture (W : ProbabilityMeasure (frontier B)) : FinProb α := by
  letI := boundaryNaturalPrior_probability p hp Y hminimal B hcontained W
  exact borelProb p hp Y (boundaryNaturalPrior p hp Y B hcontained W)

lemma meanBoundaryMixture_mass (W : ProbabilityMeasure (frontier B)) (y : α) :
    (meanBoundaryMixture p hp Y hminimal B hcontained W).w y =
      ∫ r : frontier B, (meanLaw p hp Y ⟨(r : E d),hcontained (frontier_subset_closure r.2)⟩).w y
        ∂(W : Measure (frontier B)) := by
  change (∫ θ, (tilt p hp Y θ).w y ∂(W : Measure (frontier B)).map _) = _
  exact integral_map (measurable_boundaryParameter p hp Y hminimal B hcontained).aemeasurable
    (continuous_tilt p hp Y y).aestronglyMeasurable

/-- Proposition 3.2: no countably additive Borel boundary prior in mean
coordinates can satisfy the global expected-log inequality. -/
theorem proposition_3_2_mean_borel [Nontrivial α]
    (W : ProbabilityMeasure (frontier B))
    (V : Finset α) (hV : V.Nonempty) (normal : V → E d)
    (hexpose : ∀ v : V, ∀ y, y ≠ (v : α) → inner ℝ (normal v) (Y y) < inner ℝ (normal v) (Y v))
    (g : α → ℝ) {L η : ℝ} (hL : 0 < L) (hη : 0 < η)
    (hg : ∀ y, |g y| ≤ L) (hpg : FinProb.expect p g = 0)
    (hsep : ∀ θ, mean p hp Y θ ∈ frontier B → η ≤ FinProb.expect (tilt p hp Y θ) g)
    (hgap : -log (vertexMass p V) < η^2/(2*L^2)) :
    ¬ (∀ μ : Set.range (mean p hp Y), (μ : E d) ∉ B →
      FinProb.klPos (meanBoundaryMixture p hp Y hminimal B hcontained W) p ≤
        FinProb.expect (meanLaw p hp Y μ)
          (fun y => log ((meanBoundaryMixture p hp Y hminimal B hcontained W).w y/p.w y))) := by
  let P := boundaryNaturalPrior p hp Y B hcontained W
  letI : IsProbabilityMeasure P := boundaryNaturalPrior_probability p hp Y hminimal B hcontained W
  have hs : ∀ᵐ θ ∂P, mean p hp Y θ ∈ frontier B := by
    apply (ae_map_iff (measurable_boundaryParameter p hp Y hminimal B hcontained).aemeasurable
      (p := fun θ : E d => mean p hp Y θ ∈ frontier B)
      (isClosed_frontier.measurableSet.preimage (continuous_mean p hp Y).measurable)).mpr
    exact Eventually.of_forall (fun r => by rw [mean_boundaryParameter p hp Y hminimal B hcontained]; exact r.2)
  intro hglobal
  apply proposition_3_2_borel p hp Y P V hV normal hexpose B hcontained hs g hL hη hg hpg hsep hgap
  intro θ hθ
  have hh := hglobal ⟨mean p hp Y θ,⟨θ,rfl⟩⟩ hθ
  simpa only [meanLaw,naturalParameter_mean p hp Y hminimal] using hh

end BoundaryReduction.FiniteExponential
