import BoundaryReduction.ExposedMeanBorel

open Real Set BigOperators Filter MeasureTheory
open scoped Classical
namespace BoundaryReduction.FiniteExponential

variable {α : Type} [Fintype α] [Nonempty α] {d : ℕ}
variable (p : FinProb α) (hp : ∀ y, 0 < p.w y) (Y : α → E d)

lemma nontrivial_alphabet (hd : 1 ≤ d)
    (hminimal : ∀ (a : E d) (b : ℝ), (∀ y, inner ℝ a (Y y) = b) → a = 0) : Nontrivial α := by
  rcases subsingleton_or_nontrivial α with hs | ht
  · letI := hs
    let i : Fin d := ⟨0,by omega⟩
    let a : E d := EuclideanSpace.single i 1
    let v : α := Classical.choice inferInstance
    have ha := hminimal a (inner ℝ a (Y v)) (fun y => by rw [Subsingleton.elim y v])
    have hh := congrArg (fun z : E d => z i) ha
    simpa [a,EuclideanSpace.single_apply] using hh
  · exact ht

/-- Restricting an admissible mean set to the actual mean image changes no finite mixtures. -/
lemma information_meanExterior (B : Set (E d)) :
    information p hp Y (Set.range (mean p hp Y) \ B) = information p hp Y Bᶜ := by
  unfold information
  congr 1
  ext x
  constructor
  · rintro ⟨F,rfl⟩
    exact ⟨⟨F.index,F.finite,F.weights,F.parameter,fun i => (F.admissible i).2⟩,rfl⟩
  · rintro ⟨F,rfl⟩
    exact ⟨⟨F.index,F.finite,F.weights,F.parameter,fun i => ⟨⟨F.parameter i,rfl⟩,F.admissible i⟩⟩,rfl⟩

/-- Proposition 3.2 with the original mean-space exterior and all Borel
boundary priors. Minimality is its concrete full-affine-span condition. -/
theorem proposition_3_2_full
    (hd : 1 ≤ d)
    (hminimal : ∀ (a : E d) (b : ℝ), (∀ y, inner ℝ a (Y y) = b) → a = 0)
    (hmean : (∑ y, p.w y • Y y) = 0)
    (B : Set (E d)) (h0 : (0 : E d) ∈ B)
    (hcontained : closure B ⊆ Set.range (mean p hp Y))
    (V : Finset α) (hV : V.Nonempty) (normal : V → E d)
    (hexpose : ∀ v : V, ∀ y, y ≠ (v : α) → inner ℝ (normal v) (Y y) < inner ℝ (normal v) (Y v))
    (g : α → ℝ) {L η : ℝ} (hL : 0 < L) (hη : 0 < η)
    (hg : ∀ y, |g y| ≤ L) (hpg : FinProb.expect p g = 0)
    (hsep : ∀ r : frontier B, η ≤ FinProb.expect
      (meanLaw p hp Y ⟨(r : E d),hcontained (frontier_subset_closure r.2)⟩) g) :
    information p hp Y (Set.range (mean p hp Y) \ B) ≤ -log (vertexMass p V) ∧
    η^2/(2*L^2) ≤ information p hp Y (frontier B) ∧
    (-log (vertexMass p V) < η^2/(2*L^2) →
      information p hp Y (Set.range (mean p hp Y) \ B) < information p hp Y (frontier B) ∧
      ∀ W : ProbabilityMeasure (frontier B),
        ¬ (∀ μ : Set.range (mean p hp Y), (μ : E d) ∉ B →
          FinProb.klPos (meanBoundaryMixture p hp Y hminimal B hcontained W) p ≤
            FinProb.expect (meanLaw p hp Y μ)
              (fun y => log ((meanBoundaryMixture p hp Y hminimal B hcontained W).w y/p.w y)))) := by
  letI : Nontrivial α := nontrivial_alphabet Y hd hminimal
  have hsep' : ∀ θ, mean p hp Y θ ∈ frontier B → η ≤ FinProb.expect (tilt p hp Y θ) g := by
    intro θ hθ
    have hh := hsep ⟨mean p hp Y θ,hθ⟩
    simpa only [meanLaw,naturalParameter_mean p hp Y hminimal] using hh
  have hcore := proposition_3_2 p hp Y V hV normal hexpose B h0 hmean hcontained g hL hη hg hpg hsep'
  rw [information_meanExterior]
  refine ⟨hcore.1,hcore.2.1,fun hgap => ⟨hcore.2.2 hgap,?_⟩⟩
  intro W
  exact proposition_3_2_mean_borel p hp Y hminimal B hcontained W V hV normal hexpose g hL hη hg hpg hsep' hgap

end BoundaryReduction.FiniteExponential
