import BoundaryReduction.ExposedSeparator

open Real Set BigOperators Filter MeasureTheory
open scoped Classical
namespace BoundaryReduction.FiniteExponential

variable {α : Type} [Fintype α] [Nonempty α] {d : ℕ}
variable (p : FinProb α) (hp : ∀ y, 0 < p.w y) (Y : α → E d)

lemma tilt_le_one (θ : E d) (y : α) : (tilt p hp Y θ).w y ≤ 1 := by
  have h := Finset.single_le_sum (fun z (_ : z ∈ Finset.univ) => (tilt_pos p hp Y θ z).le)
    (Finset.mem_univ y)
  simpa only [(tilt p hp Y θ).sum_eq_one] using h

variable (W : Measure (E d)) [IsProbabilityMeasure W]

lemma integrable_tilt (y : α) : Integrable (fun θ : E d => (tilt p hp Y θ).w y) W :=
  Integrable.of_bound (continuous_tilt p hp Y y).aestronglyMeasurable 1
    (Eventually.of_forall (fun θ => by
      rw [Real.norm_eq_abs,abs_of_pos (tilt_pos p hp Y θ y)]
      exact tilt_le_one p hp Y θ y))

noncomputable def borelProb : FinProb α where
  w := fun y => ∫ θ, (tilt p hp Y θ).w y ∂W
  nonneg := fun y => integral_nonneg (fun θ => (tilt_pos p hp Y θ y).le)
  sum_eq_one := by
    rw [← integral_finset_sum _ (fun y _ => integrable_tilt p hp Y W y)]
    simp only [(tilt p hp Y _).sum_eq_one]
    simp

lemma borelProb_pos (y : α) : 0 < (borelProb p hp Y W).w y := by
  change 0 < ∫ θ, (tilt p hp Y θ).w y ∂W
  rw [integral_pos_iff_support_of_nonneg (fun θ => (tilt_pos p hp Y θ y).le) (integrable_tilt p hp Y W y)]
  have hs : Function.support (fun θ : E d => (tilt p hp Y θ).w y) = Set.univ := by
    ext θ
    simp [(tilt_pos p hp Y θ y).ne']
  simp [hs]

lemma borel_expect_eq (g : α → ℝ) : FinProb.expect (borelProb p hp Y W) g =
    ∫ θ, FinProb.expect (tilt p hp Y θ) g ∂W := by
  simp only [FinProb.expect,borelProb]
  rw [integral_finset_sum _ (fun y _ => (integrable_tilt p hp Y W y).mul_const (g y))]
  simp only [integral_mul_const]

lemma integrable_tilt_expect (g : α → ℝ) : Integrable (fun θ => FinProb.expect (tilt p hp Y θ) g) W :=
  integrable_finset_sum _ (fun y _ => (integrable_tilt p hp Y W y).mul_const (g y))

/-- Every countably additive Borel boundary mixture inherits the separator. -/
lemma borel_separator_lower (B : Set (E d)) (hW : ∀ᵐ θ ∂W, mean p hp Y θ ∈ frontier B)
    (g : α → ℝ) {η : ℝ}
    (hsep : ∀ θ, mean p hp Y θ ∈ frontier B → η ≤ FinProb.expect (tilt p hp Y θ) g) :
    η ≤ FinProb.expect (borelProb p hp Y W) g := by
  rw [borel_expect_eq]
  have hh := integral_mono_ae (integrable_const η) (integrable_tilt_expect p hp Y W g)
    (hW.mono (fun θ hθ => hsep θ hθ))
  simpa using hh

/-- Proposition 3.2 excludes the global inequality for all Borel boundary priors. -/
theorem proposition_3_2_borel [Nontrivial α]
    (V : Finset α) (hV : V.Nonempty) (normal : V → E d)
    (hexpose : ∀ v : V, ∀ y, y ≠ (v : α) → inner ℝ (normal v) (Y y) < inner ℝ (normal v) (Y v))
    (B : Set (E d)) (hcontained : closure B ⊆ Set.range (mean p hp Y))
    (hW : ∀ᵐ θ ∂W, mean p hp Y θ ∈ frontier B)
    (g : α → ℝ) {L η : ℝ} (hL : 0 < L) (hη : 0 < η)
    (hg : ∀ y, |g y| ≤ L) (hpg : FinProb.expect p g = 0)
    (hsep : ∀ θ, mean p hp Y θ ∈ frontier B → η ≤ FinProb.expect (tilt p hp Y θ) g)
    (hgap : -log (vertexMass p V) < η^2/(2*L^2)) :
    ¬ (∀ θ, mean p hp Y θ ∉ B → FinProb.klPos (borelProb p hp Y W) p ≤
      FinProb.expect (tilt p hp Y θ) (fun y => log ((borelProb p hp Y W).w y/p.w y))) := by
  apply no_global_of_separator p hp Y V hV normal hexpose B
    (fun v hv => exposed_vertex_not_mean p hp Y v (normal v) (hexpose v) (hcontained hv))
    g hL hη.le hg hpg hgap (borelProb p hp Y W) (borelProb_pos p hp Y W)
  exact borel_separator_lower p hp Y W B hW g hsep

end BoundaryReduction.FiniteExponential
