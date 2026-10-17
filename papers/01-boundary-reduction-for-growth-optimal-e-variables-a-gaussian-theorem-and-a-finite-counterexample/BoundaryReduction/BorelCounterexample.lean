import BoundaryReduction.Information
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

open Real Set BigOperators MeasureTheory
open scoped Classical
namespace BoundaryReduction.NinePoint

lemma pt_le_one (θ : ℝ × ℝ) (y : Fin 9) : pt θ y ≤ 1 := by
  have h := Finset.single_le_sum (fun z (_ : z ∈ Finset.univ) => (pt_pos θ z).le)
    (Finset.mem_univ y)
  simpa [pt_sum] using h

variable (W : Measure (ℝ × ℝ)) [IsProbabilityMeasure W]

lemma integrable_pt (y : Fin 9) : Integrable (fun θ => pt θ y) W :=
  Integrable.of_bound (continuous_pt y).aestronglyMeasurable 1
    (Filter.Eventually.of_forall (fun θ => by
      rw [Real.norm_eq_abs, abs_of_pos (pt_pos θ y)]
      exact pt_le_one θ y))

/-- Actual Borel mixing of the nine masses over natural parameters. -/
noncomputable def borelProb : FinProb (Fin 9) where
  w := fun y => ∫ θ, pt θ y ∂W
  nonneg := fun y => integral_nonneg (fun θ => (pt_pos θ y).le)
  sum_eq_one := by
    rw [← integral_finset_sum _ (fun y _ => integrable_pt W y)]
    simp [pt_sum]

lemma borelProb_pos (y : Fin 9) : 0 < (borelProb W).w y := by
  change 0 < ∫ θ, pt θ y ∂W
  rw [integral_pos_iff_support_of_nonneg (fun θ => (pt_pos θ y).le) (integrable_pt W y)]
  have hs : Function.support (fun θ => pt θ y) = Set.univ := by
    ext θ
    simp [(pt_pos θ y).ne']
  simp [hs]

lemma borel_expect_eq (g : Fin 9 → ℝ) :
    FinProb.expect (borelProb W) g = ∫ θ, FinProb.expect (tiltProb θ) g ∂W := by
  simp only [FinProb.expect, borelProb, tiltProb]
  rw [integral_finset_sum _ (fun y _ => (integrable_pt W y).mul_const (g y))]
  apply Finset.sum_congr rfl
  intro y _
  rw [integral_mul_const]

lemma borel_separator_lower
    (hW : ∀ᵐ θ ∂W, ‖esMean (pt θ)‖ = r₀) :
    η ≤ FinProb.expect (borelProb W) separator := by
  rw [borel_expect_eq]
  have hi : Integrable (fun θ => FinProb.expect (tiltProb θ) separator) W :=
    integrable_finset_sum _ (fun y _ => (integrable_pt W y).mul_const (separator y))
  have h := integral_mono_ae (integrable_const η) hi
    (hW.mono (fun θ hθ => separator_boundary hθ))
  simpa using h

/-- The separator bound holds for every Borel boundary mixture. -/
theorem borel_boundary_kl_lower
    (hW : ∀ᵐ θ ∂W, ‖esMean (pt θ)‖ = r₀) :
    (7:ℝ)*10^(-12:ℤ) < FinProb.klPos (borelProb W) baseProb := by
  have h := FinProb.separator_kl_lower (borelProb W) baseProb (borelProb_pos W) p0_pos
    (by norm_num : (0:ℝ)<1) η_pos.le separator_bounded separator_base
    (borel_separator_lower W hW)
  exact η_numeric.trans_le (by simpa using h)

/-- No Borel boundary prior can satisfy the global expected-log inequality (2.7). -/
theorem no_borel_boundary_global
    (hW : ∀ᵐ θ ∂W, ‖esMean (pt θ)‖ = r₀) :
    ¬ (∀ θ : ℝ × ℝ, r₀ ≤ ‖esMean (pt θ)‖ →
      FinProb.klPos (borelProb W) baseProb ≤
        FinProb.expect (tiltProb θ) (fun y => log ((borelProb W).w y / p0 y))) := by
  intro hglobal
  have hl := borel_boundary_kl_lower W hW
  have hmean := exteriorPrior.expect_lower
    (fun y => log ((borelProb W).w y / p0 y))
    (FinProb.klPos (borelProb W) baseProb) hglobal
  rw [exteriorPrior_prob] at hmean
  have hc := FinProb.klPos_chain_rule (p := mixtureProb 200)
    (q := borelProb W) (r := baseProb) (borelProb_pos W) p0_pos
  have hn := FinProb.klPos_nonneg (p := mixtureProb 200) (borelProb_pos W)
  have hu := kl_Q200_lt
  have hnum : (1.001:ℝ)*10^(-15:ℤ) < (7:ℝ)*10^(-12:ℤ) := by norm_num
  change FinProb.klPos (mixtureProb 200) baseProb =
    FinProb.klPos (mixtureProb 200) (borelProb W) +
      FinProb.expect (mixtureProb 200) (fun y => log ((borelProb W).w y / p0 y)) at hc
  have hupper : FinProb.klPos (borelProb W) baseProb ≤
      FinProb.klPos (mixtureProb 200) baseProb := by
    calc
      _ ≤ FinProb.expect (mixtureProb 200) (fun y => log ((borelProb W).w y / p0 y)) := hmean
      _ ≤ FinProb.klPos (mixtureProb 200) (borelProb W) +
          FinProb.expect (mixtureProb 200) (fun y => log ((borelProb W).w y / p0 y)) :=
        le_add_of_nonneg_left hn
      _ = _ := hc.symm
  exact (not_lt_of_ge hupper) (hu.trans (hnum.trans hl))

/-- Theorem 3.1, both the finite information separation and the Borel obstruction. -/
theorem theorem_3_1 :
    (0 < information exterior ∧ information exterior < 2*10^(-15:ℤ) ∧
      (7:ℝ)*10^(-12:ℤ) < information boundary) ∧
    (∀ (W : Measure (ℝ × ℝ)) [IsProbabilityMeasure W],
      (∀ᵐ θ ∂W, ‖esMean (pt θ)‖ = r₀) →
      ¬ (∀ θ : ℝ × ℝ, r₀ ≤ ‖esMean (pt θ)‖ →
        FinProb.klPos (borelProb W) baseProb ≤
          FinProb.expect (tiltProb θ) (fun y => log ((borelProb W).w y / p0 y)))) := by
  refine ⟨theorem_3_1_information, ?_⟩
  intro W hW hsupport
  exact no_borel_boundary_global W hsupport

end BoundaryReduction.NinePoint
