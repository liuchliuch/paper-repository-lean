import BoundaryReduction.ExposedBorel
import Mathlib.MeasureTheory.Constructions.Polish.Basic

open Real Set BigOperators Filter MeasureTheory
open scoped Classical
namespace BoundaryReduction.FiniteExponential

variable {α : Type} [Fintype α] [Nonempty α] {d : ℕ}
variable (p : FinProb α) (hp : ∀ y, 0 < p.w y) (Y : α → E d)

lemma log_tilt_ratio (θ ϑ : E d) (y : α) :
    log ((tilt p hp Y θ).w y/(tilt p hp Y ϑ).w y) =
      inner ℝ (θ-ϑ) (Y y)+log (partition p Y ϑ)-log (partition p Y θ) := by
  rw [log_div (tilt_pos p hp Y θ y).ne' (tilt_pos p hp Y ϑ y).ne']
  change log (p.w y*exp (inner ℝ θ (Y y))/partition p Y θ)-
    log (p.w y*exp (inner ℝ ϑ (Y y))/partition p Y ϑ) = _
  rw [log_div (mul_pos (hp y) (exp_pos _)).ne' (partition_pos p hp Y θ).ne',
    log_div (mul_pos (hp y) (exp_pos _)).ne' (partition_pos p hp Y ϑ).ne',
    log_mul (hp y).ne' (exp_pos _).ne',log_mul (hp y).ne' (exp_pos _).ne',
    log_exp,log_exp,inner_sub_left]
  ring

lemma kl_tilts (θ ϑ : E d) : FinProb.klPos (tilt p hp Y θ) (tilt p hp Y ϑ) =
    inner ℝ (θ-ϑ) (mean p hp Y θ)+log (partition p Y ϑ)-log (partition p Y θ) := by
  simp only [FinProb.klPos,log_tilt_ratio]
  simp_rw [mul_sub,mul_add]
  rw [Finset.sum_sub_distrib,Finset.sum_add_distrib,← Finset.sum_mul,← Finset.sum_mul,
    (tilt p hp Y θ).sum_eq_one,one_mul,one_mul]
  congr 2
  simp [mean,inner_sum,real_inner_smul_right]

lemma weights_eq_of_kl_zero (q r : FinProb α) (hq : ∀ y, 0 < q.w y)
    (hr : ∀ y, 0 < r.w y) (hkl : FinProb.klPos q r = 0) : q.w = r.w := by
  have hpin := FinProb.pinsker q r hq hr
  rw [hkl] at hpin
  have ht : FinProb.tv q r = 0 := by nlinarith [sq_nonneg (FinProb.tv q r)]
  have hs : (∑ y, |q.w y-r.w y|) = 0 := by unfold FinProb.tv at ht; linarith
  ext y
  have hh := Finset.single_le_sum (fun i (_ : i ∈ Finset.univ) => abs_nonneg (q.w i-r.w i))
    (Finset.mem_univ y)
  rw [hs] at hh
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hh (abs_nonneg _)))

variable (hminimal : ∀ (a : E d) (b : ℝ), (∀ y, inner ℝ a (Y y) = b) → a = 0)
include hminimal

/-- For a minimal finite NEF, its actual mean map is injective. -/
theorem mean_injective : Function.Injective (mean p hp Y) := by
  intro θ ϑ hm
  have hk := kl_tilts p hp Y θ ϑ
  have hl := kl_tilts p hp Y ϑ θ
  have hv : ϑ-θ = -(θ-ϑ) := by abel
  rw [hv,inner_neg_left,← hm] at hl
  have hn1 := FinProb.klPos_nonneg (p := tilt p hp Y θ) (tilt_pos p hp Y ϑ)
  have hn2 := FinProb.klPos_nonneg (p := tilt p hp Y ϑ) (tilt_pos p hp Y θ)
  have hz : FinProb.klPos (tilt p hp Y θ) (tilt p hp Y ϑ) = 0 := by linarith
  have heq := weights_eq_of_kl_zero (tilt p hp Y θ) (tilt p hp Y ϑ)
    (tilt_pos p hp Y θ) (tilt_pos p hp Y ϑ) hz
  have hconstraint (y : α) : inner ℝ (θ-ϑ) (Y y) = log (partition p Y θ)-log (partition p Y ϑ) := by
    have hh := log_tilt_ratio p hp Y θ ϑ y
    rw [congrFun heq y,div_self (tilt_pos p hp Y ϑ y).ne',log_one] at hh
    linarith
  exact sub_eq_zero.mp (hminimal _ _ hconstraint)

/-- Lusin–Souslin gives a Borel inverse on the actual mean image. -/
theorem mean_measurableEmbedding : MeasurableEmbedding (mean p hp Y) :=
  (continuous_mean p hp Y).measurableEmbedding (mean_injective p hp Y hminimal)

noncomputable def naturalParameter (μ : Set.range (mean p hp Y)) : E d :=
  Set.rangeSplitting (mean p hp Y) μ

lemma mean_naturalParameter (μ : Set.range (mean p hp Y)) : mean p hp Y (naturalParameter p hp Y μ) = (μ : E d) :=
  Set.apply_rangeSplitting _ μ

lemma naturalParameter_mean (θ : E d) : naturalParameter p hp Y ⟨mean p hp Y θ,⟨θ,rfl⟩⟩ = θ :=
  mean_injective p hp Y hminimal (mean_naturalParameter p hp Y hminimal _)

lemma measurable_naturalParameter : Measurable (naturalParameter p hp Y) :=
  (mean_measurableEmbedding p hp Y hminimal).measurable_rangeSplitting

noncomputable def meanLaw (μ : Set.range (mean p hp Y)) : FinProb α :=
  tilt p hp Y (naturalParameter p hp Y μ)

end BoundaryReduction.FiniteExponential
