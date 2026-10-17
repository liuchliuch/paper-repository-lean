import BoundaryReduction.BorelCounterexample
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

open Real Set BigOperators MeasureTheory
open scoped Classical
namespace BoundaryReduction.NinePoint

lemma log_pt_ratio (θ ϑ : ℝ × ℝ) (y : Fin 9) :
    log (pt θ y/pt ϑ y) = dot θ (coord y)-dot ϑ (coord y)+log (Z ϑ)-log (Z θ) := by
  rw [log_div (pt_pos _ _).ne' (pt_pos _ _).ne',pt_eq,pt_eq,
    log_div (mul_pos (exp_pos _) (p0_pos _)).ne' (Z_pos _).ne',
    log_div (mul_pos (exp_pos _) (p0_pos _)).ne' (Z_pos _).ne',
    log_mul (exp_pos _).ne' (p0_pos _).ne',log_mul (exp_pos _).ne' (p0_pos _).ne',
    log_exp,log_exp]
  ring

lemma kl_tilts (θ ϑ : ℝ × ℝ) :
    FinProb.klPos (tiltProb θ) (tiltProb ϑ) =
      inner ℝ (toES (θ-ϑ)) (esMean (pt θ))+log (Z ϑ)-log (Z θ) := by
  simp only [FinProb.klPos,tiltProb,log_pt_ratio]
  have heq (y : Fin 9) :
      pt θ y*(dot θ (coord y)-dot ϑ (coord y)+log (Z ϑ)-log (Z θ)) =
      pt θ y*dot (θ-ϑ) (coord y)+pt θ y*(log (Z ϑ)-log (Z θ)) := by
    simp [dot]
    ring
  simp_rw [heq]
  rw [Finset.sum_add_distrib,← Finset.sum_mul,pt_sum,one_mul]
  have hi : inner ℝ (toES (θ-ϑ)) (esMean (pt θ)) =
      ∑ y, pt θ y*dot (θ-ϑ) (coord y) := by
    simp only [esMean,inner_sum,real_inner_smul_right,inner_toES]
  rw [hi]
  ring

lemma mass_eq_of_kl_zero {p q : FinProb (Fin 9)} (hp : ∀ y, 0 < p.w y)
    (hq : ∀ y, 0 < q.w y) (hkl : FinProb.klPos p q = 0) : p.w = q.w := by
  have hpin := FinProb.pinsker p q hp hq
  rw [hkl] at hpin
  have htv : FinProb.tv p q = 0 := by nlinarith [sq_nonneg (FinProb.tv p q)]
  have hsum : (∑ y, |p.w y-q.w y|) = 0 := by unfold FinProb.tv at htv; linarith
  ext y
  have hle := Finset.single_le_sum (fun i (_ : i ∈ Finset.univ) => abs_nonneg (p.w i-q.w i))
    (Finset.mem_univ y)
  rw [hsum] at hle
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hle (abs_nonneg _)))

/-- Minimality: equality of all tilted masses identifies both natural coordinates. -/
lemma pt_injective : Function.Injective pt := by
  intro θ ϑ h
  have h0 := congrFun h (0 : Fin 9)
  have h1 := congrFun h (1 : Fin 9)
  have h3 := congrFun h (3 : Fin 9)
  norm_num [pt,un,dot,coord,p0] at h0 h1 h3
  have hz : Z θ = Z ϑ := by
    have he : ε*(Z ϑ-Z θ) = 0 := by
      field_simp [(Z_pos θ).ne',(Z_pos ϑ).ne'] at h0
      nlinarith
    exact (sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left ε_pos.ne')).symm
  have he1 : exp θ.1 = exp ϑ.1 := by
    rw [hz] at h1
    exact (mul_left_inj' w_pos.ne').mp ((div_left_inj' (Z_pos ϑ).ne').mp h1)
  have he3 : exp θ.2 = exp ϑ.2 := by
    rw [hz] at h3
    exact (mul_left_inj' w_pos.ne').mp ((div_left_inj' (Z_pos ϑ).ne').mp h3)
  exact Prod.ext (exp_injective he1) (exp_injective he3)

/-- The actual mean map is one-to-one; no inverse-map assumption is used. -/
theorem mean_injective : Function.Injective (fun θ : ℝ × ℝ => esMean (pt θ)) := by
  intro θ ϑ hmean
  change esMean (pt θ) = esMean (pt ϑ) at hmean
  have hk := kl_tilts θ ϑ
  have hl := kl_tilts ϑ θ
  have hv : toES (ϑ-θ) = -toES (θ-ϑ) := by
    ext i
    fin_cases i <;> simp [toES] <;> ring
  rw [hv,inner_neg_left,← hmean] at hl
  have hsum : FinProb.klPos (tiltProb θ) (tiltProb ϑ)+FinProb.klPos (tiltProb ϑ) (tiltProb θ) = 0 := by
    linarith
  have hn1 := FinProb.klPos_nonneg (p := tiltProb θ) (q := tiltProb ϑ) (pt_pos ϑ)
  have hn2 := FinProb.klPos_nonneg (p := tiltProb ϑ) (q := tiltProb θ) (pt_pos θ)
  have hz : FinProb.klPos (tiltProb θ) (tiltProb ϑ) = 0 := by linarith
  exact pt_injective (mass_eq_of_kl_zero (pt_pos θ) (pt_pos ϑ) hz)

/-- Lusin–Souslin supplies the measurable inverse on the actual mean image. -/
theorem mean_measurableEmbedding : MeasurableEmbedding (fun θ : ℝ × ℝ => esMean (pt θ)) :=
  continuous_mean.measurableEmbedding mean_injective

end BoundaryReduction.NinePoint
