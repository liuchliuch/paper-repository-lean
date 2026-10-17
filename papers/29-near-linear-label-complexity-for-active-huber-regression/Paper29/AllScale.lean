import Paper29.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.SimpRw

/-! The finite-range to all-scale extension, Lemma 3.8 of P29. -/
noncomputable section
open scoped BigOperators

namespace Paper29.AllScale

def phi {ι : Type*} [Fintype ι] (y : ι → ℝ) : ℝ := ∑ i, huber (y i)

lemma huber_nonneg (t : ℝ) : 0 ≤ huber t := by
  unfold huber
  split_ifs with ht
  · positivity
  · have := abs_nonneg t
    have : 1 < |t| := lt_of_not_ge ht
    linarith

lemma huber_eq_zero_iff (t : ℝ) : huber t = 0 ↔ t = 0 := by
  unfold huber
  split_ifs with ht
  · constructor
    · intro h
      apply sq_eq_zero_iff.mp
      linarith
    · rintro rfl
      norm_num
  · have : 1 < |t| := lt_of_not_ge ht
    constructor
    · intro h
      linarith
    · rintro rfl
      norm_num at ht

lemma quadratic_of_small_huber {t : ℝ} (ht : huber t ≤ 1 / 2) : |t| ≤ 1 := by
  by_contra h
  have hlarge : 1 < |t| := lt_of_not_ge h
  simp only [huber, if_neg h] at ht
  linarith

lemma huber_quadratic {t : ℝ} (ht : |t| ≤ 1) : huber t = t ^ 2 / 2 :=
  if_pos ht

lemma huber_scale_remainder (t β : ℝ) (hβ : 1 ≤ β) :
    0 ≤ huber (β * t) - β * huber t ∧
      huber (β * t) - β * huber t ≤ (β - 1) / 2 := by
  have hβ0 : 0 ≤ β := le_trans (by norm_num) hβ
  have ha : 0 ≤ |t| := abs_nonneg t
  have hs : t ^ 2 = |t| ^ 2 := (sq_abs t).symm
  simp only [huber, abs_mul, abs_of_nonneg hβ0]
  split_ifs with hbig hsmall hsmall
  · have hscl : (β * t) ^ 2 = β ^ 2 * |t| ^ 2 := by rw [mul_pow, hs]
    rw [hscl, hs]
    have hbta : β * |t| ^ 2 ≤ 1 := by
      nlinarith only [hbig,
        mul_nonneg (mul_nonneg hβ0 ha) (sub_nonneg.mpr hsmall)]
    constructor
    · nlinarith only [mul_nonneg (sub_nonneg.mpr hβ)
        (mul_nonneg hβ0 (sq_nonneg |t|))]
    · nlinarith only [mul_nonneg (sub_nonneg.mpr hβ) (sub_nonneg.mpr hbta)]
  · have : β * |t| > 1 := by
      nlinarith only [hsmall, mul_nonneg ha (sub_nonneg.mpr hβ)]
    nlinarith only [this, hbig]
  · rw [hs]
    have hscaled : 1 < β * |t| := lt_of_not_ge hbig
    have hsq : β * |t| ^ 2 ≤ β * |t| := by
      nlinarith only [mul_nonneg hβ0 (mul_nonneg ha (sub_nonneg.mpr hsmall))]
    constructor
    · nlinarith only [hscaled, hsq]
    · nlinarith only [mul_nonneg hβ0 (sq_nonneg (|t| - 1))]
  · constructor <;> nlinarith only [hβ]

lemma phi_nonneg {ι : Type*} [Fintype ι] (y : ι → ℝ) : 0 ≤ phi y :=
  Finset.sum_nonneg fun i _ => huber_nonneg (y i)

lemma huber_le_phi {ι : Type*} [Fintype ι] (y : ι → ℝ) (i : ι) :
    huber (y i) ≤ phi y := by
  exact Finset.single_le_sum (fun j _ => huber_nonneg (y j)) (Finset.mem_univ i)

lemma weighted_zero_of_phi_zero {ι : Type*} [Fintype ι] (y w : ι → ℝ)
    (hy : phi y = 0) : weightedHuber w y = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  have hi : huber (y i) = 0 := le_antisymm (by simpa [hy] using huber_le_phi y i)
    (huber_nonneg (y i))
  simp [hi]

lemma small_scale_exact {ι : Type*} [Fintype ι] (y w : ι → ℝ)
    (hpos : 0 < phi y) (hsmall : phi y < 1 / 2) :
    ∃ β : ℝ, 0 < β ∧
      phi (fun i => β * y i) = 1 / 2 ∧
      weightedHuber w (fun i => β * y i) = β ^ 2 * weightedHuber w y ∧
      β ^ 2 * phi y = 1 / 2 := by
  let β : ℝ := Real.sqrt ((1 / 2) / phi y)
  have hrat : 0 < (1 / 2 : ℝ) / phi y := div_pos (by norm_num) hpos
  have hbpos : 0 < β := Real.sqrt_pos.2 hrat
  have hbsq : β ^ 2 = (1 / 2) / phi y := Real.sq_sqrt hrat.le
  have hnorm : β ^ 2 * phi y = 1 / 2 := by
    rw [hbsq]
    field_simp [ne_of_gt hpos]
  have heach (i : ι) : huber (β * y i) = β ^ 2 * huber (y i) := by
    have hi : huber (y i) ≤ phi y := huber_le_phi y i
    have hy : |y i| ≤ 1 := quadratic_of_small_huber (hi.trans hsmall.le)
    have heq := huber_quadratic hy
    have hscaled : |β * y i| ≤ 1 := by
      have hmul := mul_le_mul_of_nonneg_left hi (sq_nonneg β)
      rw [heq, hnorm] at hmul
      have hs : (β * y i) ^ 2 ≤ 1 := by nlinarith
      exact (sq_le_one_iff_abs_le_one _).mp hs
    rw [huber_quadratic hscaled, heq]
    ring
  refine ⟨β, hbpos, ?_, ?_, hnorm⟩
  · unfold phi
    simp_rw [heach]
    rw [← Finset.mul_sum]
    exact hnorm
  · unfold weightedHuber
    simp_rw [heach]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring

lemma phi_scale_bounds {n : ℕ} (y : Fin n → ℝ) (β : ℝ) (hβ : 1 ≤ β) :
    β * phi y ≤ phi (fun i => β * y i) ∧
    phi (fun i => β * y i) ≤ β * phi y + (n : ℝ) / 2 * (β - 1) := by
  have hlo := Finset.sum_le_sum (s := Finset.univ)
    (fun i _ => (huber_scale_remainder (y i) β hβ).1)
  have hhi := Finset.sum_le_sum (s := Finset.univ)
    (fun i _ => (huber_scale_remainder (y i) β hβ).2)
  simp only [Finset.sum_const_zero, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hlo hhi
  constructor <;> unfold phi <;> linarith

lemma weighted_scale_bounds {n : ℕ} (y w : Fin n → ℝ) (β : ℝ) (hβ : 1 ≤ β)
    (hw : ∀ i, 0 ≤ w i) (hws : ∑ i, w i ≤ 2 * (n : ℝ)) :
    β * weightedHuber w y ≤ weightedHuber w (fun i => β * y i) ∧
    weightedHuber w (fun i => β * y i) ≤
      β * weightedHuber w y + (n : ℝ) * (β - 1) := by
  have hlo := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    mul_nonneg (hw i) (huber_scale_remainder (y i) β hβ).1)
  have hhi := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    mul_le_mul_of_nonneg_left (huber_scale_remainder (y i) β hβ).2 (hw i))
  have hsum : ∑ i, w i * (huber (β * y i) - β * huber (y i)) =
      weightedHuber w (fun i => β * y i) - β * weightedHuber w y := by
    simp only [mul_sub, Finset.sum_sub_distrib, weightedHuber, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hsum] at hlo hhi
  rw [Finset.sum_const_zero] at hlo
  rw [← Finset.sum_mul] at hhi
  have hmass := mul_le_mul_of_nonneg_right hws (show 0 ≤ (β - 1) / 2 by linarith)
  constructor <;> linarith

/-- Lemma 3.8 on a ray.  The hypothesis is required at every scalar multiple of
the original vector, so this statement also applies to any linear image. -/
theorem all_scale_on_ray {n : ℕ} (y w : Fin n → ℝ) (hn : 16 < n)
    (hw : ∀ i, 0 ≤ w i) (hws : ∑ i, w i ≤ 2 * (n : ℝ))
    (hrange : ∀ c : ℝ,
      1 / 2 ≤ phi (fun i => c * y i) →
      phi (fun i => c * y i) ≤ 8 * (n : ℝ) ^ 3 →
      |weightedHuber w (fun i => c * y i) - phi (fun i => c * y i)| ≤
        (1 / 16) * phi (fun i => c * y i)) :
    |weightedHuber w y - phi y| ≤ (1 / 8) * phi y := by
  have hnR : (16 : ℝ) < n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hnpos : (0 : ℝ) < n := by linarith
  have hS : 32 * (n : ℝ) ≤ 8 * (n : ℝ) ^ 3 := by
    have hsq : (n : ℝ) ^ 2 - 4 ≥ 0 := by nlinarith [sq_nonneg ((n : ℝ) - 2)]
    nlinarith only [mul_nonneg hn0 hsq]
  have hSpos : 0 < 8 * (n : ℝ) ^ 3 := by positivity
  have hP0 : 0 ≤ phi y := phi_nonneg y
  by_cases hzero : phi y = 0
  · rw [weighted_zero_of_phi_zero y w hzero, hzero]
    norm_num
  have hPpos : 0 < phi y := lt_of_le_of_ne hP0 (Ne.symm hzero)
  by_cases hsmall : phi y < 1 / 2
  · obtain ⟨β, hbpos, hpβ, hwβ, hnorm⟩ := small_scale_exact y w hPpos hsmall
    have hβrange := hrange β (by rw [hpβ]) (by rw [hpβ]; nlinarith)
    rw [hwβ, hpβ, ← hnorm] at hβrange
    have heq : β ^ 2 * weightedHuber w y - β ^ 2 * phi y =
        β ^ 2 * (weightedHuber w y - phi y) := by ring
    rw [heq, abs_mul, abs_of_nonneg (sq_nonneg β)] at hβrange
    have hbsq : 0 < β ^ 2 := sq_pos_of_pos hbpos
    have hrelative : |weightedHuber w y - phi y| ≤ (1 / 16) * phi y := by
      apply (mul_le_mul_iff_right₀ hbsq).mp
      nlinarith only [hβrange]
    linarith
  by_cases hlarge : 8 * (n : ℝ) ^ 3 < phi y
  · let β : ℝ := 2 * phi y / (8 * (n : ℝ) ^ 3)
    have hbS : β * (8 * (n : ℝ) ^ 3) = 2 * phi y := by
      dsimp [β]
      field_simp [ne_of_gt hSpos]
    have hbpos : 0 < β := div_pos (by positivity) hSpos
    have hb : 1 ≤ β := by
      dsimp [β]
      apply (le_div_iff₀ hSpos).2
      nlinarith only [hlarge, hSpos]
    let v : Fin n → ℝ := fun i => β⁻¹ * y i
    have hrestore : (fun i => β * v i) = y := by
      funext i
      dsimp [v]
      rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hbpos), one_mul]
    have hp := phi_scale_bounds v β hb
    have hg := weighted_scale_bounds v w β hb hw hws
    rw [hrestore] at hp hg
    have hvlow : 1 / 2 ≤ phi v := by
      by_contra hc
      have hc' : phi v < 1 / 2 := lt_of_not_ge hc
      have hprod := mul_lt_mul_of_pos_left hc' hbpos
      have hS1 : (n : ℝ) + 1 ≤ 8 * (n : ℝ) ^ 3 := by linarith
      have hprodS := mul_le_mul_of_nonneg_left hS1 hbpos.le
      nlinarith only [hprod, hprodS, hbS, hp.2, hn0]
    have hvhi : phi v ≤ 8 * (n : ℝ) ^ 3 := by
      have : phi v ≤ (8 * (n : ℝ) ^ 3) / 2 := by
        apply (mul_le_mul_iff_right₀ hbpos).mp
        nlinarith only [hp.1, hbS]
      linarith
    have hv := hrange β⁻¹ hvlow hvhi
    change |weightedHuber w v - phi v| ≤ (1 / 16) * phi v at hv
    obtain ⟨hvlo, hvhi'⟩ := abs_le.mp hv
    have hlo := mul_le_mul_of_nonneg_left hvlo hbpos.le
    have hhi := mul_le_mul_of_nonneg_left hvhi' hbpos.le
    have hrem : (n : ℝ) * (β - 1) ≤ (1 / 16) * phi y := by
      have hprod := mul_le_mul_of_nonneg_left hS hbpos.le
      nlinarith only [hprod, hbS, hn0]
    apply abs_le.mpr
    constructor <;> nlinarith only [hlo, hhi, hrem, hp.1, hp.2, hg.1, hg.2,
      mul_nonneg hn0 (sub_nonneg.mpr hb)]
  · have hmid := hrange 1 (by simpa using le_of_not_gt hsmall)
      (by simpa using le_of_not_gt hlarge)
    simp only [one_mul] at hmid
    linarith

/-- The Huber all-scale extension in the original matrix formulation.  The
finite-range premise is uniform in `h`; no all-scale estimate is assumed. -/
theorem huber_all_scale_extension {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (w : Fin n → ℝ) (hn : 16 < n) (hw : ∀ i, 0 ≤ w i)
    (hws : ∑ i, w i ≤ 2 * (n : ℝ))
    (hrange : ∀ h : Fin d → ℝ,
      1 / 2 ≤ unshifted A h → unshifted A h ≤ 8 * (n : ℝ) ^ 3 →
      |weightedHuber w (A.mulVec h) - unshifted A h| ≤
        (1 / 16) * unshifted A h) :
    ∀ h : Fin d → ℝ,
      |weightedHuber w (A.mulVec h) - unshifted A h| ≤
        (1 / 8) * unshifted A h := by
  intro h
  apply all_scale_on_ray (A.mulVec h) w hn hw hws
  intro c hlo hhi
  have hscale : A.mulVec (c • h) = fun i => c * (A.mulVec h) i := by
    simpa using Matrix.mulVec_smul A c h
  have hfit := hrange (c • h)
  unfold unshifted at hfit
  rw [hscale] at hfit
  exact hfit hlo hhi

end Paper29.AllScale
