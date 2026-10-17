import Paper10.Gaussian

/-! Six-coordinate Wick formula. The finite equality-pattern case split is proved by
Lean's kernel, using actual Gaussian integrals; no native evaluator or custom axiom is used. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace Paper10
set_option maxRecDepth 4096
set_option maxHeartbeats 0

def mult6 {m : ℕ} (a b c d e f i : Fin m) : ℕ :=
  (if i = a then 1 else 0) + (if i = b then 1 else 0) +
  (if i = c then 1 else 0) + (if i = d then 1 else 0) +
  (if i = e then 1 else 0) + (if i = f then 1 else 0)

theorem prod6_as_powers {m : ℕ} (a b c d e f : Fin m) (ω : Fin m → ℝ) :
    ω a * ω b * ω c * ω d * ω e * ω f = ∏ i, ω i ^ mult6 a b c d e f i := by
  classical
  simp only [mult6, pow_add, Finset.prod_mul_distrib, prod_single_indicator]

theorem integrable_wick_six {m : ℕ} (a b c d e f : Fin m) :
    Integrable (fun ω : Fin m → ℝ => ω a * ω b * ω c * ω d * ω e * ω f)
      (stdGaussianMeasure m) := by
  simpa only [prod6_as_powers] using integrable_gaussian_monomial (mult6 a b c d e f)

def delta {m : ℕ} (a b : Fin m) : ℝ := if a = b then 1 else 0

theorem wick_six {m : ℕ} (a b c d e f : Fin m) :
    (∫ ω : Fin m → ℝ, ω a * ω b * ω c * ω d * ω e * ω f ∂stdGaussianMeasure m) =
        delta a b * delta c d * delta e f
        + delta a b * delta c e * delta d f
        + delta a b * delta c f * delta d e
        + delta a c * delta b d * delta e f
        + delta a c * delta b e * delta d f
        + delta a c * delta b f * delta d e
        + delta a d * delta b c * delta e f
        + delta a d * delta b e * delta c f
        + delta a d * delta b f * delta c e
        + delta a e * delta b c * delta d f
        + delta a e * delta b d * delta c f
        + delta a e * delta b f * delta c d
        + delta a f * delta b c * delta d e
        + delta a f * delta b d * delta c e
        + delta a f * delta b e * delta c d := by
  classical
  simp_rw [prod6_as_powers]
  rw [integral_prod_powers]
  by_cases hba : b = a
  · subst b
    by_cases hca : c = a
    · subst c
      by_cases hda : d = a
      · subst d
        by_cases hea : e = a
        · subst e
          by_cases hfa : f = a
          · subst f
            have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a a a a a a i ∂gaussianReal 0 1) = 15 := by
              rw [Finset.prod_eq_single a]
              · have he : mult6 a a a a a a a = 6 := by simp_all [mult6, eq_comm]
                rw [he, gauss_int_pow_mgfPoly]
                norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
              · intro i _ hi
                all_goals simp_all [mult6, eq_comm, gauss_int_pow_mgfPoly, gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
              · intro hh
                exact False.elim (hh (Finset.mem_univ a))
            rw [hv]
            norm_num [delta, *]
          · have haf : a ≠ f := Ne.symm hfa
            have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a a a a a f i ∂gaussianReal 0 1) = 0 := by
              apply Finset.prod_eq_zero (Finset.mem_univ a)
              have he : mult6 a a a a a f a = 5 := by simp_all [mult6, eq_comm]
              rw [he, gauss_int_pow_mgfPoly]
              norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
            rw [hv]
            norm_num [delta, *]
        · have hae : a ≠ e := Ne.symm hea
          by_cases hfa : f = a
          · subst f
            have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a a a a e a i ∂gaussianReal 0 1) = 0 := by
              apply Finset.prod_eq_zero (Finset.mem_univ a)
              have he : mult6 a a a a e a a = 5 := by simp_all [mult6, eq_comm]
              rw [he, gauss_int_pow_mgfPoly]
              norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
            rw [hv]
            norm_num [delta, *]
          · have haf : a ≠ f := Ne.symm hfa
            by_cases hfe : f = e
            · subst f
              have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a a a a e e i ∂gaussianReal 0 1) = 3 := by
                rw [Finset.prod_eq_single a]
                · have he : mult6 a a a a e e a = 4 := by simp_all [mult6, eq_comm]
                  rw [he, gauss_int_pow_mgfPoly]
                  norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                · intro i _ hi
                  by_cases hie : i = e
                  all_goals simp_all [mult6, eq_comm, gauss_int_pow_mgfPoly, gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                · intro hh
                  exact False.elim (hh (Finset.mem_univ a))
              rw [hv]
              norm_num [delta, *]
            · have hef : e ≠ f := Ne.symm hfe
              have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a a a a e f i ∂gaussianReal 0 1) = 0 := by
                apply Finset.prod_eq_zero (Finset.mem_univ e)
                have he : mult6 a a a a e f e = 1 := by simp_all [mult6, eq_comm]
                rw [he, gauss_int_pow_mgfPoly]
                norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
              rw [hv]
              norm_num [delta, *]
      · have had : a ≠ d := Ne.symm hda
        by_cases hea : e = a
        · subst e
          by_cases hfa : f = a
          · subst f
            have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a a a d a a i ∂gaussianReal 0 1) = 0 := by
              apply Finset.prod_eq_zero (Finset.mem_univ a)
              have he : mult6 a a a d a a a = 5 := by simp_all [mult6, eq_comm]
              rw [he, gauss_int_pow_mgfPoly]
              norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
            rw [hv]
            norm_num [delta, *]
          · have haf : a ≠ f := Ne.symm hfa
            by_cases hfd : f = d
            · subst f
              have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a a a d a d i ∂gaussianReal 0 1) = 3 := by
                rw [Finset.prod_eq_single a]
                · have he : mult6 a a a d a d a = 4 := by simp_all [mult6, eq_comm]
                  rw [he, gauss_int_pow_mgfPoly]
                  norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                · intro i _ hi
                  by_cases hid : i = d
                  all_goals simp_all [mult6, eq_comm, gauss_int_pow_mgfPoly, gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                · intro hh
                  exact False.elim (hh (Finset.mem_univ a))
              rw [hv]
              norm_num [delta, *]
            · have hdf : d ≠ f := Ne.symm hfd
              have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a a a d a f i ∂gaussianReal 0 1) = 0 := by
                apply Finset.prod_eq_zero (Finset.mem_univ d)
                have he : mult6 a a a d a f d = 1 := by simp_all [mult6, eq_comm]
                rw [he, gauss_int_pow_mgfPoly]
                norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
              rw [hv]
              norm_num [delta, *]
        · have hae : a ≠ e := Ne.symm hea
          by_cases hed : e = d
          · subst e
            by_cases hfa : f = a
            · subst f
              have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a a a d d a i ∂gaussianReal 0 1) = 3 := by
                rw [Finset.prod_eq_single a]
                · have he : mult6 a a a d d a a = 4 := by simp_all [mult6, eq_comm]
                  rw [he, gauss_int_pow_mgfPoly]
                  norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                · intro i _ hi
                  by_cases hid : i = d
                  all_goals simp_all [mult6, eq_comm, gauss_int_pow_mgfPoly, gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                · intro hh
                  exact False.elim (hh (Finset.mem_univ a))
              rw [hv]
              norm_num [delta, *]
            · have haf : a ≠ f := Ne.symm hfa
              by_cases hfd : f = d
              · subst f
                have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a a a d d d i ∂gaussianReal 0 1) = 0 := by
                  apply Finset.prod_eq_zero (Finset.mem_univ a)
                  have he : mult6 a a a d d d a = 3 := by simp_all [mult6, eq_comm]
                  rw [he, gauss_int_pow_mgfPoly]
                  norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                rw [hv]
                norm_num [delta, *]
              · have hdf : d ≠ f := Ne.symm hfd
                have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a a a d d f i ∂gaussianReal 0 1) = 0 := by
                  apply Finset.prod_eq_zero (Finset.mem_univ a)
                  have he : mult6 a a a d d f a = 3 := by simp_all [mult6, eq_comm]
                  rw [he, gauss_int_pow_mgfPoly]
                  norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                rw [hv]
                norm_num [delta, *]
          · have hde : d ≠ e := Ne.symm hed
            by_cases hfa : f = a
            · subst f
              have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a a a d e a i ∂gaussianReal 0 1) = 0 := by
                apply Finset.prod_eq_zero (Finset.mem_univ d)
                have he : mult6 a a a d e a d = 1 := by simp_all [mult6, eq_comm]
                rw [he, gauss_int_pow_mgfPoly]
                norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
              rw [hv]
              norm_num [delta, *]
            · have haf : a ≠ f := Ne.symm hfa
              by_cases hfd : f = d
              · subst f
                have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a a a d e d i ∂gaussianReal 0 1) = 0 := by
                  apply Finset.prod_eq_zero (Finset.mem_univ a)
                  have he : mult6 a a a d e d a = 3 := by simp_all [mult6, eq_comm]
                  rw [he, gauss_int_pow_mgfPoly]
                  norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                rw [hv]
                norm_num [delta, *]
              · have hdf : d ≠ f := Ne.symm hfd
                by_cases hfe : f = e
                · subst f
                  have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a a a d e e i ∂gaussianReal 0 1) = 0 := by
                    apply Finset.prod_eq_zero (Finset.mem_univ a)
                    have he : mult6 a a a d e e a = 3 := by simp_all [mult6, eq_comm]
                    rw [he, gauss_int_pow_mgfPoly]
                    norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                  rw [hv]
                  norm_num [delta, *]
                · have hef : e ≠ f := Ne.symm hfe
                  have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a a a d e f i ∂gaussianReal 0 1) = 0 := by
                    apply Finset.prod_eq_zero (Finset.mem_univ a)
                    have he : mult6 a a a d e f a = 3 := by simp_all [mult6, eq_comm]
                    rw [he, gauss_int_pow_mgfPoly]
                    norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                  rw [hv]
                  norm_num [delta, *]
    · have hac : a ≠ c := Ne.symm hca
      by_cases hda : d = a
      · subst d
        by_cases hea : e = a
        · subst e
          by_cases hfa : f = a
          · subst f
            have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a a c a a a i ∂gaussianReal 0 1) = 0 := by
              apply Finset.prod_eq_zero (Finset.mem_univ a)
              have he : mult6 a a c a a a a = 5 := by simp_all [mult6, eq_comm]
              rw [he, gauss_int_pow_mgfPoly]
              norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
            rw [hv]
            norm_num [delta, *]
          · have haf : a ≠ f := Ne.symm hfa
            by_cases hfc : f = c
            · subst f
              have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a a c a a c i ∂gaussianReal 0 1) = 3 := by
                rw [Finset.prod_eq_single a]
                · have he : mult6 a a c a a c a = 4 := by simp_all [mult6, eq_comm]
                  rw [he, gauss_int_pow_mgfPoly]
                  norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                · intro i _ hi
                  by_cases hic : i = c
                  all_goals simp_all [mult6, eq_comm, gauss_int_pow_mgfPoly, gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                · intro hh
                  exact False.elim (hh (Finset.mem_univ a))
              rw [hv]
              norm_num [delta, *]
            · have hcf : c ≠ f := Ne.symm hfc
              have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a a c a a f i ∂gaussianReal 0 1) = 0 := by
                apply Finset.prod_eq_zero (Finset.mem_univ c)
                have he : mult6 a a c a a f c = 1 := by simp_all [mult6, eq_comm]
                rw [he, gauss_int_pow_mgfPoly]
                norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
              rw [hv]
              norm_num [delta, *]
        · have hae : a ≠ e := Ne.symm hea
          by_cases hec : e = c
          · subst e
            by_cases hfa : f = a
            · subst f
              have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a a c a c a i ∂gaussianReal 0 1) = 3 := by
                rw [Finset.prod_eq_single a]
                · have he : mult6 a a c a c a a = 4 := by simp_all [mult6, eq_comm]
                  rw [he, gauss_int_pow_mgfPoly]
                  norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                · intro i _ hi
                  by_cases hic : i = c
                  all_goals simp_all [mult6, eq_comm, gauss_int_pow_mgfPoly, gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                · intro hh
                  exact False.elim (hh (Finset.mem_univ a))
              rw [hv]
              norm_num [delta, *]
            · have haf : a ≠ f := Ne.symm hfa
              by_cases hfc : f = c
              · subst f
                have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a a c a c c i ∂gaussianReal 0 1) = 0 := by
                  apply Finset.prod_eq_zero (Finset.mem_univ a)
                  have he : mult6 a a c a c c a = 3 := by simp_all [mult6, eq_comm]
                  rw [he, gauss_int_pow_mgfPoly]
                  norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                rw [hv]
                norm_num [delta, *]
              · have hcf : c ≠ f := Ne.symm hfc
                have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a a c a c f i ∂gaussianReal 0 1) = 0 := by
                  apply Finset.prod_eq_zero (Finset.mem_univ a)
                  have he : mult6 a a c a c f a = 3 := by simp_all [mult6, eq_comm]
                  rw [he, gauss_int_pow_mgfPoly]
                  norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                rw [hv]
                norm_num [delta, *]
          · have hce : c ≠ e := Ne.symm hec
            by_cases hfa : f = a
            · subst f
              have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a a c a e a i ∂gaussianReal 0 1) = 0 := by
                apply Finset.prod_eq_zero (Finset.mem_univ c)
                have he : mult6 a a c a e a c = 1 := by simp_all [mult6, eq_comm]
                rw [he, gauss_int_pow_mgfPoly]
                norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
              rw [hv]
              norm_num [delta, *]
            · have haf : a ≠ f := Ne.symm hfa
              by_cases hfc : f = c
              · subst f
                have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a a c a e c i ∂gaussianReal 0 1) = 0 := by
                  apply Finset.prod_eq_zero (Finset.mem_univ a)
                  have he : mult6 a a c a e c a = 3 := by simp_all [mult6, eq_comm]
                  rw [he, gauss_int_pow_mgfPoly]
                  norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                rw [hv]
                norm_num [delta, *]
              · have hcf : c ≠ f := Ne.symm hfc
                by_cases hfe : f = e
                · subst f
                  have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a a c a e e i ∂gaussianReal 0 1) = 0 := by
                    apply Finset.prod_eq_zero (Finset.mem_univ a)
                    have he : mult6 a a c a e e a = 3 := by simp_all [mult6, eq_comm]
                    rw [he, gauss_int_pow_mgfPoly]
                    norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                  rw [hv]
                  norm_num [delta, *]
                · have hef : e ≠ f := Ne.symm hfe
                  have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a a c a e f i ∂gaussianReal 0 1) = 0 := by
                    apply Finset.prod_eq_zero (Finset.mem_univ a)
                    have he : mult6 a a c a e f a = 3 := by simp_all [mult6, eq_comm]
                    rw [he, gauss_int_pow_mgfPoly]
                    norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                  rw [hv]
                  norm_num [delta, *]
      · have had : a ≠ d := Ne.symm hda
        by_cases hdc : d = c
        · subst d
          by_cases hea : e = a
          · subst e
            by_cases hfa : f = a
            · subst f
              have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a a c c a a i ∂gaussianReal 0 1) = 3 := by
                rw [Finset.prod_eq_single a]
                · have he : mult6 a a c c a a a = 4 := by simp_all [mult6, eq_comm]
                  rw [he, gauss_int_pow_mgfPoly]
                  norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                · intro i _ hi
                  by_cases hic : i = c
                  all_goals simp_all [mult6, eq_comm, gauss_int_pow_mgfPoly, gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                · intro hh
                  exact False.elim (hh (Finset.mem_univ a))
              rw [hv]
              norm_num [delta, *]
            · have haf : a ≠ f := Ne.symm hfa
              by_cases hfc : f = c
              · subst f
                have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a a c c a c i ∂gaussianReal 0 1) = 0 := by
                  apply Finset.prod_eq_zero (Finset.mem_univ a)
                  have he : mult6 a a c c a c a = 3 := by simp_all [mult6, eq_comm]
                  rw [he, gauss_int_pow_mgfPoly]
                  norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                rw [hv]
                norm_num [delta, *]
              · have hcf : c ≠ f := Ne.symm hfc
                have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a a c c a f i ∂gaussianReal 0 1) = 0 := by
                  apply Finset.prod_eq_zero (Finset.mem_univ a)
                  have he : mult6 a a c c a f a = 3 := by simp_all [mult6, eq_comm]
                  rw [he, gauss_int_pow_mgfPoly]
                  norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                rw [hv]
                norm_num [delta, *]
          · have hae : a ≠ e := Ne.symm hea
            by_cases hec : e = c
            · subst e
              by_cases hfa : f = a
              · subst f
                have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a a c c c a i ∂gaussianReal 0 1) = 0 := by
                  apply Finset.prod_eq_zero (Finset.mem_univ a)
                  have he : mult6 a a c c c a a = 3 := by simp_all [mult6, eq_comm]
                  rw [he, gauss_int_pow_mgfPoly]
                  norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                rw [hv]
                norm_num [delta, *]
              · have haf : a ≠ f := Ne.symm hfa
                by_cases hfc : f = c
                · subst f
                  have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a a c c c c i ∂gaussianReal 0 1) = 3 := by
                    rw [Finset.prod_eq_single c]
                    · have he : mult6 a a c c c c c = 4 := by simp_all [mult6, eq_comm]
                      rw [he, gauss_int_pow_mgfPoly]
                      norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                    · intro i _ hi
                      by_cases hia : i = a
                      all_goals simp_all [mult6, eq_comm, gauss_int_pow_mgfPoly, gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                    · intro hh
                      exact False.elim (hh (Finset.mem_univ c))
                  rw [hv]
                  norm_num [delta, *]
                · have hcf : c ≠ f := Ne.symm hfc
                  have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a a c c c f i ∂gaussianReal 0 1) = 0 := by
                    apply Finset.prod_eq_zero (Finset.mem_univ c)
                    have he : mult6 a a c c c f c = 3 := by simp_all [mult6, eq_comm]
                    rw [he, gauss_int_pow_mgfPoly]
                    norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                  rw [hv]
                  norm_num [delta, *]
            · have hce : c ≠ e := Ne.symm hec
              by_cases hfa : f = a
              · subst f
                have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a a c c e a i ∂gaussianReal 0 1) = 0 := by
                  apply Finset.prod_eq_zero (Finset.mem_univ a)
                  have he : mult6 a a c c e a a = 3 := by simp_all [mult6, eq_comm]
                  rw [he, gauss_int_pow_mgfPoly]
                  norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                rw [hv]
                norm_num [delta, *]
              · have haf : a ≠ f := Ne.symm hfa
                by_cases hfc : f = c
                · subst f
                  have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a a c c e c i ∂gaussianReal 0 1) = 0 := by
                    apply Finset.prod_eq_zero (Finset.mem_univ c)
                    have he : mult6 a a c c e c c = 3 := by simp_all [mult6, eq_comm]
                    rw [he, gauss_int_pow_mgfPoly]
                    norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                  rw [hv]
                  norm_num [delta, *]
                · have hcf : c ≠ f := Ne.symm hfc
                  by_cases hfe : f = e
                  · subst f
                    have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a a c c e e i ∂gaussianReal 0 1) = 1 := by
                      apply Finset.prod_eq_one
                      intro i _
                      all_goals by_cases hia : i = a
                      all_goals by_cases hic : i = c
                      all_goals by_cases hie : i = e
                      all_goals simp_all [mult6, eq_comm, gauss_int_pow_mgfPoly, gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                    rw [hv]
                    norm_num [delta, *]
                  · have hef : e ≠ f := Ne.symm hfe
                    have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a a c c e f i ∂gaussianReal 0 1) = 0 := by
                      apply Finset.prod_eq_zero (Finset.mem_univ e)
                      have he : mult6 a a c c e f e = 1 := by simp_all [mult6, eq_comm]
                      rw [he, gauss_int_pow_mgfPoly]
                      norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                    rw [hv]
                    norm_num [delta, *]
        · have hcd : c ≠ d := Ne.symm hdc
          by_cases hea : e = a
          · subst e
            by_cases hfa : f = a
            · subst f
              have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a a c d a a i ∂gaussianReal 0 1) = 0 := by
                apply Finset.prod_eq_zero (Finset.mem_univ c)
                have he : mult6 a a c d a a c = 1 := by simp_all [mult6, eq_comm]
                rw [he, gauss_int_pow_mgfPoly]
                norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
              rw [hv]
              norm_num [delta, *]
            · have haf : a ≠ f := Ne.symm hfa
              by_cases hfc : f = c
              · subst f
                have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a a c d a c i ∂gaussianReal 0 1) = 0 := by
                  apply Finset.prod_eq_zero (Finset.mem_univ a)
                  have he : mult6 a a c d a c a = 3 := by simp_all [mult6, eq_comm]
                  rw [he, gauss_int_pow_mgfPoly]
                  norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                rw [hv]
                norm_num [delta, *]
              · have hcf : c ≠ f := Ne.symm hfc
                by_cases hfd : f = d
                · subst f
                  have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a a c d a d i ∂gaussianReal 0 1) = 0 := by
                    apply Finset.prod_eq_zero (Finset.mem_univ a)
                    have he : mult6 a a c d a d a = 3 := by simp_all [mult6, eq_comm]
                    rw [he, gauss_int_pow_mgfPoly]
                    norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                  rw [hv]
                  norm_num [delta, *]
                · have hdf : d ≠ f := Ne.symm hfd
                  have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a a c d a f i ∂gaussianReal 0 1) = 0 := by
                    apply Finset.prod_eq_zero (Finset.mem_univ a)
                    have he : mult6 a a c d a f a = 3 := by simp_all [mult6, eq_comm]
                    rw [he, gauss_int_pow_mgfPoly]
                    norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                  rw [hv]
                  norm_num [delta, *]
          · have hae : a ≠ e := Ne.symm hea
            by_cases hec : e = c
            · subst e
              by_cases hfa : f = a
              · subst f
                have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a a c d c a i ∂gaussianReal 0 1) = 0 := by
                  apply Finset.prod_eq_zero (Finset.mem_univ a)
                  have he : mult6 a a c d c a a = 3 := by simp_all [mult6, eq_comm]
                  rw [he, gauss_int_pow_mgfPoly]
                  norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                rw [hv]
                norm_num [delta, *]
              · have haf : a ≠ f := Ne.symm hfa
                by_cases hfc : f = c
                · subst f
                  have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a a c d c c i ∂gaussianReal 0 1) = 0 := by
                    apply Finset.prod_eq_zero (Finset.mem_univ c)
                    have he : mult6 a a c d c c c = 3 := by simp_all [mult6, eq_comm]
                    rw [he, gauss_int_pow_mgfPoly]
                    norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                  rw [hv]
                  norm_num [delta, *]
                · have hcf : c ≠ f := Ne.symm hfc
                  by_cases hfd : f = d
                  · subst f
                    have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a a c d c d i ∂gaussianReal 0 1) = 1 := by
                      apply Finset.prod_eq_one
                      intro i _
                      all_goals by_cases hia : i = a
                      all_goals by_cases hic : i = c
                      all_goals by_cases hid : i = d
                      all_goals simp_all [mult6, eq_comm, gauss_int_pow_mgfPoly, gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                    rw [hv]
                    norm_num [delta, *]
                  · have hdf : d ≠ f := Ne.symm hfd
                    have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a a c d c f i ∂gaussianReal 0 1) = 0 := by
                      apply Finset.prod_eq_zero (Finset.mem_univ d)
                      have he : mult6 a a c d c f d = 1 := by simp_all [mult6, eq_comm]
                      rw [he, gauss_int_pow_mgfPoly]
                      norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                    rw [hv]
                    norm_num [delta, *]
            · have hce : c ≠ e := Ne.symm hec
              by_cases hed : e = d
              · subst e
                by_cases hfa : f = a
                · subst f
                  have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a a c d d a i ∂gaussianReal 0 1) = 0 := by
                    apply Finset.prod_eq_zero (Finset.mem_univ a)
                    have he : mult6 a a c d d a a = 3 := by simp_all [mult6, eq_comm]
                    rw [he, gauss_int_pow_mgfPoly]
                    norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                  rw [hv]
                  norm_num [delta, *]
                · have haf : a ≠ f := Ne.symm hfa
                  by_cases hfc : f = c
                  · subst f
                    have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a a c d d c i ∂gaussianReal 0 1) = 1 := by
                      apply Finset.prod_eq_one
                      intro i _
                      all_goals by_cases hia : i = a
                      all_goals by_cases hic : i = c
                      all_goals by_cases hid : i = d
                      all_goals simp_all [mult6, eq_comm, gauss_int_pow_mgfPoly, gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                    rw [hv]
                    norm_num [delta, *]
                  · have hcf : c ≠ f := Ne.symm hfc
                    by_cases hfd : f = d
                    · subst f
                      have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a a c d d d i ∂gaussianReal 0 1) = 0 := by
                        apply Finset.prod_eq_zero (Finset.mem_univ c)
                        have he : mult6 a a c d d d c = 1 := by simp_all [mult6, eq_comm]
                        rw [he, gauss_int_pow_mgfPoly]
                        norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                      rw [hv]
                      norm_num [delta, *]
                    · have hdf : d ≠ f := Ne.symm hfd
                      have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a a c d d f i ∂gaussianReal 0 1) = 0 := by
                        apply Finset.prod_eq_zero (Finset.mem_univ c)
                        have he : mult6 a a c d d f c = 1 := by simp_all [mult6, eq_comm]
                        rw [he, gauss_int_pow_mgfPoly]
                        norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                      rw [hv]
                      norm_num [delta, *]
              · have hde : d ≠ e := Ne.symm hed
                by_cases hfa : f = a
                · subst f
                  have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a a c d e a i ∂gaussianReal 0 1) = 0 := by
                    apply Finset.prod_eq_zero (Finset.mem_univ a)
                    have he : mult6 a a c d e a a = 3 := by simp_all [mult6, eq_comm]
                    rw [he, gauss_int_pow_mgfPoly]
                    norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                  rw [hv]
                  norm_num [delta, *]
                · have haf : a ≠ f := Ne.symm hfa
                  by_cases hfc : f = c
                  · subst f
                    have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a a c d e c i ∂gaussianReal 0 1) = 0 := by
                      apply Finset.prod_eq_zero (Finset.mem_univ d)
                      have he : mult6 a a c d e c d = 1 := by simp_all [mult6, eq_comm]
                      rw [he, gauss_int_pow_mgfPoly]
                      norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                    rw [hv]
                    norm_num [delta, *]
                  · have hcf : c ≠ f := Ne.symm hfc
                    by_cases hfd : f = d
                    · subst f
                      have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a a c d e d i ∂gaussianReal 0 1) = 0 := by
                        apply Finset.prod_eq_zero (Finset.mem_univ c)
                        have he : mult6 a a c d e d c = 1 := by simp_all [mult6, eq_comm]
                        rw [he, gauss_int_pow_mgfPoly]
                        norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                      rw [hv]
                      norm_num [delta, *]
                    · have hdf : d ≠ f := Ne.symm hfd
                      by_cases hfe : f = e
                      · subst f
                        have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a a c d e e i ∂gaussianReal 0 1) = 0 := by
                          apply Finset.prod_eq_zero (Finset.mem_univ c)
                          have he : mult6 a a c d e e c = 1 := by simp_all [mult6, eq_comm]
                          rw [he, gauss_int_pow_mgfPoly]
                          norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                        rw [hv]
                        norm_num [delta, *]
                      · have hef : e ≠ f := Ne.symm hfe
                        have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a a c d e f i ∂gaussianReal 0 1) = 0 := by
                          apply Finset.prod_eq_zero (Finset.mem_univ c)
                          have he : mult6 a a c d e f c = 1 := by simp_all [mult6, eq_comm]
                          rw [he, gauss_int_pow_mgfPoly]
                          norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                        rw [hv]
                        norm_num [delta, *]
  · have hab : a ≠ b := Ne.symm hba
    by_cases hca : c = a
    · subst c
      by_cases hda : d = a
      · subst d
        by_cases hea : e = a
        · subst e
          by_cases hfa : f = a
          · subst f
            have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b a a a a i ∂gaussianReal 0 1) = 0 := by
              apply Finset.prod_eq_zero (Finset.mem_univ a)
              have he : mult6 a b a a a a a = 5 := by simp_all [mult6, eq_comm]
              rw [he, gauss_int_pow_mgfPoly]
              norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
            rw [hv]
            norm_num [delta, *]
          · have haf : a ≠ f := Ne.symm hfa
            by_cases hfb : f = b
            · subst f
              have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b a a a b i ∂gaussianReal 0 1) = 3 := by
                rw [Finset.prod_eq_single a]
                · have he : mult6 a b a a a b a = 4 := by simp_all [mult6, eq_comm]
                  rw [he, gauss_int_pow_mgfPoly]
                  norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                · intro i _ hi
                  by_cases hib : i = b
                  all_goals simp_all [mult6, eq_comm, gauss_int_pow_mgfPoly, gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                · intro hh
                  exact False.elim (hh (Finset.mem_univ a))
              rw [hv]
              norm_num [delta, *]
            · have hbf : b ≠ f := Ne.symm hfb
              have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b a a a f i ∂gaussianReal 0 1) = 0 := by
                apply Finset.prod_eq_zero (Finset.mem_univ b)
                have he : mult6 a b a a a f b = 1 := by simp_all [mult6, eq_comm]
                rw [he, gauss_int_pow_mgfPoly]
                norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
              rw [hv]
              norm_num [delta, *]
        · have hae : a ≠ e := Ne.symm hea
          by_cases heb : e = b
          · subst e
            by_cases hfa : f = a
            · subst f
              have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b a a b a i ∂gaussianReal 0 1) = 3 := by
                rw [Finset.prod_eq_single a]
                · have he : mult6 a b a a b a a = 4 := by simp_all [mult6, eq_comm]
                  rw [he, gauss_int_pow_mgfPoly]
                  norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                · intro i _ hi
                  by_cases hib : i = b
                  all_goals simp_all [mult6, eq_comm, gauss_int_pow_mgfPoly, gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                · intro hh
                  exact False.elim (hh (Finset.mem_univ a))
              rw [hv]
              norm_num [delta, *]
            · have haf : a ≠ f := Ne.symm hfa
              by_cases hfb : f = b
              · subst f
                have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b a a b b i ∂gaussianReal 0 1) = 0 := by
                  apply Finset.prod_eq_zero (Finset.mem_univ a)
                  have he : mult6 a b a a b b a = 3 := by simp_all [mult6, eq_comm]
                  rw [he, gauss_int_pow_mgfPoly]
                  norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                rw [hv]
                norm_num [delta, *]
              · have hbf : b ≠ f := Ne.symm hfb
                have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b a a b f i ∂gaussianReal 0 1) = 0 := by
                  apply Finset.prod_eq_zero (Finset.mem_univ a)
                  have he : mult6 a b a a b f a = 3 := by simp_all [mult6, eq_comm]
                  rw [he, gauss_int_pow_mgfPoly]
                  norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                rw [hv]
                norm_num [delta, *]
          · have hbe : b ≠ e := Ne.symm heb
            by_cases hfa : f = a
            · subst f
              have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b a a e a i ∂gaussianReal 0 1) = 0 := by
                apply Finset.prod_eq_zero (Finset.mem_univ b)
                have he : mult6 a b a a e a b = 1 := by simp_all [mult6, eq_comm]
                rw [he, gauss_int_pow_mgfPoly]
                norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
              rw [hv]
              norm_num [delta, *]
            · have haf : a ≠ f := Ne.symm hfa
              by_cases hfb : f = b
              · subst f
                have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b a a e b i ∂gaussianReal 0 1) = 0 := by
                  apply Finset.prod_eq_zero (Finset.mem_univ a)
                  have he : mult6 a b a a e b a = 3 := by simp_all [mult6, eq_comm]
                  rw [he, gauss_int_pow_mgfPoly]
                  norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                rw [hv]
                norm_num [delta, *]
              · have hbf : b ≠ f := Ne.symm hfb
                by_cases hfe : f = e
                · subst f
                  have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b a a e e i ∂gaussianReal 0 1) = 0 := by
                    apply Finset.prod_eq_zero (Finset.mem_univ a)
                    have he : mult6 a b a a e e a = 3 := by simp_all [mult6, eq_comm]
                    rw [he, gauss_int_pow_mgfPoly]
                    norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                  rw [hv]
                  norm_num [delta, *]
                · have hef : e ≠ f := Ne.symm hfe
                  have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b a a e f i ∂gaussianReal 0 1) = 0 := by
                    apply Finset.prod_eq_zero (Finset.mem_univ a)
                    have he : mult6 a b a a e f a = 3 := by simp_all [mult6, eq_comm]
                    rw [he, gauss_int_pow_mgfPoly]
                    norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                  rw [hv]
                  norm_num [delta, *]
      · have had : a ≠ d := Ne.symm hda
        by_cases hdb : d = b
        · subst d
          by_cases hea : e = a
          · subst e
            by_cases hfa : f = a
            · subst f
              have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b a b a a i ∂gaussianReal 0 1) = 3 := by
                rw [Finset.prod_eq_single a]
                · have he : mult6 a b a b a a a = 4 := by simp_all [mult6, eq_comm]
                  rw [he, gauss_int_pow_mgfPoly]
                  norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                · intro i _ hi
                  by_cases hib : i = b
                  all_goals simp_all [mult6, eq_comm, gauss_int_pow_mgfPoly, gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                · intro hh
                  exact False.elim (hh (Finset.mem_univ a))
              rw [hv]
              norm_num [delta, *]
            · have haf : a ≠ f := Ne.symm hfa
              by_cases hfb : f = b
              · subst f
                have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b a b a b i ∂gaussianReal 0 1) = 0 := by
                  apply Finset.prod_eq_zero (Finset.mem_univ a)
                  have he : mult6 a b a b a b a = 3 := by simp_all [mult6, eq_comm]
                  rw [he, gauss_int_pow_mgfPoly]
                  norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                rw [hv]
                norm_num [delta, *]
              · have hbf : b ≠ f := Ne.symm hfb
                have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b a b a f i ∂gaussianReal 0 1) = 0 := by
                  apply Finset.prod_eq_zero (Finset.mem_univ a)
                  have he : mult6 a b a b a f a = 3 := by simp_all [mult6, eq_comm]
                  rw [he, gauss_int_pow_mgfPoly]
                  norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                rw [hv]
                norm_num [delta, *]
          · have hae : a ≠ e := Ne.symm hea
            by_cases heb : e = b
            · subst e
              by_cases hfa : f = a
              · subst f
                have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b a b b a i ∂gaussianReal 0 1) = 0 := by
                  apply Finset.prod_eq_zero (Finset.mem_univ a)
                  have he : mult6 a b a b b a a = 3 := by simp_all [mult6, eq_comm]
                  rw [he, gauss_int_pow_mgfPoly]
                  norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                rw [hv]
                norm_num [delta, *]
              · have haf : a ≠ f := Ne.symm hfa
                by_cases hfb : f = b
                · subst f
                  have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b a b b b i ∂gaussianReal 0 1) = 3 := by
                    rw [Finset.prod_eq_single b]
                    · have he : mult6 a b a b b b b = 4 := by simp_all [mult6, eq_comm]
                      rw [he, gauss_int_pow_mgfPoly]
                      norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                    · intro i _ hi
                      by_cases hia : i = a
                      all_goals simp_all [mult6, eq_comm, gauss_int_pow_mgfPoly, gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                    · intro hh
                      exact False.elim (hh (Finset.mem_univ b))
                  rw [hv]
                  norm_num [delta, *]
                · have hbf : b ≠ f := Ne.symm hfb
                  have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b a b b f i ∂gaussianReal 0 1) = 0 := by
                    apply Finset.prod_eq_zero (Finset.mem_univ b)
                    have he : mult6 a b a b b f b = 3 := by simp_all [mult6, eq_comm]
                    rw [he, gauss_int_pow_mgfPoly]
                    norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                  rw [hv]
                  norm_num [delta, *]
            · have hbe : b ≠ e := Ne.symm heb
              by_cases hfa : f = a
              · subst f
                have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b a b e a i ∂gaussianReal 0 1) = 0 := by
                  apply Finset.prod_eq_zero (Finset.mem_univ a)
                  have he : mult6 a b a b e a a = 3 := by simp_all [mult6, eq_comm]
                  rw [he, gauss_int_pow_mgfPoly]
                  norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                rw [hv]
                norm_num [delta, *]
              · have haf : a ≠ f := Ne.symm hfa
                by_cases hfb : f = b
                · subst f
                  have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b a b e b i ∂gaussianReal 0 1) = 0 := by
                    apply Finset.prod_eq_zero (Finset.mem_univ b)
                    have he : mult6 a b a b e b b = 3 := by simp_all [mult6, eq_comm]
                    rw [he, gauss_int_pow_mgfPoly]
                    norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                  rw [hv]
                  norm_num [delta, *]
                · have hbf : b ≠ f := Ne.symm hfb
                  by_cases hfe : f = e
                  · subst f
                    have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b a b e e i ∂gaussianReal 0 1) = 1 := by
                      apply Finset.prod_eq_one
                      intro i _
                      all_goals by_cases hia : i = a
                      all_goals by_cases hib : i = b
                      all_goals by_cases hie : i = e
                      all_goals simp_all [mult6, eq_comm, gauss_int_pow_mgfPoly, gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                    rw [hv]
                    norm_num [delta, *]
                  · have hef : e ≠ f := Ne.symm hfe
                    have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b a b e f i ∂gaussianReal 0 1) = 0 := by
                      apply Finset.prod_eq_zero (Finset.mem_univ e)
                      have he : mult6 a b a b e f e = 1 := by simp_all [mult6, eq_comm]
                      rw [he, gauss_int_pow_mgfPoly]
                      norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                    rw [hv]
                    norm_num [delta, *]
        · have hbd : b ≠ d := Ne.symm hdb
          by_cases hea : e = a
          · subst e
            by_cases hfa : f = a
            · subst f
              have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b a d a a i ∂gaussianReal 0 1) = 0 := by
                apply Finset.prod_eq_zero (Finset.mem_univ b)
                have he : mult6 a b a d a a b = 1 := by simp_all [mult6, eq_comm]
                rw [he, gauss_int_pow_mgfPoly]
                norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
              rw [hv]
              norm_num [delta, *]
            · have haf : a ≠ f := Ne.symm hfa
              by_cases hfb : f = b
              · subst f
                have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b a d a b i ∂gaussianReal 0 1) = 0 := by
                  apply Finset.prod_eq_zero (Finset.mem_univ a)
                  have he : mult6 a b a d a b a = 3 := by simp_all [mult6, eq_comm]
                  rw [he, gauss_int_pow_mgfPoly]
                  norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                rw [hv]
                norm_num [delta, *]
              · have hbf : b ≠ f := Ne.symm hfb
                by_cases hfd : f = d
                · subst f
                  have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b a d a d i ∂gaussianReal 0 1) = 0 := by
                    apply Finset.prod_eq_zero (Finset.mem_univ a)
                    have he : mult6 a b a d a d a = 3 := by simp_all [mult6, eq_comm]
                    rw [he, gauss_int_pow_mgfPoly]
                    norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                  rw [hv]
                  norm_num [delta, *]
                · have hdf : d ≠ f := Ne.symm hfd
                  have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b a d a f i ∂gaussianReal 0 1) = 0 := by
                    apply Finset.prod_eq_zero (Finset.mem_univ a)
                    have he : mult6 a b a d a f a = 3 := by simp_all [mult6, eq_comm]
                    rw [he, gauss_int_pow_mgfPoly]
                    norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                  rw [hv]
                  norm_num [delta, *]
          · have hae : a ≠ e := Ne.symm hea
            by_cases heb : e = b
            · subst e
              by_cases hfa : f = a
              · subst f
                have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b a d b a i ∂gaussianReal 0 1) = 0 := by
                  apply Finset.prod_eq_zero (Finset.mem_univ a)
                  have he : mult6 a b a d b a a = 3 := by simp_all [mult6, eq_comm]
                  rw [he, gauss_int_pow_mgfPoly]
                  norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                rw [hv]
                norm_num [delta, *]
              · have haf : a ≠ f := Ne.symm hfa
                by_cases hfb : f = b
                · subst f
                  have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b a d b b i ∂gaussianReal 0 1) = 0 := by
                    apply Finset.prod_eq_zero (Finset.mem_univ b)
                    have he : mult6 a b a d b b b = 3 := by simp_all [mult6, eq_comm]
                    rw [he, gauss_int_pow_mgfPoly]
                    norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                  rw [hv]
                  norm_num [delta, *]
                · have hbf : b ≠ f := Ne.symm hfb
                  by_cases hfd : f = d
                  · subst f
                    have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b a d b d i ∂gaussianReal 0 1) = 1 := by
                      apply Finset.prod_eq_one
                      intro i _
                      all_goals by_cases hia : i = a
                      all_goals by_cases hib : i = b
                      all_goals by_cases hid : i = d
                      all_goals simp_all [mult6, eq_comm, gauss_int_pow_mgfPoly, gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                    rw [hv]
                    norm_num [delta, *]
                  · have hdf : d ≠ f := Ne.symm hfd
                    have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b a d b f i ∂gaussianReal 0 1) = 0 := by
                      apply Finset.prod_eq_zero (Finset.mem_univ d)
                      have he : mult6 a b a d b f d = 1 := by simp_all [mult6, eq_comm]
                      rw [he, gauss_int_pow_mgfPoly]
                      norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                    rw [hv]
                    norm_num [delta, *]
            · have hbe : b ≠ e := Ne.symm heb
              by_cases hed : e = d
              · subst e
                by_cases hfa : f = a
                · subst f
                  have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b a d d a i ∂gaussianReal 0 1) = 0 := by
                    apply Finset.prod_eq_zero (Finset.mem_univ a)
                    have he : mult6 a b a d d a a = 3 := by simp_all [mult6, eq_comm]
                    rw [he, gauss_int_pow_mgfPoly]
                    norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                  rw [hv]
                  norm_num [delta, *]
                · have haf : a ≠ f := Ne.symm hfa
                  by_cases hfb : f = b
                  · subst f
                    have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b a d d b i ∂gaussianReal 0 1) = 1 := by
                      apply Finset.prod_eq_one
                      intro i _
                      all_goals by_cases hia : i = a
                      all_goals by_cases hib : i = b
                      all_goals by_cases hid : i = d
                      all_goals simp_all [mult6, eq_comm, gauss_int_pow_mgfPoly, gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                    rw [hv]
                    norm_num [delta, *]
                  · have hbf : b ≠ f := Ne.symm hfb
                    by_cases hfd : f = d
                    · subst f
                      have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b a d d d i ∂gaussianReal 0 1) = 0 := by
                        apply Finset.prod_eq_zero (Finset.mem_univ b)
                        have he : mult6 a b a d d d b = 1 := by simp_all [mult6, eq_comm]
                        rw [he, gauss_int_pow_mgfPoly]
                        norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                      rw [hv]
                      norm_num [delta, *]
                    · have hdf : d ≠ f := Ne.symm hfd
                      have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b a d d f i ∂gaussianReal 0 1) = 0 := by
                        apply Finset.prod_eq_zero (Finset.mem_univ b)
                        have he : mult6 a b a d d f b = 1 := by simp_all [mult6, eq_comm]
                        rw [he, gauss_int_pow_mgfPoly]
                        norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                      rw [hv]
                      norm_num [delta, *]
              · have hde : d ≠ e := Ne.symm hed
                by_cases hfa : f = a
                · subst f
                  have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b a d e a i ∂gaussianReal 0 1) = 0 := by
                    apply Finset.prod_eq_zero (Finset.mem_univ a)
                    have he : mult6 a b a d e a a = 3 := by simp_all [mult6, eq_comm]
                    rw [he, gauss_int_pow_mgfPoly]
                    norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                  rw [hv]
                  norm_num [delta, *]
                · have haf : a ≠ f := Ne.symm hfa
                  by_cases hfb : f = b
                  · subst f
                    have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b a d e b i ∂gaussianReal 0 1) = 0 := by
                      apply Finset.prod_eq_zero (Finset.mem_univ d)
                      have he : mult6 a b a d e b d = 1 := by simp_all [mult6, eq_comm]
                      rw [he, gauss_int_pow_mgfPoly]
                      norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                    rw [hv]
                    norm_num [delta, *]
                  · have hbf : b ≠ f := Ne.symm hfb
                    by_cases hfd : f = d
                    · subst f
                      have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b a d e d i ∂gaussianReal 0 1) = 0 := by
                        apply Finset.prod_eq_zero (Finset.mem_univ b)
                        have he : mult6 a b a d e d b = 1 := by simp_all [mult6, eq_comm]
                        rw [he, gauss_int_pow_mgfPoly]
                        norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                      rw [hv]
                      norm_num [delta, *]
                    · have hdf : d ≠ f := Ne.symm hfd
                      by_cases hfe : f = e
                      · subst f
                        have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b a d e e i ∂gaussianReal 0 1) = 0 := by
                          apply Finset.prod_eq_zero (Finset.mem_univ b)
                          have he : mult6 a b a d e e b = 1 := by simp_all [mult6, eq_comm]
                          rw [he, gauss_int_pow_mgfPoly]
                          norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                        rw [hv]
                        norm_num [delta, *]
                      · have hef : e ≠ f := Ne.symm hfe
                        have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b a d e f i ∂gaussianReal 0 1) = 0 := by
                          apply Finset.prod_eq_zero (Finset.mem_univ b)
                          have he : mult6 a b a d e f b = 1 := by simp_all [mult6, eq_comm]
                          rw [he, gauss_int_pow_mgfPoly]
                          norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                        rw [hv]
                        norm_num [delta, *]
    · have hac : a ≠ c := Ne.symm hca
      by_cases hcb : c = b
      · subst c
        by_cases hda : d = a
        · subst d
          by_cases hea : e = a
          · subst e
            by_cases hfa : f = a
            · subst f
              have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b b a a a i ∂gaussianReal 0 1) = 3 := by
                rw [Finset.prod_eq_single a]
                · have he : mult6 a b b a a a a = 4 := by simp_all [mult6, eq_comm]
                  rw [he, gauss_int_pow_mgfPoly]
                  norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                · intro i _ hi
                  by_cases hib : i = b
                  all_goals simp_all [mult6, eq_comm, gauss_int_pow_mgfPoly, gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                · intro hh
                  exact False.elim (hh (Finset.mem_univ a))
              rw [hv]
              norm_num [delta, *]
            · have haf : a ≠ f := Ne.symm hfa
              by_cases hfb : f = b
              · subst f
                have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b b a a b i ∂gaussianReal 0 1) = 0 := by
                  apply Finset.prod_eq_zero (Finset.mem_univ a)
                  have he : mult6 a b b a a b a = 3 := by simp_all [mult6, eq_comm]
                  rw [he, gauss_int_pow_mgfPoly]
                  norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                rw [hv]
                norm_num [delta, *]
              · have hbf : b ≠ f := Ne.symm hfb
                have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b b a a f i ∂gaussianReal 0 1) = 0 := by
                  apply Finset.prod_eq_zero (Finset.mem_univ a)
                  have he : mult6 a b b a a f a = 3 := by simp_all [mult6, eq_comm]
                  rw [he, gauss_int_pow_mgfPoly]
                  norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                rw [hv]
                norm_num [delta, *]
          · have hae : a ≠ e := Ne.symm hea
            by_cases heb : e = b
            · subst e
              by_cases hfa : f = a
              · subst f
                have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b b a b a i ∂gaussianReal 0 1) = 0 := by
                  apply Finset.prod_eq_zero (Finset.mem_univ a)
                  have he : mult6 a b b a b a a = 3 := by simp_all [mult6, eq_comm]
                  rw [he, gauss_int_pow_mgfPoly]
                  norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                rw [hv]
                norm_num [delta, *]
              · have haf : a ≠ f := Ne.symm hfa
                by_cases hfb : f = b
                · subst f
                  have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b b a b b i ∂gaussianReal 0 1) = 3 := by
                    rw [Finset.prod_eq_single b]
                    · have he : mult6 a b b a b b b = 4 := by simp_all [mult6, eq_comm]
                      rw [he, gauss_int_pow_mgfPoly]
                      norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                    · intro i _ hi
                      by_cases hia : i = a
                      all_goals simp_all [mult6, eq_comm, gauss_int_pow_mgfPoly, gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                    · intro hh
                      exact False.elim (hh (Finset.mem_univ b))
                  rw [hv]
                  norm_num [delta, *]
                · have hbf : b ≠ f := Ne.symm hfb
                  have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b b a b f i ∂gaussianReal 0 1) = 0 := by
                    apply Finset.prod_eq_zero (Finset.mem_univ b)
                    have he : mult6 a b b a b f b = 3 := by simp_all [mult6, eq_comm]
                    rw [he, gauss_int_pow_mgfPoly]
                    norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                  rw [hv]
                  norm_num [delta, *]
            · have hbe : b ≠ e := Ne.symm heb
              by_cases hfa : f = a
              · subst f
                have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b b a e a i ∂gaussianReal 0 1) = 0 := by
                  apply Finset.prod_eq_zero (Finset.mem_univ a)
                  have he : mult6 a b b a e a a = 3 := by simp_all [mult6, eq_comm]
                  rw [he, gauss_int_pow_mgfPoly]
                  norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                rw [hv]
                norm_num [delta, *]
              · have haf : a ≠ f := Ne.symm hfa
                by_cases hfb : f = b
                · subst f
                  have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b b a e b i ∂gaussianReal 0 1) = 0 := by
                    apply Finset.prod_eq_zero (Finset.mem_univ b)
                    have he : mult6 a b b a e b b = 3 := by simp_all [mult6, eq_comm]
                    rw [he, gauss_int_pow_mgfPoly]
                    norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                  rw [hv]
                  norm_num [delta, *]
                · have hbf : b ≠ f := Ne.symm hfb
                  by_cases hfe : f = e
                  · subst f
                    have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b b a e e i ∂gaussianReal 0 1) = 1 := by
                      apply Finset.prod_eq_one
                      intro i _
                      all_goals by_cases hia : i = a
                      all_goals by_cases hib : i = b
                      all_goals by_cases hie : i = e
                      all_goals simp_all [mult6, eq_comm, gauss_int_pow_mgfPoly, gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                    rw [hv]
                    norm_num [delta, *]
                  · have hef : e ≠ f := Ne.symm hfe
                    have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b b a e f i ∂gaussianReal 0 1) = 0 := by
                      apply Finset.prod_eq_zero (Finset.mem_univ e)
                      have he : mult6 a b b a e f e = 1 := by simp_all [mult6, eq_comm]
                      rw [he, gauss_int_pow_mgfPoly]
                      norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                    rw [hv]
                    norm_num [delta, *]
        · have had : a ≠ d := Ne.symm hda
          by_cases hdb : d = b
          · subst d
            by_cases hea : e = a
            · subst e
              by_cases hfa : f = a
              · subst f
                have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b b b a a i ∂gaussianReal 0 1) = 0 := by
                  apply Finset.prod_eq_zero (Finset.mem_univ a)
                  have he : mult6 a b b b a a a = 3 := by simp_all [mult6, eq_comm]
                  rw [he, gauss_int_pow_mgfPoly]
                  norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                rw [hv]
                norm_num [delta, *]
              · have haf : a ≠ f := Ne.symm hfa
                by_cases hfb : f = b
                · subst f
                  have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b b b a b i ∂gaussianReal 0 1) = 3 := by
                    rw [Finset.prod_eq_single b]
                    · have he : mult6 a b b b a b b = 4 := by simp_all [mult6, eq_comm]
                      rw [he, gauss_int_pow_mgfPoly]
                      norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                    · intro i _ hi
                      by_cases hia : i = a
                      all_goals simp_all [mult6, eq_comm, gauss_int_pow_mgfPoly, gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                    · intro hh
                      exact False.elim (hh (Finset.mem_univ b))
                  rw [hv]
                  norm_num [delta, *]
                · have hbf : b ≠ f := Ne.symm hfb
                  have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b b b a f i ∂gaussianReal 0 1) = 0 := by
                    apply Finset.prod_eq_zero (Finset.mem_univ b)
                    have he : mult6 a b b b a f b = 3 := by simp_all [mult6, eq_comm]
                    rw [he, gauss_int_pow_mgfPoly]
                    norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                  rw [hv]
                  norm_num [delta, *]
            · have hae : a ≠ e := Ne.symm hea
              by_cases heb : e = b
              · subst e
                by_cases hfa : f = a
                · subst f
                  have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b b b b a i ∂gaussianReal 0 1) = 3 := by
                    rw [Finset.prod_eq_single b]
                    · have he : mult6 a b b b b a b = 4 := by simp_all [mult6, eq_comm]
                      rw [he, gauss_int_pow_mgfPoly]
                      norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                    · intro i _ hi
                      by_cases hia : i = a
                      all_goals simp_all [mult6, eq_comm, gauss_int_pow_mgfPoly, gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                    · intro hh
                      exact False.elim (hh (Finset.mem_univ b))
                  rw [hv]
                  norm_num [delta, *]
                · have haf : a ≠ f := Ne.symm hfa
                  by_cases hfb : f = b
                  · subst f
                    have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b b b b b i ∂gaussianReal 0 1) = 0 := by
                      apply Finset.prod_eq_zero (Finset.mem_univ a)
                      have he : mult6 a b b b b b a = 1 := by simp_all [mult6, eq_comm]
                      rw [he, gauss_int_pow_mgfPoly]
                      norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                    rw [hv]
                    norm_num [delta, *]
                  · have hbf : b ≠ f := Ne.symm hfb
                    have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b b b b f i ∂gaussianReal 0 1) = 0 := by
                      apply Finset.prod_eq_zero (Finset.mem_univ a)
                      have he : mult6 a b b b b f a = 1 := by simp_all [mult6, eq_comm]
                      rw [he, gauss_int_pow_mgfPoly]
                      norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                    rw [hv]
                    norm_num [delta, *]
              · have hbe : b ≠ e := Ne.symm heb
                by_cases hfa : f = a
                · subst f
                  have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b b b e a i ∂gaussianReal 0 1) = 0 := by
                    apply Finset.prod_eq_zero (Finset.mem_univ b)
                    have he : mult6 a b b b e a b = 3 := by simp_all [mult6, eq_comm]
                    rw [he, gauss_int_pow_mgfPoly]
                    norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                  rw [hv]
                  norm_num [delta, *]
                · have haf : a ≠ f := Ne.symm hfa
                  by_cases hfb : f = b
                  · subst f
                    have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b b b e b i ∂gaussianReal 0 1) = 0 := by
                      apply Finset.prod_eq_zero (Finset.mem_univ a)
                      have he : mult6 a b b b e b a = 1 := by simp_all [mult6, eq_comm]
                      rw [he, gauss_int_pow_mgfPoly]
                      norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                    rw [hv]
                    norm_num [delta, *]
                  · have hbf : b ≠ f := Ne.symm hfb
                    by_cases hfe : f = e
                    · subst f
                      have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b b b e e i ∂gaussianReal 0 1) = 0 := by
                        apply Finset.prod_eq_zero (Finset.mem_univ a)
                        have he : mult6 a b b b e e a = 1 := by simp_all [mult6, eq_comm]
                        rw [he, gauss_int_pow_mgfPoly]
                        norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                      rw [hv]
                      norm_num [delta, *]
                    · have hef : e ≠ f := Ne.symm hfe
                      have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b b b e f i ∂gaussianReal 0 1) = 0 := by
                        apply Finset.prod_eq_zero (Finset.mem_univ a)
                        have he : mult6 a b b b e f a = 1 := by simp_all [mult6, eq_comm]
                        rw [he, gauss_int_pow_mgfPoly]
                        norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                      rw [hv]
                      norm_num [delta, *]
          · have hbd : b ≠ d := Ne.symm hdb
            by_cases hea : e = a
            · subst e
              by_cases hfa : f = a
              · subst f
                have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b b d a a i ∂gaussianReal 0 1) = 0 := by
                  apply Finset.prod_eq_zero (Finset.mem_univ a)
                  have he : mult6 a b b d a a a = 3 := by simp_all [mult6, eq_comm]
                  rw [he, gauss_int_pow_mgfPoly]
                  norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                rw [hv]
                norm_num [delta, *]
              · have haf : a ≠ f := Ne.symm hfa
                by_cases hfb : f = b
                · subst f
                  have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b b d a b i ∂gaussianReal 0 1) = 0 := by
                    apply Finset.prod_eq_zero (Finset.mem_univ b)
                    have he : mult6 a b b d a b b = 3 := by simp_all [mult6, eq_comm]
                    rw [he, gauss_int_pow_mgfPoly]
                    norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                  rw [hv]
                  norm_num [delta, *]
                · have hbf : b ≠ f := Ne.symm hfb
                  by_cases hfd : f = d
                  · subst f
                    have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b b d a d i ∂gaussianReal 0 1) = 1 := by
                      apply Finset.prod_eq_one
                      intro i _
                      all_goals by_cases hia : i = a
                      all_goals by_cases hib : i = b
                      all_goals by_cases hid : i = d
                      all_goals simp_all [mult6, eq_comm, gauss_int_pow_mgfPoly, gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                    rw [hv]
                    norm_num [delta, *]
                  · have hdf : d ≠ f := Ne.symm hfd
                    have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b b d a f i ∂gaussianReal 0 1) = 0 := by
                      apply Finset.prod_eq_zero (Finset.mem_univ d)
                      have he : mult6 a b b d a f d = 1 := by simp_all [mult6, eq_comm]
                      rw [he, gauss_int_pow_mgfPoly]
                      norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                    rw [hv]
                    norm_num [delta, *]
            · have hae : a ≠ e := Ne.symm hea
              by_cases heb : e = b
              · subst e
                by_cases hfa : f = a
                · subst f
                  have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b b d b a i ∂gaussianReal 0 1) = 0 := by
                    apply Finset.prod_eq_zero (Finset.mem_univ b)
                    have he : mult6 a b b d b a b = 3 := by simp_all [mult6, eq_comm]
                    rw [he, gauss_int_pow_mgfPoly]
                    norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                  rw [hv]
                  norm_num [delta, *]
                · have haf : a ≠ f := Ne.symm hfa
                  by_cases hfb : f = b
                  · subst f
                    have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b b d b b i ∂gaussianReal 0 1) = 0 := by
                      apply Finset.prod_eq_zero (Finset.mem_univ a)
                      have he : mult6 a b b d b b a = 1 := by simp_all [mult6, eq_comm]
                      rw [he, gauss_int_pow_mgfPoly]
                      norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                    rw [hv]
                    norm_num [delta, *]
                  · have hbf : b ≠ f := Ne.symm hfb
                    by_cases hfd : f = d
                    · subst f
                      have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b b d b d i ∂gaussianReal 0 1) = 0 := by
                        apply Finset.prod_eq_zero (Finset.mem_univ a)
                        have he : mult6 a b b d b d a = 1 := by simp_all [mult6, eq_comm]
                        rw [he, gauss_int_pow_mgfPoly]
                        norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                      rw [hv]
                      norm_num [delta, *]
                    · have hdf : d ≠ f := Ne.symm hfd
                      have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b b d b f i ∂gaussianReal 0 1) = 0 := by
                        apply Finset.prod_eq_zero (Finset.mem_univ a)
                        have he : mult6 a b b d b f a = 1 := by simp_all [mult6, eq_comm]
                        rw [he, gauss_int_pow_mgfPoly]
                        norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                      rw [hv]
                      norm_num [delta, *]
              · have hbe : b ≠ e := Ne.symm heb
                by_cases hed : e = d
                · subst e
                  by_cases hfa : f = a
                  · subst f
                    have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b b d d a i ∂gaussianReal 0 1) = 1 := by
                      apply Finset.prod_eq_one
                      intro i _
                      all_goals by_cases hia : i = a
                      all_goals by_cases hib : i = b
                      all_goals by_cases hid : i = d
                      all_goals simp_all [mult6, eq_comm, gauss_int_pow_mgfPoly, gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                    rw [hv]
                    norm_num [delta, *]
                  · have haf : a ≠ f := Ne.symm hfa
                    by_cases hfb : f = b
                    · subst f
                      have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b b d d b i ∂gaussianReal 0 1) = 0 := by
                        apply Finset.prod_eq_zero (Finset.mem_univ a)
                        have he : mult6 a b b d d b a = 1 := by simp_all [mult6, eq_comm]
                        rw [he, gauss_int_pow_mgfPoly]
                        norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                      rw [hv]
                      norm_num [delta, *]
                    · have hbf : b ≠ f := Ne.symm hfb
                      by_cases hfd : f = d
                      · subst f
                        have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b b d d d i ∂gaussianReal 0 1) = 0 := by
                          apply Finset.prod_eq_zero (Finset.mem_univ a)
                          have he : mult6 a b b d d d a = 1 := by simp_all [mult6, eq_comm]
                          rw [he, gauss_int_pow_mgfPoly]
                          norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                        rw [hv]
                        norm_num [delta, *]
                      · have hdf : d ≠ f := Ne.symm hfd
                        have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b b d d f i ∂gaussianReal 0 1) = 0 := by
                          apply Finset.prod_eq_zero (Finset.mem_univ a)
                          have he : mult6 a b b d d f a = 1 := by simp_all [mult6, eq_comm]
                          rw [he, gauss_int_pow_mgfPoly]
                          norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                        rw [hv]
                        norm_num [delta, *]
                · have hde : d ≠ e := Ne.symm hed
                  by_cases hfa : f = a
                  · subst f
                    have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b b d e a i ∂gaussianReal 0 1) = 0 := by
                      apply Finset.prod_eq_zero (Finset.mem_univ d)
                      have he : mult6 a b b d e a d = 1 := by simp_all [mult6, eq_comm]
                      rw [he, gauss_int_pow_mgfPoly]
                      norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                    rw [hv]
                    norm_num [delta, *]
                  · have haf : a ≠ f := Ne.symm hfa
                    by_cases hfb : f = b
                    · subst f
                      have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b b d e b i ∂gaussianReal 0 1) = 0 := by
                        apply Finset.prod_eq_zero (Finset.mem_univ a)
                        have he : mult6 a b b d e b a = 1 := by simp_all [mult6, eq_comm]
                        rw [he, gauss_int_pow_mgfPoly]
                        norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                      rw [hv]
                      norm_num [delta, *]
                    · have hbf : b ≠ f := Ne.symm hfb
                      by_cases hfd : f = d
                      · subst f
                        have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b b d e d i ∂gaussianReal 0 1) = 0 := by
                          apply Finset.prod_eq_zero (Finset.mem_univ a)
                          have he : mult6 a b b d e d a = 1 := by simp_all [mult6, eq_comm]
                          rw [he, gauss_int_pow_mgfPoly]
                          norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                        rw [hv]
                        norm_num [delta, *]
                      · have hdf : d ≠ f := Ne.symm hfd
                        by_cases hfe : f = e
                        · subst f
                          have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b b d e e i ∂gaussianReal 0 1) = 0 := by
                            apply Finset.prod_eq_zero (Finset.mem_univ a)
                            have he : mult6 a b b d e e a = 1 := by simp_all [mult6, eq_comm]
                            rw [he, gauss_int_pow_mgfPoly]
                            norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                          rw [hv]
                          norm_num [delta, *]
                        · have hef : e ≠ f := Ne.symm hfe
                          have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b b d e f i ∂gaussianReal 0 1) = 0 := by
                            apply Finset.prod_eq_zero (Finset.mem_univ a)
                            have he : mult6 a b b d e f a = 1 := by simp_all [mult6, eq_comm]
                            rw [he, gauss_int_pow_mgfPoly]
                            norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                          rw [hv]
                          norm_num [delta, *]
      · have hbc : b ≠ c := Ne.symm hcb
        by_cases hda : d = a
        · subst d
          by_cases hea : e = a
          · subst e
            by_cases hfa : f = a
            · subst f
              have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b c a a a i ∂gaussianReal 0 1) = 0 := by
                apply Finset.prod_eq_zero (Finset.mem_univ b)
                have he : mult6 a b c a a a b = 1 := by simp_all [mult6, eq_comm]
                rw [he, gauss_int_pow_mgfPoly]
                norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
              rw [hv]
              norm_num [delta, *]
            · have haf : a ≠ f := Ne.symm hfa
              by_cases hfb : f = b
              · subst f
                have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b c a a b i ∂gaussianReal 0 1) = 0 := by
                  apply Finset.prod_eq_zero (Finset.mem_univ a)
                  have he : mult6 a b c a a b a = 3 := by simp_all [mult6, eq_comm]
                  rw [he, gauss_int_pow_mgfPoly]
                  norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                rw [hv]
                norm_num [delta, *]
              · have hbf : b ≠ f := Ne.symm hfb
                by_cases hfc : f = c
                · subst f
                  have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b c a a c i ∂gaussianReal 0 1) = 0 := by
                    apply Finset.prod_eq_zero (Finset.mem_univ a)
                    have he : mult6 a b c a a c a = 3 := by simp_all [mult6, eq_comm]
                    rw [he, gauss_int_pow_mgfPoly]
                    norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                  rw [hv]
                  norm_num [delta, *]
                · have hcf : c ≠ f := Ne.symm hfc
                  have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b c a a f i ∂gaussianReal 0 1) = 0 := by
                    apply Finset.prod_eq_zero (Finset.mem_univ a)
                    have he : mult6 a b c a a f a = 3 := by simp_all [mult6, eq_comm]
                    rw [he, gauss_int_pow_mgfPoly]
                    norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                  rw [hv]
                  norm_num [delta, *]
          · have hae : a ≠ e := Ne.symm hea
            by_cases heb : e = b
            · subst e
              by_cases hfa : f = a
              · subst f
                have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b c a b a i ∂gaussianReal 0 1) = 0 := by
                  apply Finset.prod_eq_zero (Finset.mem_univ a)
                  have he : mult6 a b c a b a a = 3 := by simp_all [mult6, eq_comm]
                  rw [he, gauss_int_pow_mgfPoly]
                  norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                rw [hv]
                norm_num [delta, *]
              · have haf : a ≠ f := Ne.symm hfa
                by_cases hfb : f = b
                · subst f
                  have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b c a b b i ∂gaussianReal 0 1) = 0 := by
                    apply Finset.prod_eq_zero (Finset.mem_univ b)
                    have he : mult6 a b c a b b b = 3 := by simp_all [mult6, eq_comm]
                    rw [he, gauss_int_pow_mgfPoly]
                    norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                  rw [hv]
                  norm_num [delta, *]
                · have hbf : b ≠ f := Ne.symm hfb
                  by_cases hfc : f = c
                  · subst f
                    have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b c a b c i ∂gaussianReal 0 1) = 1 := by
                      apply Finset.prod_eq_one
                      intro i _
                      all_goals by_cases hia : i = a
                      all_goals by_cases hib : i = b
                      all_goals by_cases hic : i = c
                      all_goals simp_all [mult6, eq_comm, gauss_int_pow_mgfPoly, gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                    rw [hv]
                    norm_num [delta, *]
                  · have hcf : c ≠ f := Ne.symm hfc
                    have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b c a b f i ∂gaussianReal 0 1) = 0 := by
                      apply Finset.prod_eq_zero (Finset.mem_univ c)
                      have he : mult6 a b c a b f c = 1 := by simp_all [mult6, eq_comm]
                      rw [he, gauss_int_pow_mgfPoly]
                      norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                    rw [hv]
                    norm_num [delta, *]
            · have hbe : b ≠ e := Ne.symm heb
              by_cases hec : e = c
              · subst e
                by_cases hfa : f = a
                · subst f
                  have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b c a c a i ∂gaussianReal 0 1) = 0 := by
                    apply Finset.prod_eq_zero (Finset.mem_univ a)
                    have he : mult6 a b c a c a a = 3 := by simp_all [mult6, eq_comm]
                    rw [he, gauss_int_pow_mgfPoly]
                    norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                  rw [hv]
                  norm_num [delta, *]
                · have haf : a ≠ f := Ne.symm hfa
                  by_cases hfb : f = b
                  · subst f
                    have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b c a c b i ∂gaussianReal 0 1) = 1 := by
                      apply Finset.prod_eq_one
                      intro i _
                      all_goals by_cases hia : i = a
                      all_goals by_cases hib : i = b
                      all_goals by_cases hic : i = c
                      all_goals simp_all [mult6, eq_comm, gauss_int_pow_mgfPoly, gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                    rw [hv]
                    norm_num [delta, *]
                  · have hbf : b ≠ f := Ne.symm hfb
                    by_cases hfc : f = c
                    · subst f
                      have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b c a c c i ∂gaussianReal 0 1) = 0 := by
                        apply Finset.prod_eq_zero (Finset.mem_univ b)
                        have he : mult6 a b c a c c b = 1 := by simp_all [mult6, eq_comm]
                        rw [he, gauss_int_pow_mgfPoly]
                        norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                      rw [hv]
                      norm_num [delta, *]
                    · have hcf : c ≠ f := Ne.symm hfc
                      have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b c a c f i ∂gaussianReal 0 1) = 0 := by
                        apply Finset.prod_eq_zero (Finset.mem_univ b)
                        have he : mult6 a b c a c f b = 1 := by simp_all [mult6, eq_comm]
                        rw [he, gauss_int_pow_mgfPoly]
                        norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                      rw [hv]
                      norm_num [delta, *]
              · have hce : c ≠ e := Ne.symm hec
                by_cases hfa : f = a
                · subst f
                  have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b c a e a i ∂gaussianReal 0 1) = 0 := by
                    apply Finset.prod_eq_zero (Finset.mem_univ a)
                    have he : mult6 a b c a e a a = 3 := by simp_all [mult6, eq_comm]
                    rw [he, gauss_int_pow_mgfPoly]
                    norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                  rw [hv]
                  norm_num [delta, *]
                · have haf : a ≠ f := Ne.symm hfa
                  by_cases hfb : f = b
                  · subst f
                    have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b c a e b i ∂gaussianReal 0 1) = 0 := by
                      apply Finset.prod_eq_zero (Finset.mem_univ c)
                      have he : mult6 a b c a e b c = 1 := by simp_all [mult6, eq_comm]
                      rw [he, gauss_int_pow_mgfPoly]
                      norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                    rw [hv]
                    norm_num [delta, *]
                  · have hbf : b ≠ f := Ne.symm hfb
                    by_cases hfc : f = c
                    · subst f
                      have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b c a e c i ∂gaussianReal 0 1) = 0 := by
                        apply Finset.prod_eq_zero (Finset.mem_univ b)
                        have he : mult6 a b c a e c b = 1 := by simp_all [mult6, eq_comm]
                        rw [he, gauss_int_pow_mgfPoly]
                        norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                      rw [hv]
                      norm_num [delta, *]
                    · have hcf : c ≠ f := Ne.symm hfc
                      by_cases hfe : f = e
                      · subst f
                        have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b c a e e i ∂gaussianReal 0 1) = 0 := by
                          apply Finset.prod_eq_zero (Finset.mem_univ b)
                          have he : mult6 a b c a e e b = 1 := by simp_all [mult6, eq_comm]
                          rw [he, gauss_int_pow_mgfPoly]
                          norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                        rw [hv]
                        norm_num [delta, *]
                      · have hef : e ≠ f := Ne.symm hfe
                        have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b c a e f i ∂gaussianReal 0 1) = 0 := by
                          apply Finset.prod_eq_zero (Finset.mem_univ b)
                          have he : mult6 a b c a e f b = 1 := by simp_all [mult6, eq_comm]
                          rw [he, gauss_int_pow_mgfPoly]
                          norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                        rw [hv]
                        norm_num [delta, *]
        · have had : a ≠ d := Ne.symm hda
          by_cases hdb : d = b
          · subst d
            by_cases hea : e = a
            · subst e
              by_cases hfa : f = a
              · subst f
                have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b c b a a i ∂gaussianReal 0 1) = 0 := by
                  apply Finset.prod_eq_zero (Finset.mem_univ a)
                  have he : mult6 a b c b a a a = 3 := by simp_all [mult6, eq_comm]
                  rw [he, gauss_int_pow_mgfPoly]
                  norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                rw [hv]
                norm_num [delta, *]
              · have haf : a ≠ f := Ne.symm hfa
                by_cases hfb : f = b
                · subst f
                  have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b c b a b i ∂gaussianReal 0 1) = 0 := by
                    apply Finset.prod_eq_zero (Finset.mem_univ b)
                    have he : mult6 a b c b a b b = 3 := by simp_all [mult6, eq_comm]
                    rw [he, gauss_int_pow_mgfPoly]
                    norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                  rw [hv]
                  norm_num [delta, *]
                · have hbf : b ≠ f := Ne.symm hfb
                  by_cases hfc : f = c
                  · subst f
                    have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b c b a c i ∂gaussianReal 0 1) = 1 := by
                      apply Finset.prod_eq_one
                      intro i _
                      all_goals by_cases hia : i = a
                      all_goals by_cases hib : i = b
                      all_goals by_cases hic : i = c
                      all_goals simp_all [mult6, eq_comm, gauss_int_pow_mgfPoly, gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                    rw [hv]
                    norm_num [delta, *]
                  · have hcf : c ≠ f := Ne.symm hfc
                    have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b c b a f i ∂gaussianReal 0 1) = 0 := by
                      apply Finset.prod_eq_zero (Finset.mem_univ c)
                      have he : mult6 a b c b a f c = 1 := by simp_all [mult6, eq_comm]
                      rw [he, gauss_int_pow_mgfPoly]
                      norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                    rw [hv]
                    norm_num [delta, *]
            · have hae : a ≠ e := Ne.symm hea
              by_cases heb : e = b
              · subst e
                by_cases hfa : f = a
                · subst f
                  have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b c b b a i ∂gaussianReal 0 1) = 0 := by
                    apply Finset.prod_eq_zero (Finset.mem_univ b)
                    have he : mult6 a b c b b a b = 3 := by simp_all [mult6, eq_comm]
                    rw [he, gauss_int_pow_mgfPoly]
                    norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                  rw [hv]
                  norm_num [delta, *]
                · have haf : a ≠ f := Ne.symm hfa
                  by_cases hfb : f = b
                  · subst f
                    have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b c b b b i ∂gaussianReal 0 1) = 0 := by
                      apply Finset.prod_eq_zero (Finset.mem_univ a)
                      have he : mult6 a b c b b b a = 1 := by simp_all [mult6, eq_comm]
                      rw [he, gauss_int_pow_mgfPoly]
                      norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                    rw [hv]
                    norm_num [delta, *]
                  · have hbf : b ≠ f := Ne.symm hfb
                    by_cases hfc : f = c
                    · subst f
                      have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b c b b c i ∂gaussianReal 0 1) = 0 := by
                        apply Finset.prod_eq_zero (Finset.mem_univ a)
                        have he : mult6 a b c b b c a = 1 := by simp_all [mult6, eq_comm]
                        rw [he, gauss_int_pow_mgfPoly]
                        norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                      rw [hv]
                      norm_num [delta, *]
                    · have hcf : c ≠ f := Ne.symm hfc
                      have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b c b b f i ∂gaussianReal 0 1) = 0 := by
                        apply Finset.prod_eq_zero (Finset.mem_univ a)
                        have he : mult6 a b c b b f a = 1 := by simp_all [mult6, eq_comm]
                        rw [he, gauss_int_pow_mgfPoly]
                        norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                      rw [hv]
                      norm_num [delta, *]
              · have hbe : b ≠ e := Ne.symm heb
                by_cases hec : e = c
                · subst e
                  by_cases hfa : f = a
                  · subst f
                    have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b c b c a i ∂gaussianReal 0 1) = 1 := by
                      apply Finset.prod_eq_one
                      intro i _
                      all_goals by_cases hia : i = a
                      all_goals by_cases hib : i = b
                      all_goals by_cases hic : i = c
                      all_goals simp_all [mult6, eq_comm, gauss_int_pow_mgfPoly, gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                    rw [hv]
                    norm_num [delta, *]
                  · have haf : a ≠ f := Ne.symm hfa
                    by_cases hfb : f = b
                    · subst f
                      have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b c b c b i ∂gaussianReal 0 1) = 0 := by
                        apply Finset.prod_eq_zero (Finset.mem_univ a)
                        have he : mult6 a b c b c b a = 1 := by simp_all [mult6, eq_comm]
                        rw [he, gauss_int_pow_mgfPoly]
                        norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                      rw [hv]
                      norm_num [delta, *]
                    · have hbf : b ≠ f := Ne.symm hfb
                      by_cases hfc : f = c
                      · subst f
                        have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b c b c c i ∂gaussianReal 0 1) = 0 := by
                          apply Finset.prod_eq_zero (Finset.mem_univ a)
                          have he : mult6 a b c b c c a = 1 := by simp_all [mult6, eq_comm]
                          rw [he, gauss_int_pow_mgfPoly]
                          norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                        rw [hv]
                        norm_num [delta, *]
                      · have hcf : c ≠ f := Ne.symm hfc
                        have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b c b c f i ∂gaussianReal 0 1) = 0 := by
                          apply Finset.prod_eq_zero (Finset.mem_univ a)
                          have he : mult6 a b c b c f a = 1 := by simp_all [mult6, eq_comm]
                          rw [he, gauss_int_pow_mgfPoly]
                          norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                        rw [hv]
                        norm_num [delta, *]
                · have hce : c ≠ e := Ne.symm hec
                  by_cases hfa : f = a
                  · subst f
                    have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b c b e a i ∂gaussianReal 0 1) = 0 := by
                      apply Finset.prod_eq_zero (Finset.mem_univ c)
                      have he : mult6 a b c b e a c = 1 := by simp_all [mult6, eq_comm]
                      rw [he, gauss_int_pow_mgfPoly]
                      norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                    rw [hv]
                    norm_num [delta, *]
                  · have haf : a ≠ f := Ne.symm hfa
                    by_cases hfb : f = b
                    · subst f
                      have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b c b e b i ∂gaussianReal 0 1) = 0 := by
                        apply Finset.prod_eq_zero (Finset.mem_univ a)
                        have he : mult6 a b c b e b a = 1 := by simp_all [mult6, eq_comm]
                        rw [he, gauss_int_pow_mgfPoly]
                        norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                      rw [hv]
                      norm_num [delta, *]
                    · have hbf : b ≠ f := Ne.symm hfb
                      by_cases hfc : f = c
                      · subst f
                        have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b c b e c i ∂gaussianReal 0 1) = 0 := by
                          apply Finset.prod_eq_zero (Finset.mem_univ a)
                          have he : mult6 a b c b e c a = 1 := by simp_all [mult6, eq_comm]
                          rw [he, gauss_int_pow_mgfPoly]
                          norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                        rw [hv]
                        norm_num [delta, *]
                      · have hcf : c ≠ f := Ne.symm hfc
                        by_cases hfe : f = e
                        · subst f
                          have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b c b e e i ∂gaussianReal 0 1) = 0 := by
                            apply Finset.prod_eq_zero (Finset.mem_univ a)
                            have he : mult6 a b c b e e a = 1 := by simp_all [mult6, eq_comm]
                            rw [he, gauss_int_pow_mgfPoly]
                            norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                          rw [hv]
                          norm_num [delta, *]
                        · have hef : e ≠ f := Ne.symm hfe
                          have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b c b e f i ∂gaussianReal 0 1) = 0 := by
                            apply Finset.prod_eq_zero (Finset.mem_univ a)
                            have he : mult6 a b c b e f a = 1 := by simp_all [mult6, eq_comm]
                            rw [he, gauss_int_pow_mgfPoly]
                            norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                          rw [hv]
                          norm_num [delta, *]
          · have hbd : b ≠ d := Ne.symm hdb
            by_cases hdc : d = c
            · subst d
              by_cases hea : e = a
              · subst e
                by_cases hfa : f = a
                · subst f
                  have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b c c a a i ∂gaussianReal 0 1) = 0 := by
                    apply Finset.prod_eq_zero (Finset.mem_univ a)
                    have he : mult6 a b c c a a a = 3 := by simp_all [mult6, eq_comm]
                    rw [he, gauss_int_pow_mgfPoly]
                    norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                  rw [hv]
                  norm_num [delta, *]
                · have haf : a ≠ f := Ne.symm hfa
                  by_cases hfb : f = b
                  · subst f
                    have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b c c a b i ∂gaussianReal 0 1) = 1 := by
                      apply Finset.prod_eq_one
                      intro i _
                      all_goals by_cases hia : i = a
                      all_goals by_cases hib : i = b
                      all_goals by_cases hic : i = c
                      all_goals simp_all [mult6, eq_comm, gauss_int_pow_mgfPoly, gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                    rw [hv]
                    norm_num [delta, *]
                  · have hbf : b ≠ f := Ne.symm hfb
                    by_cases hfc : f = c
                    · subst f
                      have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b c c a c i ∂gaussianReal 0 1) = 0 := by
                        apply Finset.prod_eq_zero (Finset.mem_univ b)
                        have he : mult6 a b c c a c b = 1 := by simp_all [mult6, eq_comm]
                        rw [he, gauss_int_pow_mgfPoly]
                        norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                      rw [hv]
                      norm_num [delta, *]
                    · have hcf : c ≠ f := Ne.symm hfc
                      have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b c c a f i ∂gaussianReal 0 1) = 0 := by
                        apply Finset.prod_eq_zero (Finset.mem_univ b)
                        have he : mult6 a b c c a f b = 1 := by simp_all [mult6, eq_comm]
                        rw [he, gauss_int_pow_mgfPoly]
                        norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                      rw [hv]
                      norm_num [delta, *]
              · have hae : a ≠ e := Ne.symm hea
                by_cases heb : e = b
                · subst e
                  by_cases hfa : f = a
                  · subst f
                    have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b c c b a i ∂gaussianReal 0 1) = 1 := by
                      apply Finset.prod_eq_one
                      intro i _
                      all_goals by_cases hia : i = a
                      all_goals by_cases hib : i = b
                      all_goals by_cases hic : i = c
                      all_goals simp_all [mult6, eq_comm, gauss_int_pow_mgfPoly, gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                    rw [hv]
                    norm_num [delta, *]
                  · have haf : a ≠ f := Ne.symm hfa
                    by_cases hfb : f = b
                    · subst f
                      have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b c c b b i ∂gaussianReal 0 1) = 0 := by
                        apply Finset.prod_eq_zero (Finset.mem_univ a)
                        have he : mult6 a b c c b b a = 1 := by simp_all [mult6, eq_comm]
                        rw [he, gauss_int_pow_mgfPoly]
                        norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                      rw [hv]
                      norm_num [delta, *]
                    · have hbf : b ≠ f := Ne.symm hfb
                      by_cases hfc : f = c
                      · subst f
                        have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b c c b c i ∂gaussianReal 0 1) = 0 := by
                          apply Finset.prod_eq_zero (Finset.mem_univ a)
                          have he : mult6 a b c c b c a = 1 := by simp_all [mult6, eq_comm]
                          rw [he, gauss_int_pow_mgfPoly]
                          norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                        rw [hv]
                        norm_num [delta, *]
                      · have hcf : c ≠ f := Ne.symm hfc
                        have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b c c b f i ∂gaussianReal 0 1) = 0 := by
                          apply Finset.prod_eq_zero (Finset.mem_univ a)
                          have he : mult6 a b c c b f a = 1 := by simp_all [mult6, eq_comm]
                          rw [he, gauss_int_pow_mgfPoly]
                          norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                        rw [hv]
                        norm_num [delta, *]
                · have hbe : b ≠ e := Ne.symm heb
                  by_cases hec : e = c
                  · subst e
                    by_cases hfa : f = a
                    · subst f
                      have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b c c c a i ∂gaussianReal 0 1) = 0 := by
                        apply Finset.prod_eq_zero (Finset.mem_univ b)
                        have he : mult6 a b c c c a b = 1 := by simp_all [mult6, eq_comm]
                        rw [he, gauss_int_pow_mgfPoly]
                        norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                      rw [hv]
                      norm_num [delta, *]
                    · have haf : a ≠ f := Ne.symm hfa
                      by_cases hfb : f = b
                      · subst f
                        have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b c c c b i ∂gaussianReal 0 1) = 0 := by
                          apply Finset.prod_eq_zero (Finset.mem_univ a)
                          have he : mult6 a b c c c b a = 1 := by simp_all [mult6, eq_comm]
                          rw [he, gauss_int_pow_mgfPoly]
                          norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                        rw [hv]
                        norm_num [delta, *]
                      · have hbf : b ≠ f := Ne.symm hfb
                        by_cases hfc : f = c
                        · subst f
                          have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b c c c c i ∂gaussianReal 0 1) = 0 := by
                            apply Finset.prod_eq_zero (Finset.mem_univ a)
                            have he : mult6 a b c c c c a = 1 := by simp_all [mult6, eq_comm]
                            rw [he, gauss_int_pow_mgfPoly]
                            norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                          rw [hv]
                          norm_num [delta, *]
                        · have hcf : c ≠ f := Ne.symm hfc
                          have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b c c c f i ∂gaussianReal 0 1) = 0 := by
                            apply Finset.prod_eq_zero (Finset.mem_univ a)
                            have he : mult6 a b c c c f a = 1 := by simp_all [mult6, eq_comm]
                            rw [he, gauss_int_pow_mgfPoly]
                            norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                          rw [hv]
                          norm_num [delta, *]
                  · have hce : c ≠ e := Ne.symm hec
                    by_cases hfa : f = a
                    · subst f
                      have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b c c e a i ∂gaussianReal 0 1) = 0 := by
                        apply Finset.prod_eq_zero (Finset.mem_univ b)
                        have he : mult6 a b c c e a b = 1 := by simp_all [mult6, eq_comm]
                        rw [he, gauss_int_pow_mgfPoly]
                        norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                      rw [hv]
                      norm_num [delta, *]
                    · have haf : a ≠ f := Ne.symm hfa
                      by_cases hfb : f = b
                      · subst f
                        have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b c c e b i ∂gaussianReal 0 1) = 0 := by
                          apply Finset.prod_eq_zero (Finset.mem_univ a)
                          have he : mult6 a b c c e b a = 1 := by simp_all [mult6, eq_comm]
                          rw [he, gauss_int_pow_mgfPoly]
                          norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                        rw [hv]
                        norm_num [delta, *]
                      · have hbf : b ≠ f := Ne.symm hfb
                        by_cases hfc : f = c
                        · subst f
                          have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b c c e c i ∂gaussianReal 0 1) = 0 := by
                            apply Finset.prod_eq_zero (Finset.mem_univ a)
                            have he : mult6 a b c c e c a = 1 := by simp_all [mult6, eq_comm]
                            rw [he, gauss_int_pow_mgfPoly]
                            norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                          rw [hv]
                          norm_num [delta, *]
                        · have hcf : c ≠ f := Ne.symm hfc
                          by_cases hfe : f = e
                          · subst f
                            have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b c c e e i ∂gaussianReal 0 1) = 0 := by
                              apply Finset.prod_eq_zero (Finset.mem_univ a)
                              have he : mult6 a b c c e e a = 1 := by simp_all [mult6, eq_comm]
                              rw [he, gauss_int_pow_mgfPoly]
                              norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                            rw [hv]
                            norm_num [delta, *]
                          · have hef : e ≠ f := Ne.symm hfe
                            have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b c c e f i ∂gaussianReal 0 1) = 0 := by
                              apply Finset.prod_eq_zero (Finset.mem_univ a)
                              have he : mult6 a b c c e f a = 1 := by simp_all [mult6, eq_comm]
                              rw [he, gauss_int_pow_mgfPoly]
                              norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                            rw [hv]
                            norm_num [delta, *]
            · have hcd : c ≠ d := Ne.symm hdc
              by_cases hea : e = a
              · subst e
                by_cases hfa : f = a
                · subst f
                  have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b c d a a i ∂gaussianReal 0 1) = 0 := by
                    apply Finset.prod_eq_zero (Finset.mem_univ a)
                    have he : mult6 a b c d a a a = 3 := by simp_all [mult6, eq_comm]
                    rw [he, gauss_int_pow_mgfPoly]
                    norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                  rw [hv]
                  norm_num [delta, *]
                · have haf : a ≠ f := Ne.symm hfa
                  by_cases hfb : f = b
                  · subst f
                    have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b c d a b i ∂gaussianReal 0 1) = 0 := by
                      apply Finset.prod_eq_zero (Finset.mem_univ c)
                      have he : mult6 a b c d a b c = 1 := by simp_all [mult6, eq_comm]
                      rw [he, gauss_int_pow_mgfPoly]
                      norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                    rw [hv]
                    norm_num [delta, *]
                  · have hbf : b ≠ f := Ne.symm hfb
                    by_cases hfc : f = c
                    · subst f
                      have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b c d a c i ∂gaussianReal 0 1) = 0 := by
                        apply Finset.prod_eq_zero (Finset.mem_univ b)
                        have he : mult6 a b c d a c b = 1 := by simp_all [mult6, eq_comm]
                        rw [he, gauss_int_pow_mgfPoly]
                        norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                      rw [hv]
                      norm_num [delta, *]
                    · have hcf : c ≠ f := Ne.symm hfc
                      by_cases hfd : f = d
                      · subst f
                        have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b c d a d i ∂gaussianReal 0 1) = 0 := by
                          apply Finset.prod_eq_zero (Finset.mem_univ b)
                          have he : mult6 a b c d a d b = 1 := by simp_all [mult6, eq_comm]
                          rw [he, gauss_int_pow_mgfPoly]
                          norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                        rw [hv]
                        norm_num [delta, *]
                      · have hdf : d ≠ f := Ne.symm hfd
                        have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b c d a f i ∂gaussianReal 0 1) = 0 := by
                          apply Finset.prod_eq_zero (Finset.mem_univ b)
                          have he : mult6 a b c d a f b = 1 := by simp_all [mult6, eq_comm]
                          rw [he, gauss_int_pow_mgfPoly]
                          norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                        rw [hv]
                        norm_num [delta, *]
              · have hae : a ≠ e := Ne.symm hea
                by_cases heb : e = b
                · subst e
                  by_cases hfa : f = a
                  · subst f
                    have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b c d b a i ∂gaussianReal 0 1) = 0 := by
                      apply Finset.prod_eq_zero (Finset.mem_univ c)
                      have he : mult6 a b c d b a c = 1 := by simp_all [mult6, eq_comm]
                      rw [he, gauss_int_pow_mgfPoly]
                      norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                    rw [hv]
                    norm_num [delta, *]
                  · have haf : a ≠ f := Ne.symm hfa
                    by_cases hfb : f = b
                    · subst f
                      have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b c d b b i ∂gaussianReal 0 1) = 0 := by
                        apply Finset.prod_eq_zero (Finset.mem_univ a)
                        have he : mult6 a b c d b b a = 1 := by simp_all [mult6, eq_comm]
                        rw [he, gauss_int_pow_mgfPoly]
                        norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                      rw [hv]
                      norm_num [delta, *]
                    · have hbf : b ≠ f := Ne.symm hfb
                      by_cases hfc : f = c
                      · subst f
                        have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b c d b c i ∂gaussianReal 0 1) = 0 := by
                          apply Finset.prod_eq_zero (Finset.mem_univ a)
                          have he : mult6 a b c d b c a = 1 := by simp_all [mult6, eq_comm]
                          rw [he, gauss_int_pow_mgfPoly]
                          norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                        rw [hv]
                        norm_num [delta, *]
                      · have hcf : c ≠ f := Ne.symm hfc
                        by_cases hfd : f = d
                        · subst f
                          have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b c d b d i ∂gaussianReal 0 1) = 0 := by
                            apply Finset.prod_eq_zero (Finset.mem_univ a)
                            have he : mult6 a b c d b d a = 1 := by simp_all [mult6, eq_comm]
                            rw [he, gauss_int_pow_mgfPoly]
                            norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                          rw [hv]
                          norm_num [delta, *]
                        · have hdf : d ≠ f := Ne.symm hfd
                          have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b c d b f i ∂gaussianReal 0 1) = 0 := by
                            apply Finset.prod_eq_zero (Finset.mem_univ a)
                            have he : mult6 a b c d b f a = 1 := by simp_all [mult6, eq_comm]
                            rw [he, gauss_int_pow_mgfPoly]
                            norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                          rw [hv]
                          norm_num [delta, *]
                · have hbe : b ≠ e := Ne.symm heb
                  by_cases hec : e = c
                  · subst e
                    by_cases hfa : f = a
                    · subst f
                      have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b c d c a i ∂gaussianReal 0 1) = 0 := by
                        apply Finset.prod_eq_zero (Finset.mem_univ b)
                        have he : mult6 a b c d c a b = 1 := by simp_all [mult6, eq_comm]
                        rw [he, gauss_int_pow_mgfPoly]
                        norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                      rw [hv]
                      norm_num [delta, *]
                    · have haf : a ≠ f := Ne.symm hfa
                      by_cases hfb : f = b
                      · subst f
                        have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b c d c b i ∂gaussianReal 0 1) = 0 := by
                          apply Finset.prod_eq_zero (Finset.mem_univ a)
                          have he : mult6 a b c d c b a = 1 := by simp_all [mult6, eq_comm]
                          rw [he, gauss_int_pow_mgfPoly]
                          norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                        rw [hv]
                        norm_num [delta, *]
                      · have hbf : b ≠ f := Ne.symm hfb
                        by_cases hfc : f = c
                        · subst f
                          have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b c d c c i ∂gaussianReal 0 1) = 0 := by
                            apply Finset.prod_eq_zero (Finset.mem_univ a)
                            have he : mult6 a b c d c c a = 1 := by simp_all [mult6, eq_comm]
                            rw [he, gauss_int_pow_mgfPoly]
                            norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                          rw [hv]
                          norm_num [delta, *]
                        · have hcf : c ≠ f := Ne.symm hfc
                          by_cases hfd : f = d
                          · subst f
                            have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b c d c d i ∂gaussianReal 0 1) = 0 := by
                              apply Finset.prod_eq_zero (Finset.mem_univ a)
                              have he : mult6 a b c d c d a = 1 := by simp_all [mult6, eq_comm]
                              rw [he, gauss_int_pow_mgfPoly]
                              norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                            rw [hv]
                            norm_num [delta, *]
                          · have hdf : d ≠ f := Ne.symm hfd
                            have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b c d c f i ∂gaussianReal 0 1) = 0 := by
                              apply Finset.prod_eq_zero (Finset.mem_univ a)
                              have he : mult6 a b c d c f a = 1 := by simp_all [mult6, eq_comm]
                              rw [he, gauss_int_pow_mgfPoly]
                              norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                            rw [hv]
                            norm_num [delta, *]
                  · have hce : c ≠ e := Ne.symm hec
                    by_cases hed : e = d
                    · subst e
                      by_cases hfa : f = a
                      · subst f
                        have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b c d d a i ∂gaussianReal 0 1) = 0 := by
                          apply Finset.prod_eq_zero (Finset.mem_univ b)
                          have he : mult6 a b c d d a b = 1 := by simp_all [mult6, eq_comm]
                          rw [he, gauss_int_pow_mgfPoly]
                          norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                        rw [hv]
                        norm_num [delta, *]
                      · have haf : a ≠ f := Ne.symm hfa
                        by_cases hfb : f = b
                        · subst f
                          have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b c d d b i ∂gaussianReal 0 1) = 0 := by
                            apply Finset.prod_eq_zero (Finset.mem_univ a)
                            have he : mult6 a b c d d b a = 1 := by simp_all [mult6, eq_comm]
                            rw [he, gauss_int_pow_mgfPoly]
                            norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                          rw [hv]
                          norm_num [delta, *]
                        · have hbf : b ≠ f := Ne.symm hfb
                          by_cases hfc : f = c
                          · subst f
                            have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b c d d c i ∂gaussianReal 0 1) = 0 := by
                              apply Finset.prod_eq_zero (Finset.mem_univ a)
                              have he : mult6 a b c d d c a = 1 := by simp_all [mult6, eq_comm]
                              rw [he, gauss_int_pow_mgfPoly]
                              norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                            rw [hv]
                            norm_num [delta, *]
                          · have hcf : c ≠ f := Ne.symm hfc
                            by_cases hfd : f = d
                            · subst f
                              have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b c d d d i ∂gaussianReal 0 1) = 0 := by
                                apply Finset.prod_eq_zero (Finset.mem_univ a)
                                have he : mult6 a b c d d d a = 1 := by simp_all [mult6, eq_comm]
                                rw [he, gauss_int_pow_mgfPoly]
                                norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                              rw [hv]
                              norm_num [delta, *]
                            · have hdf : d ≠ f := Ne.symm hfd
                              have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b c d d f i ∂gaussianReal 0 1) = 0 := by
                                apply Finset.prod_eq_zero (Finset.mem_univ a)
                                have he : mult6 a b c d d f a = 1 := by simp_all [mult6, eq_comm]
                                rw [he, gauss_int_pow_mgfPoly]
                                norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                              rw [hv]
                              norm_num [delta, *]
                    · have hde : d ≠ e := Ne.symm hed
                      by_cases hfa : f = a
                      · subst f
                        have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b c d e a i ∂gaussianReal 0 1) = 0 := by
                          apply Finset.prod_eq_zero (Finset.mem_univ b)
                          have he : mult6 a b c d e a b = 1 := by simp_all [mult6, eq_comm]
                          rw [he, gauss_int_pow_mgfPoly]
                          norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                        rw [hv]
                        norm_num [delta, *]
                      · have haf : a ≠ f := Ne.symm hfa
                        by_cases hfb : f = b
                        · subst f
                          have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b c d e b i ∂gaussianReal 0 1) = 0 := by
                            apply Finset.prod_eq_zero (Finset.mem_univ a)
                            have he : mult6 a b c d e b a = 1 := by simp_all [mult6, eq_comm]
                            rw [he, gauss_int_pow_mgfPoly]
                            norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                          rw [hv]
                          norm_num [delta, *]
                        · have hbf : b ≠ f := Ne.symm hfb
                          by_cases hfc : f = c
                          · subst f
                            have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b c d e c i ∂gaussianReal 0 1) = 0 := by
                              apply Finset.prod_eq_zero (Finset.mem_univ a)
                              have he : mult6 a b c d e c a = 1 := by simp_all [mult6, eq_comm]
                              rw [he, gauss_int_pow_mgfPoly]
                              norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                            rw [hv]
                            norm_num [delta, *]
                          · have hcf : c ≠ f := Ne.symm hfc
                            by_cases hfd : f = d
                            · subst f
                              have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b c d e d i ∂gaussianReal 0 1) = 0 := by
                                apply Finset.prod_eq_zero (Finset.mem_univ a)
                                have he : mult6 a b c d e d a = 1 := by simp_all [mult6, eq_comm]
                                rw [he, gauss_int_pow_mgfPoly]
                                norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                              rw [hv]
                              norm_num [delta, *]
                            · have hdf : d ≠ f := Ne.symm hfd
                              by_cases hfe : f = e
                              · subst f
                                have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b c d e e i ∂gaussianReal 0 1) = 0 := by
                                  apply Finset.prod_eq_zero (Finset.mem_univ a)
                                  have he : mult6 a b c d e e a = 1 := by simp_all [mult6, eq_comm]
                                  rw [he, gauss_int_pow_mgfPoly]
                                  norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                                rw [hv]
                                norm_num [delta, *]
                              · have hef : e ≠ f := Ne.symm hfe
                                have hv : (∏ i, ∫ x : ℝ, x ^ mult6 a b c d e f i ∂gaussianReal 0 1) = 0 := by
                                  apply Finset.prod_eq_zero (Finset.mem_univ a)
                                  have he : mult6 a b c d e f a = 1 := by simp_all [mult6, eq_comm]
                                  rw [he, gauss_int_pow_mgfPoly]
                                  norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]
                                rw [hv]
                                norm_num [delta, *]

end Paper10
