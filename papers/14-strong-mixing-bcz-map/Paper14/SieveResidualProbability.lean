import Paper14.SieveResidualExpectation

open MeasureTheory Set Function Filter Finset
namespace Paper14
noncomputable section

lemma primitive_single_le_sieve (M q : ℕ) (ε u : ℝ) :
    sieveSingle 0 (q : ℤ) ε u ≤ sieveSingle M (q : ℤ) ε u := by
  rw [sieveSingle_zero_modulus]
  by_cases hc : (Int.ceil u : ℝ) < u+ε ∧ IsCoprime (Int.ceil u) (q : ℤ)
  · have hfinite := hc.2.of_isCoprime_of_dvd_right (Int.gcd_dvd_left (q : ℤ) (Int.ofNat M))
    have hb : (Int.ceil u : ℝ) < u+ε ∧
        IsCoprime (Int.ceil u) ((Int.gcd (q : ℤ) (Int.ofNat M) : ℕ) : ℤ) := ⟨hc.1,hfinite⟩
    simp only [if_pos hc,sieveSingle,if_pos hb,le_refl]
  · simp only [if_neg hc]
    exact Nat.zero_le _

lemma GPrim_cast_le_GM (M Q : ℕ) (c θ ε : ℝ) (hε : ε ≤ 1) :
    (GPrim Q c θ ε : ℝ) ≤ (GM M Q c θ ε : ℝ) := by
  rw [GPrim_cast_sum_nat Q c θ ε hε,GM_cast_sum_nat M Q c θ ε hε]
  apply Finset.sum_le_sum
  intro q hq
  exact_mod_cast primitive_single_le_sieve M (q+1) ε (((q+1 : ℕ) : ℝ)*θ-c)

lemma measurable_GM_coordinates (M Q : ℕ) {ε : ℝ} (hε : ε ≤ 1) :
    Measurable (fun x : ℝ × ℝ => (GM M Q (cOf x) (thetaOf x) ε : ℝ)) := by
  change Measurable ((fun z : ℝ × ℝ => (GM M Q z.1 z.2 ε : ℝ)) ∘
    (fun x : ℝ × ℝ => (cOf x,thetaOf x)))
  have hn : Measurable (fun z : ℝ × ℝ => GM M Q z.1 z.2 ε) := measurable_GM M Q hε
  have hh : Measurable (fun z : ℝ × ℝ => (GM M Q z.1 z.2 ε : ℝ)) :=
    (measurable_of_countable (fun n : ℕ => (n : ℝ))).comp hn
  apply hh.comp
  unfold cOf thetaOf
  fun_prop

lemma integrable_GM_coordinates (M Q : ℕ) {ε : ℝ} (hε : ε ≤ 1) :
    Integrable (fun x : ℝ × ℝ => (GM M Q (cOf x) (thetaOf x) ε : ℝ)) m := by
  apply integrable_of_measurable_bound (measurable_GM_coordinates M Q hε) (Q : ℝ)
  intro x
  rw [Real.norm_eq_abs,abs_of_nonneg (Nat.cast_nonneg _)]
  exact GM_cast_le_Q M Q (cOf x) (thetaOf x) ε hε

lemma integrable_GPrim_coordinates (Q : ℕ) {ε : ℝ} (hε : ε ≤ 1) :
    Integrable (fun x : ℝ × ℝ => (GPrim Q (cOf x) (thetaOf x) ε : ℝ)) m := by
  have heq : (fun x : ℝ × ℝ => (GPrim Q (cOf x) (thetaOf x) ε : ℝ)) =
      (fun x : ℝ × ℝ => (GM 0 Q (cOf x) (thetaOf x) ε : ℝ)) := by
    funext x
    rw [GPrim_eq_GM_zero]
  rw [heq]
  exact integrable_GM_coordinates 0 Q hε

/-- Actual Markov remainder probability used in (20), with the source
residual expectation proved under m rather than assumed. -/
theorem sieve_residual_markov (P Q : ℕ) {ε β : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hβ : 0 < β) :
    m {x | β/2 ≤ (GM (primorial P) Q (cOf x) (thetaOf x) ε : ℝ)-
      (GPrim Q (cOf x) (thetaOf x) ε : ℝ)} ≤ ENNReal.ofReal (2*ε*(Q : ℝ)*SP P/β) := by
  let R : ℝ × ℝ → ℝ := fun x => (GM (primorial P) Q (cOf x) (thetaOf x) ε : ℝ)-
    (GPrim Q (cOf x) (thetaOf x) ε : ℝ)
  have hR : Integrable R m := (integrable_GM_coordinates (primorial P) Q hε1).sub (integrable_GPrim_coordinates Q hε1)
  have h0 : ∀ᵐ x ∂m, 0 ≤ R x := Eventually.of_forall (fun x =>
    sub_nonneg.mpr (GPrim_cast_le_GM (primorial P) Q (cOf x) (thetaOf x) ε hε1))
  have hm := mul_meas_ge_le_integral_of_nonneg (μ := m) h0 hR (β/2)
  have hb : m.real {x | β/2 ≤ R x} ≤ 2*ε*(Q : ℝ)*SP P/β := by
    have hi := hm.trans (integral_sieve_residual P Q hε0 hε1)
    apply (le_div_iff₀ hβ).mpr
    nlinarith
  rw [← ENNReal.ofReal_toReal (measure_ne_top m {x | β/2 ≤ R x})]
  exact ENNReal.ofReal_le_ofReal hb

end
end Paper14
