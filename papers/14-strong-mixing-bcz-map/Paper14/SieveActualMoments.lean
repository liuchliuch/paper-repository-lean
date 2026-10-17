import Paper14.SievePeriodTransfer
import Paper14.Chebyshev

open MeasureTheory ProbabilityTheory Filter Set Function Finset
open scoped ENNReal
namespace Paper14
noncomputable section

lemma sieveCircleSingle_add_q (M : ℕ) (q : ℤ) (ε : ℝ) (u : AddCircle (M : ℝ)) :
    sieveCircleSingle M q ε (u+((q : ℝ) : AddCircle (M : ℝ))) = sieveCircleSingle M q ε u := by
  induction u using Quotient.inductionOn with
  | _ u =>
    rw [← AddCircle.coe_add,sieveCircleSingle_coe,sieveCircleSingle_coe]
    exact (sieveSingle_periods M q ε).2 u

lemma sieveTorusSingle_unit_period (M : ℕ) (q : ℕ) (ε : ℝ)
    (θ c : AddCircle (M : ℝ)) :
    sieveTorusSingle M q ε (θ+((1 : ℝ) : AddCircle (M : ℝ)),c) = sieveTorusSingle M q ε (θ,c) := by
  unfold sieveTorusSingle
  have hq : (q : ℤ) • ((1 : ℝ) : AddCircle (M : ℝ)) = ((q : ℝ) : AddCircle (M : ℝ)) := by
    rw [← AddCircle.coe_zsmul,zsmul_eq_mul,mul_one,Int.cast_natCast]
  rw [smul_add,hq]
  have heq : (q : ℤ) • θ+((q : ℝ) : AddCircle (M : ℝ))-c =
      ((q : ℤ) • θ-c)+((q : ℝ) : AddCircle (M : ℝ)) := by abel
  rw [heq]
  exact congrArg (fun n : ℕ => (n : ℝ)) (sieveCircleSingle_add_q M (q : ℤ) ε _)

lemma sieveTorusCount_unit_period (M Q : ℕ) (ε : ℝ)
    (θ c : AddCircle (M : ℝ)) :
    sieveTorusCount M Q ε (θ+((1 : ℝ) : AddCircle (M : ℝ)),c) = sieveTorusCount M Q ε (θ,c) := by
  simp only [sieveTorusCount,Finset.sum_apply,sieveTorusSingle_unit_period]

/-- Exact equality of the actual original G_M with its torus variable on
real representatives; all integer coefficient ranges are retained. -/
lemma sieveTorusCount_real_eq_GM (M Q : ℕ) (ε θ c : ℝ) (hε : ε ≤ 1) :
    sieveTorusCount M Q ε ((θ : AddCircle (M : ℝ)),(c : AddCircle (M : ℝ))) = (GM M Q c θ ε : ℝ) := by
  rw [GM_eq_sum_sieveSingle M Q c θ ε hε,Nat.cast_sum,Int.Icc_eq_finset_map,Finset.sum_map]
  simp only [add_sub_cancel_right,Int.toNat_natCast]
  simp only [sieveTorusCount,Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro q hq
  simp [sieveTorusSingle,sieve_indicator_real_representatives,add_comm]

lemma measurable_sieveTorusCount (M : ℕ) [Fact (0 < (M : ℝ))] (Q : ℕ) (ε : ℝ) :
    Measurable (sieveTorusCount M Q ε) := by
  have heq : sieveTorusCount M Q ε = fun z => ∑ q ∈ Finset.range Q, sieveTorusSingle M (q+1) ε z := by
    funext z
    simp only [sieveTorusCount,Finset.sum_apply]
  rw [heq]
  exact Finset.measurable_sum (Finset.range Q) (fun q _ => measurable_sieveTorusSingle M (q+1) ε)

lemma sieveTorusCount_mem_Icc (M : ℕ) [Fact (0 < (M : ℝ))] (Q : ℕ) (ε : ℝ)
    (z : AddCircle (M : ℝ) × AddCircle (M : ℝ)) :
    sieveTorusCount M Q ε z ∈ Icc (0 : ℝ) Q := by
  simp only [sieveTorusCount,Finset.sum_apply]
  constructor
  · exact Finset.sum_nonneg (fun q _ => (sieveTorusSingle_mem_Icc M (q+1) ε z).1)
  · calc _ ≤ ∑ _q ∈ Finset.range Q, (1 : ℝ) :=
          Finset.sum_le_sum (fun q _ => (sieveTorusSingle_mem_Icc M (q+1) ε z).2)
         _ = _ := by simp

/-- Full original expectation formula (16), under the actual real
auxiliary probability and for the actual G_M. -/
theorem integral_GM_aux {M : ℕ} [Fact (0 < (M : ℝ))] (hM : Squarefree M)
    (Q : ℕ) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    (∫ z : ℝ × ℝ, (GM M Q z.2 z.1 ε : ℝ) ∂sieveAuxMeasure M) = betaN M Q ε := by
  have hbound (z) : ‖sieveTorusCount M Q ε z‖ ≤ (Q : ℝ) := by
    obtain ⟨hl,hu⟩ := sieveTorusCount_mem_Icc M Q ε z
    simpa only [Real.norm_eq_abs,abs_of_nonneg hl] using hu
  have hh := integral_sieve_aux_eq_torus M (sieveTorusCount M Q ε)
    (measurable_sieveTorusCount M Q ε) Q hbound (sieveTorusCount_unit_period M Q ε)
  simp only [sieveTorusCount_real_eq_GM M Q ε _ _ hε1] at hh
  exact hh.trans (integral_sieveTorusCount hM Q hε0 hε1)

/-- Full centered second-moment bound (16), under the actual auxiliary
probability; it is not an algebraic sum-of-means surrogate. -/
theorem integral_GM_aux_variance {M : ℕ} [Fact (0 < (M : ℝ))] (hM : Squarefree M)
    (Q : ℕ) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    (∫ z : ℝ × ℝ, ((GM M Q z.2 z.1 ε : ℝ)-betaN M Q ε)^2 ∂sieveAuxMeasure M) ≤ betaN M Q ε := by
  let β := betaN M Q ε
  let F : AddCircle (M : ℝ) × AddCircle (M : ℝ) → ℝ := fun z => (sieveTorusCount M Q ε z-β)^2
  have hF : Measurable F := ((measurable_sieveTorusCount M Q ε).sub_const β).pow_const 2
  have hbound (z) : ‖F z‖ ≤ ((Q : ℝ)+|β|)^2 := by
    obtain ⟨hl,hu⟩ := sieveTorusCount_mem_Icc M Q ε z
    rw [show ‖F z‖ = (sieveTorusCount M Q ε z-β)^2 by exact abs_of_nonneg (sq_nonneg _)]
    nlinarith [le_abs_self β,neg_abs_le β]
  have hh := integral_sieve_aux_eq_torus M F hF _ hbound
    (fun θ c => by dsimp [F]; rw [sieveTorusCount_unit_period])
  simp only [F,sieveTorusCount_real_eq_GM M Q ε _ _ hε1] at hh
  rw [hh]
  have hvar := variance_sieveTorusCount hM Q hε0 hε1
  rw [variance_eq_integral (measurable_sieveTorusCount M Q ε).aemeasurable,
    integral_sieveTorusCount hM Q hε0 hε1] at hvar
  exact hvar

/-- Chebyshev's bound for the actual finite-sieve count under the actual
auxiliary measure, with its mean and variance proved above. -/
theorem GM_aux_lower_tail {M : ℕ} [Fact (0 < (M : ℝ))] (hM : Squarefree M)
    (Q : ℕ) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hβ : 0 < betaN M Q ε) :
    sieveAuxMeasure M {z : ℝ × ℝ | (GM M Q z.2 z.1 ε : ℝ) < betaN M Q ε/2} ≤
      ENNReal.ofReal (4/betaN M Q ε) := by
  apply chebyshev_lower_tail _ hβ ?_ (integral_GM_aux_variance hM Q hε0 hε1)
  have heq : (fun z : ℝ × ℝ => (GM M Q z.2 z.1 ε : ℝ)) =
      (fun z : ℝ × ℝ => sieveTorusCount M Q ε
        ((z.1 : AddCircle (M : ℝ)),(z.2 : AddCircle (M : ℝ)))) := by
    funext z
    exact (sieveTorusCount_real_eq_GM M Q ε z.1 z.2 hε1).symm
  have hpair : Measurable (fun z : ℝ × ℝ =>
      ((z.1 : AddCircle (M : ℝ)),(z.2 : AddCircle (M : ℝ)))) :=
    (AddCircle.measurable_mk'.comp measurable_fst).prodMk (AddCircle.measurable_mk'.comp measurable_snd)
  have hG : Measurable (fun z : ℝ × ℝ => (GM M Q z.2 z.1 ε : ℝ)) := by
    rw [heq]
    exact (measurable_sieveTorusCount M Q ε).comp hpair
  apply integrable_of_measurable_bound ((hG.sub_const _).pow_const 2)
    (((Q : ℝ)+|betaN M Q ε|)^2)
  intro z
  have hh := sieveTorusCount_mem_Icc M Q ε
    ((z.1 : AddCircle (M : ℝ)),(z.2 : AddCircle (M : ℝ)))
  rw [sieveTorusCount_real_eq_GM M Q ε z.1 z.2 hε1] at hh
  obtain ⟨hl,hu⟩ := hh
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  nlinarith [le_abs_self (betaN M Q ε),neg_abs_le (betaN M Q ε)]

end
end Paper14
