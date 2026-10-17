import Paper14.SieveTorusMoments
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory Set Function Filter
open scoped ENNReal
namespace Paper14
noncomputable section

lemma intervalIntegrable_of_measurable_bound {f : ℝ → ℝ} (hf : Measurable f)
    (C : ℝ) (hC : ∀ x, ‖f x‖ ≤ C) (a b : ℝ) : IntervalIntegrable f volume a b := by
  have hi (a b : ℝ) : IntegrableOn f (Ioc a b) := by
    letI : IsFiniteMeasure (volume.restrict (Ioc a b)) := ⟨by simp [Real.volume_Ioc]⟩
    exact integrable_of_measurable_bound hf C hC
  exact ⟨hi a b,hi b a⟩

/-- A function on the period-M circle that is also one-periodic has its
Haar probability mean on any unit real interval. -/
theorem integral_circle_prob_one_period (M : ℕ) [hM : Fact (0 < (M : ℝ))]
    (f : AddCircle (M : ℝ) → ℝ) (hf : Measurable f)
    (C : ℝ) (hC : ∀ x, ‖f x‖ ≤ C)
    (hp : ∀ x, f (x+((1 : ℝ) : AddCircle (M : ℝ))) = f x) :
    (∫ x, f x ∂sieveCircleProb M) = ∫ x in Ioc (0 : ℝ) 1, f x := by
  let g : ℝ → ℝ := fun x => f (x : AddCircle (M : ℝ))
  have hg : Measurable g := hf.comp AddCircle.measurable_mk'
  have hgp : Periodic g 1 := by
    intro x
    change f ((x+1 : ℝ) : AddCircle (M : ℝ)) = f (x : AddCircle (M : ℝ))
    rw [AddCircle.coe_add]
    exact hp _
  have hgi : ∀ a b, IntervalIntegrable g volume a b :=
    intervalIntegrable_of_measurable_bound hg C (fun x => hC _) 
  have hrep := AddCircle.integral_preimage (M : ℝ) 0 f
  simp only [zero_add] at hrep
  rw [sieveCircleProb,integral_smul_measure,← hrep]
  have hmult := hgp.intervalIntegral_add_zsmul_eq (M : ℤ) 0 hgi
  simp only [zero_add,zsmul_eq_mul,Int.cast_natCast,mul_one] at hmult
  rw [intervalIntegral.integral_of_le (by exact_mod_cast (le_of_lt hM.out)),
    intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hmult
  change (ENNReal.ofReal (M : ℝ))⁻¹.toReal • (∫ x in Ioc (0 : ℝ) (M : ℝ), g x) = _
  rw [hmult]
  simp only [ENNReal.toReal_inv,ENNReal.toReal_ofReal hM.out.le,smul_eq_mul]
  rw [← mul_assoc,inv_mul_cancel₀ hM.out.ne',one_mul]

/-- The real auxiliary probability in the proof of Lemma 5, in coordinate
order (theta,c). Half-open endpoint choices have Lebesgue-null differences. -/
def sieveAuxMeasure (M : ℕ) : Measure (ℝ × ℝ) :=
  (volume.restrict (Ioc (0 : ℝ) 1)).prod
    ((ENNReal.ofReal (M : ℝ))⁻¹ • volume.restrict (Ioc (0 : ℝ) (M : ℝ)))

instance sieveAuxMeasure_probability (M : ℕ) [hM : Fact (0 < (M : ℝ))] :
    IsProbabilityMeasure (sieveAuxMeasure M) := by
  constructor
  rw [sieveAuxMeasure,Measure.prod_apply MeasurableSet.univ]
  simp only [preimage_univ]
  rw [lintegral_const]
  simp only [preimage_univ,Measure.smul_apply,Measure.restrict_apply_univ,
    Real.volume_Ioc,sub_zero,ENNReal.ofReal_one,smul_eq_mul,mul_one]
  exact ENNReal.inv_mul_cancel (ne_of_gt (ENNReal.ofReal_pos.mpr hM.out)) ENNReal.ofReal_ne_top

/-- Bounded observable transfer from the Haar torus to the paper's
actual [0,1] x [0,M] auxiliary domain, using its extra unit period. -/
theorem integral_sieve_aux_eq_torus (M : ℕ) [hM : Fact (0 < (M : ℝ))]
    (F : AddCircle (M : ℝ) × AddCircle (M : ℝ) → ℝ) (hF : Measurable F)
    (C : ℝ) (hC : ∀ z, ‖F z‖ ≤ C)
    (hp : ∀ θ c, F (θ+((1 : ℝ) : AddCircle (M : ℝ)),c) = F (θ,c)) :
    (∫ z : ℝ × ℝ, F ((z.1 : AddCircle (M : ℝ)),(z.2 : AddCircle (M : ℝ))) ∂sieveAuxMeasure M) =
      ∫ z, F z ∂(sieveCircleProb M).prod (sieveCircleProb M) := by
  let G : AddCircle (M : ℝ) → ℝ := fun θ => ∫ c, F (θ,c) ∂sieveCircleProb M
  have hFI : Integrable F ((sieveCircleProb M).prod (sieveCircleProb M)) :=
    integrable_of_measurable_bound hF C hC
  have hG : Measurable G := hF.stronglyMeasurable.integral_prod_right'.measurable
  have hGb : ∀ θ, ‖G θ‖ ≤ C := by
    intro θ
    simpa [G] using norm_integral_le_of_norm_le_const (μ := sieveCircleProb M)
      (Eventually.of_forall (fun c => hC (θ,c)))
  have hGp : ∀ θ, G (θ+((1 : ℝ) : AddCircle (M : ℝ))) = G θ := by
    intro θ
    apply integral_congr_ae
    exact Eventually.of_forall (fun c => hp θ c)
  rw [integral_prod F hFI]
  change _ = ∫ θ, G θ ∂sieveCircleProb M
  rw [integral_circle_prob_one_period M G hG C hGb hGp]
  have hreal : Measurable (fun z : ℝ × ℝ =>
      F ((z.1 : AddCircle (M : ℝ)),(z.2 : AddCircle (M : ℝ)))) := hF.comp
        ((AddCircle.measurable_mk'.comp measurable_fst).prodMk (AddCircle.measurable_mk'.comp measurable_snd))
  have hrealI : Integrable (fun z : ℝ × ℝ =>
      F ((z.1 : AddCircle (M : ℝ)),(z.2 : AddCircle (M : ℝ)))) (sieveAuxMeasure M) :=
    integrable_of_measurable_bound hreal C (fun z => hC _)
  rw [sieveAuxMeasure,integral_prod _ hrealI]
  apply integral_congr_ae
  filter_upwards [] with θ
  rw [integral_smul_measure]
  change _ = ∫ c, F ((θ : AddCircle (M : ℝ)),c) ∂sieveCircleProb M
  rw [sieveCircleProb,integral_smul_measure]
  congr 1
  simpa only [zero_add] using AddCircle.integral_preimage (M : ℝ) 0
    (fun c => F ((θ : AddCircle (M : ℝ)),c))

end
end Paper14
