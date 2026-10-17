import Paper14.EigenExclusion
import Paper14.PhiRSectionL2
import Paper14.InducedMeasure

open MeasureTheory Filter Topology Set Function
open scoped ENNReal NNReal
namespace Paper14
noncomputable section

/-- The eigenfunction approximation bound is uniform in the iterate. -/
theorem eigen_iterate_L2_error_le {A : Type*} [MeasurableSpace A] {μ : Measure A}
    {T : A → A} (hT : MeasurePreserving T μ μ) {f g : A → ℂ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) {eig : ℂ} (he : ‖eig‖=1)
    (heig : ∀ᵐ x ∂μ,g (T x)=eig*g x) (n : ℕ) :
    eLpNorm (fun x => f (T^[n] x)-eig^n*f x) 2 μ ≤
      2*eLpNorm (fun x => g x-f x) 2 μ := by
  let a : A → ℂ := fun x => f (T^[n] x)-g (T^[n] x)
  let b : A → ℂ := fun x => eig^n*(g x-f x)
  have ha : MemLp a 2 μ := (hf.sub hg).comp_measurePreserving (hT.iterate n)
  have hb : MemLp b 2 μ := (hg.sub hf).const_mul (eig^n)
  have hsplit : (fun x => f (T^[n] x)-eig^n*f x) =ᵐ[μ] a+b := by
    filter_upwards [eigen_iterate_ae hT heig n] with x hx
    dsimp [a,b]
    rw [hx]
    ring
  rw [eLpNorm_congr_ae hsplit]
  calc
    eLpNorm (a+b) 2 μ ≤ eLpNorm a 2 μ + eLpNorm b 2 μ :=
      eLpNorm_add_le ha.1 hb.1 (by norm_num)
    _ = eLpNorm (fun x => g x-f x) 2 μ + eLpNorm (fun x => g x-f x) 2 μ := by
      have hna : eLpNorm a 2 μ=eLpNorm (fun x => g x-f x) 2 μ := by
        change eLpNorm ((f-g) ∘ T^[n]) 2 μ = _
        rw [eLpNorm_comp_measurePreserving (hf.sub hg).1 (hT.iterate n)]
        have hneg : f-g=-(fun x => g x-f x) := by funext x; simp
        rw [hneg,eLpNorm_neg]
      have hnb : eLpNorm b 2 μ=eLpNorm (fun x => g x-f x) 2 μ := by
        change eLpNorm ((eig^n) • (fun x => g x-f x)) 2 μ = _
        rw [eLpNorm_const_smul]
        have heNN : ‖eig‖₊=1 := by apply NNReal.eq; exact he
        simp [enorm,heNN]
      rw [hna,hnb]
    _ = _ := by rw [two_mul]

lemma measurePreserving_phiRInv {r : ℝ} (hr : 0<r) (hr1 : r<1) :
    MeasurePreserving (phiRInv r) (mr r) m := by
  refine ⟨measurable_phiRInv r,?_⟩
  rw [← (measurePreserving_phiR r hr hr1).map_eq,
    Measure.map_map (measurable_phiRInv r) (measurable_phiR r)]
  have heq : phiRInv r ∘ phiR r =ᵐ[m] id := by
    filter_upwards [ae_mem_Omega] with x hx
    exact phiRInv_phiR hr hr1 hx
  rw [Measure.map_congr heq,Measure.map_id]

lemma phiRInv_inducedMap {r : ℝ} (hr : 0<r) (hr1 : r<1)
    {y : ℝ × ℝ} (hy : y∈Yr r) :
    phiRInv r (inducedMap B (Yr r) y)=B (phiRInv r y) := by
  have hx : phiRInv r y∈Omega := phiRInv_mem_Omega hr hr1 hy
  have hyx : phiR r (phiRInv r y)=y := phiR_phiRInv hr hr1 hy
  conv_lhs => rw [← hyx]
  rw [(phiR_first_return_point hr hr1 hx).1]
  exact phiRInv_phiR hr hr1 (B_mem_Omega hx)

/-- The exact original inequality (61), for every iterate and the actual section measure. -/
theorem eigen_section_L2_error_le {f : ℝ × ℝ → ℂ} (hf : Measurable f)
    (hb : ∀ x,‖f x‖≤1) {eig : ℂ} (he : ‖eig‖=1)
    (heig : ∀ᵐ x ∂m,f (B x)=eig*f x)
    {r : ℝ} (hr : (2 : ℝ)/3<r) (hr1 : r<1) (n : ℕ) :
    eLpNorm (fun y => f ((inducedMap B (Yr r))^[n] y)-eig^n*f y) 2 (mr r) ≤
      2*eLpNorm (fun y => f (phiRInv r y)-f y) 2 (mr r) := by
  have hr0 : 0<r := by linarith
  have hd : mr r≤(4 : ℝ≥0∞) • m := mr_le_four hr hr1
  letI : IsFiniteMeasure (mr r) := ⟨(hd univ).trans_lt (by norm_num [Measure.smul_apply,smul_eq_mul,ENNReal.smul_def])⟩
  have hY : ∀ᵐ y ∂mr r,y∈Yr r := by
    rw [mr_eq_normalizedRestriction hr0 hr1]
    exact (ae_restrict_mem (measurableSet_Yr r)).filter_mono Measure.smul_absolutelyContinuous.ae_le
  have hm : MeasurePreserving (inducedMap B (Yr r)) (mr r) (mr r) := by
    have hmp := ((measurePreserving_phiR r hr0 hr1).comp measurePreserving_B).comp
      (measurePreserving_phiRInv hr0 hr1)
    refine ⟨(measurable_inducedMap measurable_B (measurableSet_Yr r)),?_⟩
    calc
      Measure.map (inducedMap B (Yr r)) (mr r) =
          Measure.map ((phiR r ∘ B) ∘ phiRInv r) (mr r) := ?_
      _ = mr r := hmp.map_eq
    apply Measure.map_congr
    filter_upwards [hY] with y hy
    change inducedMap B (Yr r) y=phiR r (B (phiRInv r y))
    have hyx : phiR r (phiRInv r y)=y := phiR_phiRInv hr0 hr1 hy
    have hx : phiRInv r y∈Omega := phiRInv_mem_Omega hr0 hr1 hy
    rw [← (phiR_first_return_point hr0 hr1 hx).1,hyx]
  have hge : ∀ᵐ y ∂mr r,f (phiRInv r (inducedMap B (Yr r) y))=eig*f (phiRInv r y) := by
    filter_upwards [hY,(measurePreserving_phiRInv hr0 hr1).quasiMeasurePreserving.ae heig] with y hy heigy
    rw [phiRInv_inducedMap hr0 hr1 hy,heigy]
  have hfM : MemLp f 2 (mr r) := MemLp.of_bound hf.aestronglyMeasurable 1 (ae_of_all _ hb)
  have hgM : MemLp (fun y => f (phiRInv r y)) 2 (mr r) :=
    MemLp.of_bound (hf.comp (measurable_phiRInv r)).aestronglyMeasurable 1 (ae_of_all _ (fun y => hb _))
  exact eigen_iterate_L2_error_le hm hfM hgM he hge n

/-- The original vanishing L2 error remains valid with the growing exponent n. -/
theorem eigen_section_L2_error_tendsto {f : ℝ × ℝ → ℂ} (hf : Measurable f)
    (hb : ∀ x,‖f x‖≤1) {eig : ℂ} (he : ‖eig‖=1)
    (heig : ∀ᵐ x ∂m,f (B x)=eig*f x) {α : ℝ} (hα : 0<α) :
    Tendsto (fun n : ℕ => eLpNorm
      (fun y => f ((inducedMap B (Yr (bczScale n α)))^[n] y)-eig^n*f y)
      2 (mr (bczScale n α))) atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (by simpa using ENNReal.Tendsto.const_mul (a := (2 : ℝ≥0∞)) (bounded_phiRInv_L2_error hf hb hα) (Or.inr (by norm_num)))
    (Eventually.of_forall (fun _ => bot_le))
  filter_upwards [bczScale_eventually hα] with n hr
  exact eigen_section_L2_error_le hf hb he heig hr.1 hr.2 n

end
end Paper14
