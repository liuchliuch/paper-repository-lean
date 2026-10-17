import Paper14.EigenNormalization
import Paper14.PhiRFunctionApproximation
import Paper14.ExactlyOneProbability

open MeasureTheory Filter Topology Set Function
open scoped NNReal ENNReal
namespace Paper14
noncomputable section

lemma eigen_iterate_ae {A : Type*} [MeasurableSpace A] {μ : Measure A} {T : A → A}
    (hT : MeasurePreserving T μ μ) {f : A → ℂ} {eig : ℂ}
    (heig : ∀ᵐ x ∂μ,f (T x)=eig*f x) (n : ℕ) :
    ∀ᵐ x ∂μ,f (T^[n] x)=eig^n*f x := by
  induction n with
  | zero => simp
  | succ n ih =>
    filter_upwards [ih,(hT.iterate n).quasiMeasurePreserving.ae heig] with x hx hxT
    rw [iterate_succ_apply',hxT,hx,pow_succ]
    ring

lemma phiR_induced_iterate {r : ℝ} (hr : 0<r) (hr1 : r<1) {x : ℝ × ℝ} (hx : x∈Omega) (n : ℕ) :
    (inducedMap B (Yr r))^[n] (phiR r x)=phiR r (B^[n] x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iterate_succ_apply',ih,(phiR_first_return_point hr hr1 (B_iterate_mem hx n)).1,iterate_succ_apply']

/-- A bounded unit eigenfunction cannot have a nontrivial eigenvalue, using the actual event (22). -/
theorem unit_eigenvalue_eq_one (hB : Ergodic B m) {f : ℝ × ℝ → ℂ}
    (hf : Measurable f) (hb : ∀ x,‖f x‖≤1) (hunit : ∀ᵐ x ∂m,‖f x‖=1)
    {eig : ℂ} (heigNorm : ‖eig‖=1) (heig : ∀ᵐ x ∂m,f (B x)=eig*f x) : eig=1 := by
  classical
  by_contra hneq
  obtain ⟨α,η,hα,hη,hextra⟩ := exactly_one_extra_of_ergodic hB
  let D : ℝ → ℕ → ℝ × ℝ → ℝ := fun r n y => ‖f ((inducedMap B (Yr r))^[n] y)-eig^n*f y‖
  let e : ℝ → ℝ × ℝ → ℝ := fun r x => ‖f (phiR r x)-f x‖
  have hemeas (r : ℝ) : Measurable (e r) := ((hf.comp (measurable_phiR r)).sub hf).norm
  have heb (r : ℝ) (x : ℝ × ℝ) : ‖e r x‖≤2 := by
    change ‖‖f (phiR r x)-f x‖‖≤2
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    exact (norm_sub_le _ _).trans (by nlinarith [hb (phiR r x),hb x])
  have heI (r : ℝ) : Integrable (e r) m := integrable_of_measurable_bound (hemeas r) 2 (heb r)
  have hDmeas (r : ℝ) (n : ℕ) : Measurable (D r n) :=
    ((hf.comp ((measurable_inducedMap measurable_B (measurableSet_Yr r)).iterate n)).sub
      (measurable_const.mul hf)).norm
  have hDb (r : ℝ) (n : ℕ) (x : ℝ × ℝ) : ‖D r n x‖≤2 := by
    change ‖‖f ((inducedMap B (Yr r))^[n] x)-eig^n*f x‖‖≤2
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    have hh := norm_sub_le (f ((inducedMap B (Yr r))^[n] x)) (eig^n*f x)
    rw [norm_mul,norm_pow,heigNorm,one_pow,one_mul] at hh
    nlinarith [hb ((inducedMap B (Yr r))^[n] x),hb x]
  let J : ℕ → ℝ := fun n => ∫ x,D (bczScale n α) n (phiR (bczScale n α) x) ∂m
  have hJupper : ∀ᶠ n : ℕ in atTop,J n≤2*(∫ x,e (bczScale n α) x ∂m) := by
    filter_upwards [bczScale_eventually hα] with n hr
    let r := bczScale n α
    have hr0 : 0<r := by dsimp [r]; linarith [hr.1]
    have hleftI : Integrable (fun x => D r n (phiR r x)) m :=
      integrable_of_measurable_bound ((hDmeas r n).comp (measurable_phiR r)) 2 (fun x => hDb r n _)
    have hecompI : Integrable (fun x => e r (B^[n] x)) m :=
      integrable_of_measurable_bound ((hemeas r).comp (measurable_B.iterate n)) 2 (fun x => heb r _)
    have hbound : J n≤(∫ x,e r (B^[n] x)+e r x ∂m) := by
      apply integral_mono_ae hleftI (hecompI.add (heI r))
      filter_upwards [ae_mem_Omega,eigen_iterate_ae measurePreserving_B heig n] with x hx hfx
      change ‖f ((inducedMap B (Yr r))^[n] (phiR r x))-eig^n*f (phiR r x)‖≤e r (B^[n] x)+e r x
      rw [phiR_induced_iterate hr0 hr.2 hx]
      have hh := norm_sub_le_norm_sub_add_norm_sub (f (phiR r (B^[n] x))) (f (B^[n] x)) (eig^n*f (phiR r x))
      rw [hfx,← mul_sub,norm_mul,norm_pow,heigNorm,one_pow,one_mul,norm_sub_rev (f x)] at hh
      simpa only [e,hfx] using hh
    rw [integral_add hecompI (heI r)] at hbound
    have hmap := integral_map (μ := m) (measurable_B.iterate n).aemeasurable (hemeas r).aestronglyMeasurable
    rw [(measurePreserving_B.iterate n).map_eq] at hmap
    rw [← hmap] at hbound
    linarith
  have hJlim : Tendsto J atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (by simpa only [mul_zero] using (bounded_phiR_L1_error hf hb hα).const_mul 2)
      (Eventually.of_forall (fun n => integral_nonneg (fun x => norm_nonneg _))) hJupper
  have hJlower : ∀ᶠ n : ℕ in atTop,η*‖eig-1‖≤J n := by
    filter_upwards [bczScale_eventually hα,hextra] with n hr hηn
    let r := bczScale n α
    let E := {y ∈ Yr r | Rn B (Yr r) n y=n+1}
    have hr0 : 0<r := by dsimp [r]; linarith [hr.1]
    have hdom : mr r≤(4 : ℝ≥0∞) • m := mr_le_four hr.1 hr.2
    letI : IsFiniteMeasure (mr r) := ⟨(hdom univ).trans_lt (by simp [Measure.smul_apply,smul_eq_mul])⟩
    have hAC : mr r ≪ m := Measure.absolutelyContinuous_of_le_smul hdom
    have hE : MeasurableSet E := (measurableSet_Yr r).inter
      ((measurable_Rn measurable_B (measurableSet_Yr r) n) (measurableSet_singleton (n+1)))
    have hDI : Integrable (D r n) (mr r) := integrable_of_measurable_bound (hDmeas r n) 2 (hDb r n)
    have hAE : ∀ᵐ y ∂mr r,y∈E → D r n y=‖eig-1‖ := by
      filter_upwards [(hunit.and (eigen_iterate_ae measurePreserving_B heig (n+1))).filter_mono hAC.ae_le] with y hy hyE
      change ‖f ((inducedMap B (Yr r))^[n] y)-eig^n*f y‖=‖eig-1‖
      rw [induced_iterate_eq,hyE.2,hy.2]
      have hh : eig^(n+1)*f y-eig^n*f y=eig^n*(eig-1)*f y := by rw [pow_succ]; ring
      rw [hh,norm_mul,norm_mul,norm_pow,heigNorm,one_pow,hy.1,one_mul,mul_one]
    have hlower : (mr r E).toReal*‖eig-1‖≤∫ y,D r n y ∂mr r := by
      have hm := integral_mono_ae ((integrable_const ‖eig-1‖).indicator hE) hDI (by
        filter_upwards [hAE] with y hy
        by_cases hyE : y∈E
        · rw [indicator_of_mem hyE,hy hyE]
        · rw [indicator_of_notMem hyE]; exact norm_nonneg _)
      rw [integral_indicator hE,setIntegral_const,smul_eq_mul] at hm
      exact hm
    have hmass : m E≤mr r E := by
      rw [mr_eq_normalizedRestriction hr0 hr.2,normalizedRestriction,Measure.smul_apply,smul_eq_mul,
        Measure.restrict_apply hE,inter_eq_self_of_subset_left (show E⊆Yr r from fun y hy => hy.1)]
      exact le_mul_of_one_le_left' (ENNReal.one_le_inv.mpr MeasureTheory.prob_le_one)
    have hmassR := ENNReal.toReal_mono (measure_ne_top (mr r) E) hmass
    have hmap := integral_map (μ := m) (measurable_phiR r).aemeasurable (hDmeas r n).aestronglyMeasurable
    rw [(measurePreserving_phiR r hr0 hr.2).map_eq] at hmap
    change η≤(m E).toReal at hηn
    change η*‖eig-1‖≤∫ x,D r n (phiR r x) ∂m
    rw [← hmap]
    exact (mul_le_mul_of_nonneg_right (hηn.trans hmassR) (norm_nonneg _)).trans hlower
  have hh : η*‖eig-1‖≤0 := ge_of_tendsto hJlim hJlower
  have hp : 0<η*‖eig-1‖ := mul_pos hη (norm_pos_iff.mpr (sub_ne_zero.mpr hneq))
  linarith

/-- The full Appendix A exclusion of nontrivial L2 eigenvalues, from explicit BCZ ergodicity. -/
theorem noNontrivialEigen_of_ergodic (hB : Ergodic B m) : NoNontrivialEigen := by
  intro eig heig
  obtain ⟨hne,f,hf,hf0,hfe⟩ := heig
  obtain ⟨hnorm,g,hg,hgb,hunit,hge⟩ := normalized_eigenfunction hB hf hf0 hfe
  exact hne (unit_eigenvalue_eq_one hB hg hgb hunit hnorm hge)

end
end Paper14
