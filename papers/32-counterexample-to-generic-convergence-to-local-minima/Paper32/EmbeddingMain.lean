import Paper32.EmbeddingCalculus
import Paper32.Main
import Paper32.MeasureExtensions
import Paper32.IidRecursion
import Paper32.BorelSelection

open Set Filter Topology MeasureTheory ProbabilityTheory
noncomputable section
namespace Paper32

variable {ι : Type*} [Fintype ι]

/-- Pathwise Corollary 7.2 for an arbitrary actual full Clarke oracle. The
extra coordinates start at zero, as required by the source construction. -/
theorem pathwise_embedded_trapping {v : EmbeddedPoint ι} {γ : ℝ}
    (hv : embeddedU v) (hγlo : (1/2:ℝ) < γ) (hγhi : γ < 1)
    (z w ν : ℕ → EmbeddedPoint ι) (hinit : Dstar (z 0).1 ∧ (z 0).2=0)
    (hw : ∀ k, w k ∈ embeddedClarkeSubdiff (embeddedTilt v) (z k))
    (hν : ∀ k, |(ν k).1.1| ≤ 1/100 ∧ |(ν k).1.2| ≤ 1/100 ∧
      ∀ i, |(ν k).2 i| ≤ 1/100)
    (hrec : ∀ k, z (k+1)=z k-powerStep γ k • (w k+ν k))
    (havoid : ∀ k ≥ 1, (z k).1 ∉ singularArrangement ∧ ∀ i, (z k).2 i ≠ 0) :
    (∀ k, |(z (k+1)).1.1| ≤ (36/5)*powerStep γ k ∧
      |(z (k+1)).1.2| ≤ (39/10)*powerStep γ k ∧
      ∀ i, |(z (k+1)).2 i| ≤ (21/10)*powerStep γ k) ∧
    Tendsto z atTop (𝓝 0) := by
  have hbase := pathwise_coercive_trapping hv.1 hγlo hγhi
    (fun k => (z k).1) (fun k => (w k).1) (fun k => (ν k).1) hinit.1
    (fun k => embeddedClarke_projection (hw k))
    (fun k => ⟨(hν k).1,(hν k).2.1⟩)
    (fun k => by
      simpa only [Prod.fst_sub,Prod.smul_fst,Prod.fst_add] using (congrArg Prod.fst (hrec k)))
    (fun k hk => (havoid k hk).1)
  have hfirst : ∀ i, |(z 1).2 i| ≤ (101/50:ℝ)*powerStep γ 0 := by
    intro i
    have hwi := embeddedClarke_extra_bound (hw 0) i
    have hf := extraCoordinate_first_bound (powerStep_pos γ 0) hwi (hv.2 i) ((hν 0).2.2 i)
    have hr := congrArg (fun p : EmbeddedPoint ι => p.2 i) (hrec 0)
    have hz : (z 0).2 i = 0 := congrFun hinit.2 i
    simp only [Prod.snd_sub,Prod.smul_snd,Prod.snd_add,Pi.sub_apply,Pi.smul_apply,
      Pi.add_apply,smul_eq_mul,Nat.zero_add,hz] at hr
    rw [hr]
    convert hf.le using 1 <;> ring
  have he : ∀ k i, |(ν (k+1)).2 i-v.2 i| ≤ (1/50:ℝ) := by
    intro k i
    exact (extraCoordinate_error ((hν (k+1)).2.2 i) (hv.2 i)).le
  have hextra := embeddedExtra_powerStep hγlo hγhi
    (q:= fun k => (z k).2) (e:= fun k i => (ν k).2 i-v.2 i)
    (fun k i => (havoid (k+1) (by omega)).2 i) hfirst he (fun k i => by
      have hr := congrArg (fun p : EmbeddedPoint ι => p.2 i) (hrec (k+1))
      simp only [Prod.snd_sub,Prod.smul_snd,Prod.snd_add,Pi.sub_apply,Pi.smul_apply,
        Pi.add_apply,smul_eq_mul] at hr
      rw [embeddedClarke_extra_eq (hw (k+1)) i ((havoid (k+1) (by omega)).2 i)] at hr
      convert hr using 1 <;> ring)
  exact ⟨fun k => ⟨(hbase.1 k).1,(hbase.1 k).2,hextra.1 k⟩,
    by simpa using hbase.2.prodMk_nhds hextra.2⟩


/-- Corollary 7.2 with the actual full pre-noise sigma fields and full
absolutely continuous conditional noise law. -/
theorem embedded_trapping_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ]
    (m : ℕ → MeasurableSpace Ω) (hm : ∀ k, m k ≤ mΩ)
    {v : EmbeddedPoint ι} {γ : ℝ} (hv : embeddedU v)
    (hγlo : (1/2:ℝ) < γ) (hγhi : γ < 1)
    (z w ν : ℕ → Ω → EmbeddedPoint ι)
    (hzmeas : ∀ k, Measurable[m k] (z k))
    (hwmeas : ∀ k, Measurable[m k] (w k))
    (hνmeas : ∀ k, Measurable (ν k))
    (hinit : ∀ᵐ ω ∂μ, Dstar (z 0 ω).1 ∧ (z 0 ω).2=0)
    (hw : ∀ k, ∀ᵐ ω ∂μ, w k ω ∈ embeddedClarkeSubdiff (embeddedTilt v) (z k ω))
    (hν : ∀ k, ∀ᵐ ω ∂μ, |(ν k ω).1.1| ≤ 1/100 ∧ |(ν k ω).1.2| ≤ 1/100 ∧
      ∀ i, |(ν k ω).2 i| ≤ 1/100)
    (hac : ∀ k, ∀ᵐ ω ∂μ,
      ProbabilityTheory.condDistrib (ν k) (preNoiseObservation (m k)) μ
        (preNoiseObservation (m k) ω) ≪ (MeasureTheory.volume : MeasureTheory.Measure (EmbeddedPoint ι)))
    (hrec : ∀ k, ∀ᵐ ω ∂μ, z (k+1) ω=z k ω-powerStep γ k • (w k ω+ν k ω)) :
    (∀ᵐ ω ∂μ, (∀ k, |(z (k+1) ω).1.1| ≤ (36/5)*powerStep γ k ∧
      |(z (k+1) ω).1.2| ≤ (39/10)*powerStep γ k ∧
      ∀ i, |(z (k+1) ω).2 i| ≤ (21/10)*powerStep γ k) ∧
      Tendsto (fun k => z k ω) atTop (𝓝 0)) ∧
    μ (boundedOrbitEvent z \ localMinLimitEvent (embeddedTilt v) z)=1 := by
  have havoid := ae_forall_positive_embedded_avoidance_adapted μ m hm z w ν
    (powerStep γ) hzmeas hwmeas hνmeas
    (fun k => ne_of_gt (powerStep_pos γ k)) hac hrec
  have hall : ∀ᵐ ω ∂μ, (∀ k, |(z (k+1) ω).1.1| ≤ (36/5)*powerStep γ k ∧
      |(z (k+1) ω).1.2| ≤ (39/10)*powerStep γ k ∧
      ∀ i, |(z (k+1) ω).2 i| ≤ (21/10)*powerStep γ k) ∧
      Tendsto (fun k => z k ω) atTop (𝓝 0) := by
    filter_upwards [hinit,MeasureTheory.ae_all_iff.mpr hw,
      MeasureTheory.ae_all_iff.mpr hν,MeasureTheory.ae_all_iff.mpr hrec,havoid]
      with ω hω0 hωw hων hωrec hωavoid
    exact pathwise_embedded_trapping hv hγlo hγhi (fun k => z k ω)
      (fun k => w k ω) (fun k => ν k ω) hω0 hωw hων hωrec hωavoid
  exact ⟨hall,measure_bad_limit_eq_one μ (not_localMin_embeddedTilt hv)
    (hall.mono fun _ h => h.2)⟩

/-- Projection of actual limiting subgradients preserves the source's
non-limiting-critical origin in every dimension. -/
theorem embedded_origin_not_limiting {v : EmbeddedPoint ι} (hv : embeddedU v) :
    (0 : EmbeddedPoint ι) ∉ embeddedLimitingSubdiff (embeddedTilt v) 0 := by
  intro h
  exact (criticality_gap hv.1).2.1 (embeddedLimiting_projection h)


/-- The source's full-dimensional criticality gap. -/
theorem embedded_criticality_gap {v : EmbeddedPoint ι} (hv : embeddedU v) :
    (0:EmbeddedPoint ι) ∈ embeddedClarkeSubdiff (embeddedTilt v) 0 ∧
    (0:EmbeddedPoint ι) ∉ embeddedLimitingSubdiff (embeddedTilt v) 0 ∧
    ¬ IsLocalMin (embeddedTilt v) 0 := by
  refine ⟨embeddedClarke_product.mpr ⟨(criticality_gap hv.1).1,?_⟩,
    embedded_origin_not_limiting hv,not_localMin_embeddedTilt hv⟩
  intro i
  refine ⟨?_,by simp⟩
  simpa only [Prod.snd_zero,Pi.zero_apply,zero_add] using
    (hv.2 i).le.trans (by norm_num : (1/100:ℝ) ≤ 2)


/-- Corollary 7.2 for every fixed Borel Clarke selection, with the actual
IID uniform law on the full Euclidean ball and the actual defined recursion. -/
theorem iid_uniformEmbeddedBall_selected_trapping_ae
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {v : EmbeddedPoint ι} {γ : ℝ} (hv : embeddedU v)
    (hγlo : (1/2:ℝ) < γ) (hγhi : γ < 1)
    (selection : EmbeddedPoint ι → EmbeddedPoint ι) (hs : Measurable selection)
    (hselection : ∀ x, selection x ∈ embeddedClarkeSubdiff (embeddedTilt v) x)
    (noise : ℕ → Ω → EmbeddedPoint ι) (hnoise : ∀ k, Measurable (noise k))
    (hiid : iIndepFun noise μ)
    (huniform : ∀ k, pdf.IsUniform (noise k) (embeddedEuclideanBall ι (1/100)) μ volume) :
    let z := noisyRecursion 0 (powerStep γ) selection noise
    (∀ᵐ ω ∂μ, (∀ k, |(z (k+1) ω).1.1| ≤ (36/5)*powerStep γ k ∧
      |(z (k+1) ω).1.2| ≤ (39/10)*powerStep γ k ∧
      ∀ i, |(z (k+1) ω).2 i| ≤ (21/10)*powerStep γ k) ∧
      Tendsto (fun k => z k ω) atTop (𝓝 0)) ∧
    μ (boundedOrbitEvent z \ localMinLimitEvent (embeddedTilt v) z)=1 := by
  let z := noisyRecursion 0 (powerStep γ) selection noise
  apply embedded_trapping_ae μ (noisePastSigma noise)
    (fun k => (measurable_noisePast noise hnoise k).comap_le)
    hv hγlo hγhi z (fun k ω => selection (z k ω)) noise
  · exact measurable_noisyRecursion_adapted 0 (powerStep γ) selection hs noise
  · intro k
    exact hs.comp (measurable_noisyRecursion_adapted 0 (powerStep γ) selection hs noise k)
  · exact hnoise
  · exact Eventually.of_forall (fun _ => ⟨by norm_num [z,noisyRecursion,Dstar],rfl⟩)
  · exact fun k => Eventually.of_forall (fun ω => hselection (z k ω))
  · intro k
    filter_upwards [ae_coordinate_bounds_of_uniform_embeddedEuclideanBall μ
      (noise k) (hnoise k) (by norm_num : (0:ℝ) ≤ 1/100) (huniform k)] with ω hω
    exact ⟨hω.1.1,hω.1.2,hω.2⟩
  · exact iid_uniform_conditional_absolutelyContinuous μ volume noise hnoise hiid
      (embeddedEuclideanBall ι (1/100)) huniform
  · exact fun k => Eventually.of_forall (fun _ => rfl)

/-- An explicit fixed Borel full-dimensional Clarke selection. -/
def embeddedBorelClarkeSelection (v z : EmbeddedPoint ι) : EmbeddedPoint ι :=
  (borelClarkeSelection v.1 z.1,fun i => 2*Real.sign (z.2 i)-v.2 i)

theorem measurable_embeddedBorelClarkeSelection (v : EmbeddedPoint ι) :
    Measurable (embeddedBorelClarkeSelection v) := by
  have hsign : Measurable Real.sign := by
    exact Measurable.ite measurableSet_Iio measurable_const
      (Measurable.ite measurableSet_Ioi measurable_const measurable_const)
  apply Measurable.prodMk
  · exact (measurable_borelClarkeSelection v.1).comp measurable_fst
  · apply measurable_pi_lambda
    intro i
    exact (((hsign.comp ((measurable_pi_apply i).comp measurable_snd)).const_mul 2).sub measurable_const)

theorem embeddedBorelClarkeSelection_mem (v z : EmbeddedPoint ι) :
    embeddedBorelClarkeSelection v z ∈ embeddedClarkeSubdiff (embeddedTilt v) z := by
  apply embeddedClarke_product.mpr
  refine ⟨borelClarkeSelection_mem v.1 z.1,?_⟩
  intro i
  refine ⟨?_,fun _ => rfl⟩
  change |2*Real.sign (z.2 i)-v.2 i+v.2 i| ≤ 2
  rw [sub_add_cancel,abs_mul]
  have hsign : |Real.sign (z.2 i)| ≤ 1 := by
    by_cases hz : z.2 i=0
    · simp [hz]
    · exact (abs_sign_of_ne hz).le
  norm_num
  linarith

end Paper32
