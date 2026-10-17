import Paper32.Subdifferential

/-! # Positive scaling of the genuine subdifferentials

Every identity below is proved from the epsilon inequality or the actual
convergent-gradient/regular-subgradient sequences. No subdifferential identity
is assumed as an oracle hypothesis.
-/

open Set Filter Topology

namespace Paper32

lemma lin_smul_left (C : ℝ) (w u : Point) : lin (C • w) u = C * lin w u := by
  simp only [lin, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

/-- Positive scalar multiplication preserves the regular-subgradient inequality. -/
theorem frechet_scale_mem {f : Point → ℝ} {z w : Point} {C : ℝ} (hC : 0 < C)
    (hw : FrechetSubgradient f z w) :
    FrechetSubgradient (fun q => C * f q) z (C • w) := by
  intro ε hε
  obtain ⟨δ,hδ,hs⟩ := hw (ε / C) (div_pos hε hC)
  refine ⟨δ,hδ,?_⟩
  intro u hu
  have he : C * (ε / C) = ε := by field_simp
  have hid : C * (f z + lin w u - (ε / C) * ‖u‖) =
      C * f z + lin (C • w) u - ε * ‖u‖ := by
    rw [lin_smul_left]
    calc
      _ = C * f z + C * lin w u - (C * (ε / C)) * ‖u‖ := by ring
      _ = _ := by rw [he]
  rw [← hid]
  exact mul_le_mul_of_nonneg_left (hs u hu) hC.le

/-- Exact positive scaling, with the inverse-scaled coefficient explicit. -/
theorem frechet_scale_iff {f : Point → ℝ} {z W : Point} {C : ℝ} (hC : 0 < C) :
    FrechetSubgradient (fun q => C * f q) z W ↔
      FrechetSubgradient f z (C⁻¹ • W) := by
  constructor
  · intro hw
    have hh := frechet_scale_mem (inv_pos.mpr hC) hw
    have heq : (fun q => C⁻¹ * (C * f q)) = f := by
      funext q
      simp [← mul_assoc, hC.ne']
    rwa [heq] at hh
  · intro hw
    have hh := frechet_scale_mem hC hw
    simpa only [smul_smul, mul_inv_cancel₀ hC.ne', one_smul] using hh

theorem frechetSubdiff_scale {f : Point → ℝ} {z : Point} {C : ℝ} (hC : 0 < C) :
    frechetSubdiff (fun q => C * f q) z = (fun w => C • w) '' frechetSubdiff f z := by
  ext W
  constructor
  · intro hW
    refine ⟨C⁻¹ • W, (frechet_scale_iff hC).mp hW, ?_⟩
    simp only [smul_smul, mul_inv_cancel₀ hC.ne', one_smul]
  · rintro ⟨w,hw,rfl⟩
    exact frechet_scale_mem hC hw

/-- Actual limiting-subgradient sequences can be scaled term by term. -/
theorem limiting_scale_mem {f : Point → ℝ} {z w : Point} {C : ℝ} (hC : 0 < C)
    (hw : w ∈ limitingSubdiff f z) :
    C • w ∈ limitingSubdiff (fun q => C * f q) z := by
  obtain ⟨a,b,ha,hfa,hb,hd⟩ := hw
  exact ⟨a,fun n => C • b n,ha,hfa.const_mul C,hb.const_smul C,
    fun n => frechet_scale_mem hC (hd n)⟩

theorem limiting_scale_iff {f : Point → ℝ} {z W : Point} {C : ℝ} (hC : 0 < C) :
    W ∈ limitingSubdiff (fun q => C * f q) z ↔ C⁻¹ • W ∈ limitingSubdiff f z := by
  constructor
  · intro hw
    have hh := limiting_scale_mem (inv_pos.mpr hC) hw
    have heq : (fun q => C⁻¹ * (C * f q)) = f := by
      funext q
      simp [← mul_assoc, hC.ne']
    rwa [heq] at hh
  · intro hw
    have hh := limiting_scale_mem hC hw
    simpa only [smul_smul, mul_inv_cancel₀ hC.ne', one_smul] using hh

theorem limitingSubdiff_scale {f : Point → ℝ} {z : Point} {C : ℝ} (hC : 0 < C) :
    limitingSubdiff (fun q => C * f q) z = (fun w => C • w) '' limitingSubdiff f z := by
  ext W
  constructor
  · intro hW
    refine ⟨C⁻¹ • W, (limiting_scale_iff hC).mp hW, ?_⟩
    simp only [smul_smul, mul_inv_cancel₀ hC.ne', one_smul]
  · rintro ⟨w,hw,rfl⟩
    exact limiting_scale_mem hC hw

/-- Scaling an ordinary derivative scales its vector in the Euclidean pairing. -/
lemma hasFDerivAt_scale_gradient {f : Point → ℝ} {z w : Point} (C : ℝ)
    (hd : HasFDerivAt f (linCLM w) z) :
    HasFDerivAt (fun q => C * f q) (linCLM (C • w)) z := by
  convert hd.const_mul C using 1
  apply ContinuousLinearMap.ext
  intro u
  change lin (C • w) u = C * lin w u
  exact lin_smul_left C w u

/-- Reachable-gradient sequences scale without any regularity assumptions. -/
theorem gradientLimits_scale_mem {f : Point → ℝ} {z w : Point} (C : ℝ)
    (hw : w ∈ gradientLimits f z) : C • w ∈ gradientLimits (fun q => C * f q) z := by
  obtain ⟨a,b,ha,hb,hd⟩ := hw
  exact ⟨a,fun n => C • b n,ha,hb.const_smul C,
    fun n => hasFDerivAt_scale_gradient C (hd n)⟩

theorem gradientLimits_scale_iff {f : Point → ℝ} {z W : Point} {C : ℝ} (hC : C ≠ 0) :
    W ∈ gradientLimits (fun q => C * f q) z ↔ C⁻¹ • W ∈ gradientLimits f z := by
  constructor
  · intro hw
    have hh := gradientLimits_scale_mem C⁻¹ hw
    have heq : (fun q => C⁻¹ * (C * f q)) = f := by
      funext q
      simp [← mul_assoc, hC]
    rwa [heq] at hh
  · intro hw
    have hh := gradientLimits_scale_mem C hw
    simpa only [smul_smul, mul_inv_cancel₀ hC, one_smul] using hh

theorem gradientLimits_scale {f : Point → ℝ} {z : Point} {C : ℝ} (hC : C ≠ 0) :
    gradientLimits (fun q => C * f q) z = (fun w => C • w) '' gradientLimits f z := by
  ext W
  constructor
  · intro hW
    refine ⟨C⁻¹ • W, (gradientLimits_scale_iff hC).mp hW, ?_⟩
    simp only [smul_smul, mul_inv_cancel₀ hC, one_smul]
  · rintro ⟨w,hw,rfl⟩
    exact gradientLimits_scale_mem C hw

/-- Closed-convex-hull minimality propagates the actual gradient scaling to Clarke values. -/
theorem clarke_scale_mem {f : Point → ℝ} {z w : Point} (C : ℝ)
    (hw : w ∈ clarkeSubdiff f z) : C • w ∈ clarkeSubdiff (fun q => C * f q) z := by
  let S : Set Point := {u | C • u ∈ clarkeSubdiff (fun q => C * f q) z}
  have hclosed : IsClosed S := isClosed_closure.preimage (continuous_const_smul C)
  have hconv : Convex ℝ S := by
    intro a ha b hb s t hs ht hst
    change C • (s • a + t • b) ∈ clarkeSubdiff (fun q => C * f q) z
    have halg : C • (s • a + t • b) = s • (C • a) + t • (C • b) := by
      ext <;> simp only [Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add,
        smul_eq_mul] <;> ring
    rw [halg]
    exact (convex_convexHull ℝ (gradientLimits (fun q => C * f q) z)).closure ha hb hs ht hst
  have hbase : gradientLimits f z ⊆ S := by
    intro u hu
    exact subset_closure (subset_convexHull ℝ _ (gradientLimits_scale_mem C hu))
  exact closure_minimal (convexHull_min hbase hconv) hclosed hw

/-- Dividing a genuine Clarke oracle by a nonzero objective scaling is legitimate. -/
theorem clarke_scale_iff {f : Point → ℝ} {z W : Point} {C : ℝ} (hC : C ≠ 0) :
    W ∈ clarkeSubdiff (fun q => C * f q) z ↔ C⁻¹ • W ∈ clarkeSubdiff f z := by
  constructor
  · intro hw
    have hh := clarke_scale_mem C⁻¹ hw
    have heq : (fun q => C⁻¹ * (C * f q)) = f := by
      funext q
      simp [← mul_assoc, hC]
    rwa [heq] at hh
  · intro hw
    have hh := clarke_scale_mem C hw
    simpa only [smul_smul, mul_inv_cancel₀ hC, one_smul] using hh

theorem clarkeSubdiff_scale {f : Point → ℝ} {z : Point} {C : ℝ} (hC : C ≠ 0) :
    clarkeSubdiff (fun q => C * f q) z = (fun w => C • w) '' clarkeSubdiff f z := by
  ext W
  constructor
  · intro hW
    refine ⟨C⁻¹ • W, (clarke_scale_iff hC).mp hW, ?_⟩
    simp only [smul_smul, mul_inv_cancel₀ hC, one_smul]
  · rintro ⟨w,hw,rfl⟩
    exact clarke_scale_mem C hw

/-- Positive scaling preserves the Clarke--limiting criticality gap. -/
theorem criticality_gap_scale {f : Point → ℝ} {z : Point} {C : ℝ} (hC : 0 < C)
    (hc : (0 : Point) ∈ clarkeSubdiff f z) (hl : (0 : Point) ∉ limitingSubdiff f z) :
    (0 : Point) ∈ clarkeSubdiff (fun q => C * f q) z ∧
      (0 : Point) ∉ limitingSubdiff (fun q => C * f q) z := by
  constructor
  · simpa only [smul_zero] using clarke_scale_mem C hc
  · intro h
    apply hl
    simpa only [smul_zero] using (limiting_scale_iff hC).mp h

end Paper32
