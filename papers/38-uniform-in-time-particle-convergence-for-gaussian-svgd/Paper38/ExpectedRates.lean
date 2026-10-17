import Paper38.ProbabilityAssembly
import Paper38.Specification
import Paper38.GaussianCoupling
import Paper38.TransportGluing

/-! Own probability and last-iterate assembly. These lemmas name every needed
analytic estimate explicitly and do not relabel missing geometry as an external
statistical theorem. The actual main contracts remain in Specification. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace Paper38.ExpectedRates

/-- Any a.e. property can be made pointwise on a measurable probability-one
core. This justifies the common null-event extension in the source. -/
theorem measurable_core {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (p : Ω → Prop) (hp : ∀ᵐ ω ∂P, p ω) :
    ∃ H : Set Ω, MeasurableSet H ∧ P Hᶜ = 0 ∧ ∀ ω ∈ H, p ω := by
  obtain ⟨T, hTsub, hTm, hTzero⟩ :=
    exists_measurable_superset_of_null (show P {ω | ¬p ω} = 0 from hp)
  refine ⟨Tᶜ, hTm.compl, by simpa using hTzero, ?_⟩
  intro ω hω
  by_contra hn
  exact hω (hTsub hn)

/-- The source good/bad split is an integral proof, not discarding the bad event.
No measurability or integrability of the unbounded all-time error is assumed
for this nonnegative-integral inequality. -/
theorem good_bad_split {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (G : Set Ω) (hG : MeasurableSet G)
    (f U W : Ω → ℝ≥0∞) (hU : Measurable U) (a b u w tail : ℝ≥0∞)
    (ha : a ≠ ∞) (hb : b ≠ ∞)
    (hgood : ∀ ω ∈ G, f ω ≤ a * U ω + b * W ω)
    (hUbound : (∫⁻ ω in G, U ω ∂P) ≤ u)
    (hWbound : (∫⁻ ω, W ω ∂P) ≤ w)
    (hbad : (∫⁻ ω in Gᶜ, f ω ∂P) ≤ tail) :
    (∫⁻ ω, f ω ∂P) ≤ a * u + b * w + tail := by
  rw [← lintegral_add_compl f hG]
  apply add_le_add _ hbad
  calc
    (∫⁻ ω in G, f ω ∂P) ≤ ∫⁻ ω in G, a * U ω + b * W ω ∂P := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hG] with ω hω
      exact hgood ω hω
    _ = a * (∫⁻ ω in G, U ω ∂P) + b * (∫⁻ ω in G, W ω ∂P) := by
      rw [lintegral_add_left (measurable_const.mul hU),
        lintegral_const_mul' a _ ha, lintegral_const_mul' b _ hb]
    _ ≤ a * u + b * w := by
      exact add_le_add (mul_le_mul_left' hUbound a)
        (mul_le_mul_left' ((lintegral_mono' Measure.restrict_le_self (fun _ => le_rfl)).trans hWbound) b)

/-- The exact rate assembly in the final proof of Theorem2.2, with the three
constants independent of N. Its prerequisites are supplied by localization,
standardized shape, and the logarithmic-energy bad-event argument. -/
theorem good_bad_rate {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (G : Set Ω) (hG : MeasurableSet G)
    (f U W : Ω → ℝ≥0∞) (hU : Measurable U)
    (d N : ℕ) (hd : 1 ≤ d) (hN : 1 ≤ N)
    (a b M K L c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hM : 0 ≤ M) (hK : 0 ≤ K) (hL : 0 ≤ L) (hc : 0 < c)
    (hgood : ∀ ω ∈ G, f ω ≤ ENNReal.ofReal a * U ω + ENNReal.ofReal b * W ω)
    (hUbound : (∫⁻ ω in G, U ω ∂P) ≤ ENNReal.ofReal (M / N))
    (hWbound : (∫⁻ ω, W ω ∂P) ≤ ENNReal.ofReal (K * Model.rate d N))
    (hbad : (∫⁻ ω in Gᶜ, f ω ∂P) ≤ ENNReal.ofReal (L * Real.exp (-c * N))) :
    (∫⁻ ω, f ω ∂P) ≤
      ENNReal.ofReal ((a * M + b * K + L * c⁻¹) * Model.rate d N) := by
  have hr := Model.rate_pos d N hd hN
  have hNreal : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hmean : M / N ≤ M * Model.rate d N := by
    simpa only [div_eq_mul_inv] using
      mul_le_mul_of_nonneg_left (Model.inv_sampleSize_le_rate d N hd hN) hM
  have hexp := ProbabilityAssembly.exponential_le_rate d N hd hN c hc
  have hraw := good_bad_split P G hG f U W hU
    (ENNReal.ofReal a) (ENNReal.ofReal b) (ENNReal.ofReal (M / N))
    (ENNReal.ofReal (K * Model.rate d N)) (ENNReal.ofReal (L * Real.exp (-c * N)))
    (by simp) (by simp) hgood hUbound hWbound hbad
  calc
    _ ≤ _ := hraw
    _ = ENNReal.ofReal (a * (M / N) + b * (K * Model.rate d N) +
        L * Real.exp (-c * N)) := by
      rw [← ENNReal.ofReal_mul ha, ← ENNReal.ofReal_mul hb,
        ← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      have h1 := mul_le_mul_of_nonneg_left hmean ha
      have h2 := mul_le_mul_of_nonneg_left hexp hL
      nlinarith

/-- A physical-time estimate from the all-time expectation and deterministic
mean-field convergence. Both sides use the actual quadratic transport object. -/
theorem last_iterate {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {d N : ℕ} (hN : 0 < N) (X : Ω → Specification.ParticlePath d N)
    (p : Specification.MomentPath d) (target : Measure (Model.E d))
    [IsProbabilityMeasure target] (t : ℝ) (ht : 0 ≤ t)
    (A B : ℝ≥0∞)
    (hstat : (∫⁻ ω, Specification.pathSup (X ω) p ∂P) ≤ A)
    (hmean : Transport.w2sq (p.law t) target ≤ B) :
    (∫⁻ ω, Transport.w2sq (Model.empiricalLaw (X ω t)) target ∂P) ≤ 2 * A + 2 * B := by
  letI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  letI : IsProbabilityMeasure (p.law t) :=
    GaussianCoupling.gaussianLaw_probability _ _
  have hpoint : ∀ ω, Transport.w2sq (Model.empiricalLaw (X ω t)) target ≤
      2 * Specification.pathSup (X ω) p + 2 * B := by
    intro ω
    letI : IsProbabilityMeasure (Model.empiricalLaw (X ω t)) := by
      rw [GaussianCoupling.empiricalLaw_eq_transport_empirical hN]; infer_instance
    have htime : Specification.pathError (X ω) p t ≤ Specification.pathSup (X ω) p :=
      le_iSup (fun s : {s : ℝ // 0 ≤ s} => Specification.pathError (X ω) p s) ⟨t, ht⟩
    exact (Transport.w2sq_triangle (Model.empiricalLaw (X ω t)) (p.law t) target).trans
      (add_le_add (mul_le_mul_left' htime 2) (mul_le_mul_left' hmean 2))
  calc
    _ ≤ ∫⁻ ω, 2 * Specification.pathSup (X ω) p + 2 * B ∂P := lintegral_mono hpoint
    _ = 2 * (∫⁻ ω, Specification.pathSup (X ω) p ∂P) + 2 * B := by
      rw [lintegral_add_right _ measurable_const, lintegral_const_mul' 2 _ (by simp)]
      simp
    _ ≤ _ := add_le_add (mul_le_mul_left' hstat 2) le_rfl

end Paper38.ExpectedRates
