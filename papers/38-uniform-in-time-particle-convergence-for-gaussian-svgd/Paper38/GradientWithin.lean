import Paper38.GradientStability

/-! Preserve the source's right-time-domain derivatives in the stability theorem. -/
noncomputable section
namespace Paper38.GradientWithin
open Set Real
open scoped InnerProductSpace Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Genuine energy trapping with exactly the source `Ici 0` derivative convention. -/
theorem energy_nonincreasing {F : E → ℝ} {G : E → E} {P : E → E →L[ℝ] E}
    {q : ℝ → E} {Ω : Set E} {t : ℝ} (ht : 0 ≤ t)
    (hF : ∀ x ∈ Ω, HasFDerivAt F (innerSL ℝ (G x)) x)
    (hP : ∀ x ∈ Ω, ∀ v : E, 0 ≤ ⟪v,P x v⟫_ℝ)
    (hqΩ : ∀ s, 0 ≤ s → q s ∈ Ω)
    (hq : ∀ s, 0 ≤ s → HasDerivWithinAt q (-(P (q s) (G (q s)))) (Ici 0) s) :
    F (q t) ≤ F (q 0) := by
  have hd : ∀ s, 0 ≤ s → HasDerivWithinAt (fun s => F (q s))
      (-⟪G (q s),P (q s) (G (q s))⟫_ℝ) (Ici 0) s := by
    intro s hs
    simpa using (hF _ (hqΩ s hs)).comp_hasDerivWithinAt s (hq s hs)
  have h := Stability.scalar_exp_bound (c := 0)
    (fun s hs => (hd s hs.1).continuousWithinAt.mono (fun u hu => hu.1))
    (fun s hs => (hd s hs.1).mono (fun u hu => hs.1.trans hu))
    (fun s hs => by simpa only [zero_mul] using neg_nonpos.mpr (hP _ (hqΩ s hs.1) _)) ht
  simpa using h

/-- Right-continuity passes a uniform estimate for positive shifts to the original
time, including time zero, without imposing values at negative times. -/
theorem norm_bound_of_positive_shifts {q r : ℝ → E} {t C : ℝ} (ht : 0 ≤ t)
    (hq : ContinuousOn q (Ici 0)) (hr : ContinuousOn r (Ici 0))
    (hbound : ∀ ε : ℝ, 0 < ε → ‖q (t+ε)-r (t+ε)‖ ≤ C*‖q ε-r ε‖) :
    ‖q t-r t‖ ≤ C*‖q 0-r 0‖ := by
  have hmap : MapsTo (fun ε : ℝ => t+ε) (Ici 0) (Ici 0) := fun _ hε => add_nonneg ht hε
  have hqt : ContinuousWithinAt (fun ε : ℝ => q (t+ε)) (Ici 0) 0 := by
    simpa using (hq t ht).comp_of_eq (continuousWithinAt_const.add continuousWithinAt_id) hmap (by simp)
  have hrt : ContinuousWithinAt (fun ε : ℝ => r (t+ε)) (Ici 0) 0 := by
    simpa using (hr t ht).comp_of_eq (continuousWithinAt_const.add continuousWithinAt_id) hmap (by simp)
  have hleft := ((hqt.sub hrt).norm).mono Ioi_subset_Ici_self
  have hright : ContinuousWithinAt (fun ε : ℝ => C*‖q ε-r ε‖) (Ioi 0) 0 :=
    (continuousWithinAt_const.mul (((hq 0 (le_refl (0:ℝ))).sub
      (hr 0 (le_refl (0:ℝ)))).norm)).mono Ioi_subset_Ici_self
  have h := ContinuousWithinAt.closure_le (s := Ioi (0:ℝ)) (x := 0)
    (by simp) hleft hright (fun ε hε => hbound ε hε)
  simpa only [add_zero] using h

/-- The full semiglobal estimate with the source's `HasDerivWithinAt ... (Ici 0)`
solutions. Positive shifts and right-continuity remove negative-time assumptions. -/
theorem semiglobal [FiniteDimensional ℝ E]
    {F : E → ℝ} {P : E → E →L[ℝ] E} {Ω : Set E} {α R : ℝ}
    (hα : 0 < α) (hR : 0 ≤ R) (hΩ : IsOpen Ω) (hΩconv : Convex ℝ Ω)
    (hF : ContDiffOn ℝ 2 F Ω)
    (hH : ∀ x ∈ Ω, ∀ v : E, α * ‖v‖^2 ≤ (fderiv ℝ (fderiv ℝ F) x v) v)
    (hP : ContDiffOn ℝ 1 P Ω)
    (hPpos : ∀ x ∈ Ω, ∀ v : E, v ≠ 0 → 0 < ⟪v,P x v⟫_ℝ)
    (hcompact : ∀ c : ℝ, IsCompact {x | x ∈ Ω ∧ F x ≤ c})
    {z : E} (hz : z ∈ Ω) (hmin : ∀ x ∈ Ω, F z ≤ F x) :
    ∃ S > 0, ∃ T ≥ 0, ∃ k > 0, ∀ q r : ℝ → E,
      (∀ s, 0 ≤ s → HasDerivWithinAt q (-(P (q s) (gradient F (q s)))) (Ici 0) s) →
      (∀ s, 0 ≤ s → HasDerivWithinAt r (-(P (r s) (gradient F (r s)))) (Ici 0) s) →
      (∀ s, 0 ≤ s → q s ∈ Ω) → (∀ s, 0 ≤ s → r s ∈ Ω) →
      F (q 0)-F z ≤ R → F (r 0)-F z ≤ R →
      (∀ t, 0 ≤ t → ‖q t-r t‖ ≤ S*‖q 0-r 0‖) ∧
      (∀ t, T ≤ t → ‖q t-r t‖ ≤ S*exp (-k/2*(t-T))*‖q 0-r 0‖) := by
  obtain ⟨S,hS,T,hT,k,hk,hstable⟩ := GradientStability.semiglobal
    hα hR hΩ hΩconv hF hH hP hPpos hcompact hz hmin
  refine ⟨S,hS,T,hT,k,hk,?_⟩
  intro q r hq hr hqΩ hrΩ hqi hri
  have hFderiv : ∀ x ∈ Ω, HasFDerivAt F (innerSL ℝ (gradient F x)) x := by
    intro x hx
    exact GradientGeometry.hasFDerivAt_gradient_repr
      ((hF.contDiffAt (hΩ.mem_nhds hx)).differentiableAt (by norm_num))
  have hP0 : ∀ x ∈ Ω, ∀ v : E, 0 ≤ ⟪v,P x v⟫_ℝ := by
    intro x hx v
    by_cases hv : v = 0
    · simp [hv]
    · exact (hPpos x hx v hv).le
  have hqcont : ContinuousOn q (Ici 0) := fun s hs => (hq s hs).continuousWithinAt
  have hrcont : ContinuousOn r (Ici 0) := fun s hs => (hr s hs).continuousWithinAt
  have hshift : ∀ ε : ℝ, 0 < ε →
      (∀ t, 0 ≤ t → ‖q (t+ε)-r (t+ε)‖ ≤ S*‖q ε-r ε‖) ∧
      (∀ t, T ≤ t → ‖q (t+ε)-r (t+ε)‖ ≤ S*exp (-k/2*(t-T))*‖q ε-r ε‖) := by
    intro ε hε
    have hs := hstable (fun t => q (t+ε)) (fun t => r (t+ε))
    simp only [zero_add] at hs
    apply hs
    · intro s hs
      have hpos : 0 < s+ε := by linarith
      have hd := (hq (s+ε) hpos.le).hasDerivAt (Ici_mem_nhds hpos)
      simpa using hd.hasFDerivAt.comp_hasDerivAt s ((hasDerivAt_id s).add_const ε)
    · intro s hs
      have hpos : 0 < s+ε := by linarith
      have hd := (hr (s+ε) hpos.le).hasDerivAt (Ici_mem_nhds hpos)
      simpa using hd.hasFDerivAt.comp_hasDerivAt s ((hasDerivAt_id s).add_const ε)
    · intro s hs; exact hqΩ _ (add_nonneg hs hε.le)
    · intro s hs; exact hrΩ _ (add_nonneg hs hε.le)
    · simpa only [zero_add] using
        (show F (q ε)-F z ≤ R from by linarith [energy_nonincreasing hε.le hFderiv hP0 hqΩ hq])
    · simpa only [zero_add] using
        (show F (r ε)-F z ≤ R from by linarith [energy_nonincreasing hε.le hFderiv hP0 hrΩ hr])
  constructor
  · intro t ht
    exact norm_bound_of_positive_shifts ht hqcont hrcont (fun ε hε => (hshift ε hε).1 t ht)
  · intro t ht
    exact norm_bound_of_positive_shifts (hT.trans ht) hqcont hrcont
      (fun ε hε => (hshift ε hε).2 t ht)

end Paper38.GradientWithin
