import Paper38.CompactEllipticity

/-! Semiglobal stability from genuine C² energy and positive smooth mobility. -/
noncomputable section
namespace Paper38.GradientStability
open Set InnerProductSpace
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- All constants in the semiglobal stability argument are constructed from
C² energy geometry, positive C¹ mobility and compact sublevels. No stability,
convergence, local contraction, ellipticity constant, or metric equivalence
estimate is a premise. -/
theorem semiglobal {F : E → ℝ} {P : E → E →L[ℝ] E} {Ω : Set E} {α R : ℝ}
    (hα : 0 < α) (hR : 0 ≤ R) (hΩ : IsOpen Ω) (hΩconv : Convex ℝ Ω)
    (hF : ContDiffOn ℝ 2 F Ω)
    (hH : ∀ x ∈ Ω, ∀ v : E, α * ‖v‖^2 ≤ (fderiv ℝ (fderiv ℝ F) x v) v)
    (hP : ContDiffOn ℝ 1 P Ω)
    (hPpos : ∀ x ∈ Ω, ∀ v : E, v ≠ 0 → 0 < ⟪v, P x v⟫_ℝ)
    (hcompact : ∀ c : ℝ, IsCompact {x | x ∈ Ω ∧ F x ≤ c})
    {z : E} (hz : z ∈ Ω) (hmin : ∀ x ∈ Ω, F z ≤ F x) :
    ∃ S > 0, ∃ T ≥ 0, ∃ k > 0, ∀ q r : ℝ → E,
      (∀ s, 0 ≤ s → HasDerivAt q (-(P (q s) (gradient F (q s)))) s) →
      (∀ s, 0 ≤ s → HasDerivAt r (-(P (r s) (gradient F (r s)))) s) →
      (∀ s, 0 ≤ s → q s ∈ Ω) → (∀ s, 0 ≤ s → r s ∈ Ω) →
      F (q 0)-F z ≤ R → F (r 0)-F z ≤ R →
      (∀ t, 0 ≤ t → ‖q t-r t‖ ≤ S * ‖q 0-r 0‖) ∧
      (∀ t, T ≤ t → ‖q t-r t‖ ≤ S * Real.exp (-k/2 * (t-T)) * ‖q 0-r 0‖) := by
  let G := gradient F
  let f : E → E := fun x => -(P x (G x))
  let J := fderiv ℝ f
  let H := GradientGeometry.hessianOperator F z
  let C : Set E := {x | x ∈ Ω ∧ F x ≤ F z+R}
  have hstrong := GradientGeometry.strongConvexGradientOn_of_second_fderiv_lower hΩ hΩconv hF hH
  have hcrit : G z = 0 := GradientGeometry.gradient_eq_zero_of_minimizer hΩ hz hmin
  have hG1 : ContDiffOn ℝ 1 G Ω := GradientGeometry.gradient_contDiffOn hΩ hF
  have hf1 : ContDiffOn ℝ 1 f Ω := (hP.clm_apply hG1).neg
  have hJat : ∀ x ∈ Ω, ContinuousAt J x := by
    intro x hx
    exact ((hf1.contDiffAt (hΩ.mem_nhds hx)).fderiv_right (m := 0) (by norm_num)).continuousAt
  have hdf : ∀ x ∈ Ω, HasFDerivAt f (J x) x := by
    intro x hx
    exact ((hf1.contDiffAt (hΩ.mem_nhds hx)).differentiableAt (by norm_num)).hasFDerivAt
  have hCΩ : C ⊆ Ω := fun _ hx => hx.1
  have hCcompact : IsCompact C := hcompact _
  have hCconv : Convex ℝ C :=
    (GradientGeometry.convexOn_of_strongConvexGradientOn hΩconv hα.le hstrong).convex_le _
  obtain ⟨p, hp, hpell⟩ := CompactEllipticity.exists_uniform_lower hCcompact
    (hP.continuousOn.mono hCΩ) (fun x hx => hPpos x hx.1)
  have hsingleton : ({z} : Set E) ⊆ Ω := by simpa using hz
  obtain ⟨pstar, hpstar, hpstarell⟩ := CompactEllipticity.exists_uniform_lower
    (K := {z}) isCompact_singleton (hP.continuousOn.mono hsingleton)
    (fun x hx => hPpos x (hsingleton hx))
  have hHz : ∀ v : E, α * ‖v‖^2 ≤ Stability.energy H v := by
    intro v
    have hi : Stability.energy H v = (fderiv ℝ (fderiv ℝ F) z v) v := by
      unfold Stability.energy
      calc
        ⟪v,H v⟫_ℝ = ⟪H v,v⟫_ℝ := real_inner_comm _ _
        _ = _ := GradientGeometry.hessianOperator_inner _ _ _ _
    rw [hi]
    exact hH z hz v
  have hsymm : ∀ u v : E, ⟪u,H v⟫_ℝ = ⟪v,H u⟫_ℝ := by
    intro u v
    calc
      ⟪u,H v⟫_ℝ = ⟪H v,u⟫_ℝ := real_inner_comm _ _
      _ = (fderiv ℝ (fderiv ℝ F) z v) u := GradientGeometry.hessianOperator_inner _ _ _ _
      _ = (fderiv ℝ (fderiv ℝ F) z u) v :=
        (hF.contDiffAt (hΩ.mem_nhds hz)).isSymmSndFDerivAt (by norm_num) v u
      _ = ⟪H u,v⟫_ℝ := (GradientGeometry.hessianOperator_inner _ _ _ _).symm
      _ = ⟪v,H u⟫_ℝ := real_inner_comm _ _
  let K := ‖H‖/α+1
  have hK : 1 ≤ K := by dsimp [K]; linarith [div_nonneg (norm_nonneg H) hα.le]
  have hquot : α * (‖H‖/α) = ‖H‖ := by field_simp
  have hKsq : ‖H‖/α ≤ K^2 := by
    have hn : 0 ≤ ‖H‖/α := div_nonneg (norm_nonneg _) hα.le
    dsimp [K]
    nlinarith [sq_nonneg (‖H‖/α)]
  have hKbound : ‖H‖ ≤ α*K^2 := by nlinarith [mul_le_mul_of_nonneg_left hKsq hα.le]
  have hupper : ∀ v : E, Stability.energy H v ≤ α * K^2 * ‖v‖^2 := by
    intro v
    calc
      Stability.energy H v ≤ ‖v‖ * ‖H v‖ := real_inner_le_norm _ _
      _ ≤ ‖v‖ * (‖H‖ * ‖v‖) := mul_le_mul_of_nonneg_left (H.le_opNorm v) (norm_nonneg _)
      _ = ‖H‖ * ‖v‖^2 := by ring
      _ ≤ α * K^2 * ‖v‖^2 := mul_le_mul_of_nonneg_right hKbound (sq_nonneg _)
  have hbase : ∀ v : E, ⟪v,H (J z v)⟫_ℝ ≤ -(pstar*α) * Stability.energy H v := by
    intro v
    exact Stability.critical_point_dissipativity
      ((hP.contDiffAt (hΩ.mem_nhds hz)).differentiableAt (by norm_num)).hasFDerivAt
      (GradientGeometry.gradient_hasFDerivAt
        (((hF.contDiffAt (hΩ.mem_nhds hz)).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)))
      hcrit hsymm hα.le hpstar.le hHz (hpstarell z (by simp)) v
  obtain ⟨S,hS,T,hT,hstable⟩ := EnergyDecay.semiglobal_from_gradient_geometry
    hΩconv hCcompact hCconv hCΩ H hsymm hα hp hR (mul_pos hpstar hα) hα hK
    hstrong hz hcrit
    (fun x hx => GradientGeometry.hasFDerivAt_gradient_repr
      ((hF.contDiffAt (hΩ.mem_nhds hx)).differentiableAt (by norm_num)))
    (fun x hx v => by
      by_cases hv : v = 0
      · simp [hv]
      · exact (hPpos x hx v hv).le)
    (fun x hx hFx => hpell x ⟨hx,by linarith⟩)
    (fun x hx hFx => ⟨hx,by linarith⟩)
    hdf (fun x hx => (hJat x hx.1).continuousWithinAt) (hJat z hz)
    hHz hupper hbase
  exact ⟨S,hS,T,hT,pstar*α,mul_pos hpstar hα,hstable⟩

end Paper38.GradientStability
