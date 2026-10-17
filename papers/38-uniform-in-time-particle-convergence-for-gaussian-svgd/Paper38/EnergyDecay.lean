import Paper38.Stability

/-!
# Strong convexity and preconditioned gradient energy decay

The hypotheses below are the usual first-order strong-convexity inequality and
an actual Fréchet derivative represented by the gradient. Neither the PL bound
nor an energy or trajectory convergence estimate is an input.
-/

namespace Paper38.EnergyDecay

open Set Real
open scoped InnerProductSpace NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The standard first-order strong convexity inequality on a domain. -/
def StrongConvexGradientOn (F : E → ℝ) (G : E → E) (Ω : Set E) (α : ℝ) : Prop :=
  ∀ x ∈ Ω, ∀ y ∈ Ω,
    F x + ⟪G x, y-x⟫_ℝ + α/2 * ‖y-x‖^2 ≤ F y

/-- The Hessian lower bound on a convex domain implies the standard first-order
strong convexity inequality.  Both derivatives are actual Fréchet derivatives. -/
theorem strongConvexGradientOn_of_hessian_lower {F : E → ℝ} {G : E → E}
    {A : E → E →L[ℝ] E} {Ω : Set E} {α : ℝ} (hΩ : Convex ℝ Ω)
    (hF : ∀ x ∈ Ω, HasFDerivAt F (innerSL ℝ (G x)) x)
    (hG : ∀ x ∈ Ω, HasFDerivAt G (A x) x)
    (hA : ∀ x ∈ Ω, ∀ v : E, α * ‖v‖^2 ≤ ⟪v, A x v⟫_ℝ) :
    StrongConvexGradientOn F G Ω α := by
  intro x hx y hy
  let d := y-x
  let path : ℝ → E := fun s => x+s • d
  let b : ℝ → ℝ := fun s => ⟪G (path s), d⟫_ℝ
  have hpΩ : ∀ s ∈ Icc (0:ℝ) 1, path s ∈ Ω := by
    intro s hs
    have h := hΩ hx hy (sub_nonneg.mpr hs.2) hs.1 (by ring : (1-s)+s=1)
    convert h using 1 <;> simp [path, d, smul_sub, sub_smul] <;> module
  have hp : ∀ s : ℝ, HasDerivAt path d s := by
    intro s
    simpa only [one_smul] using ((hasDerivAt_id s).smul_const d).const_add x
  have hfd : ∀ s ∈ Icc (0:ℝ) 1,
      HasDerivAt (fun s => F (path s)) (b s) s := by
    intro s hs
    exact (hF _ (hpΩ s hs)).comp_hasDerivAt s (hp s)
  have hbd : ∀ s ∈ Icc (0:ℝ) 1,
      HasDerivAt b ⟪A (path s) d, d⟫_ℝ s := by
    intro s hs
    simpa only [b, Function.comp_apply, inner_zero_right, zero_add] using
      ((hG _ (hpΩ s hs)).comp_hasDerivAt s (hp s)).inner ℝ (hasDerivAt_const s d)
  have hline : ∀ s : ℝ, HasDerivAt (fun s => b 0 + α*‖d‖^2*s) (α*‖d‖^2) s := by
    intro s
    simpa using ((hasDerivAt_id s).const_mul (α*‖d‖^2)).const_add (b 0)
  have hfirst := image_le_of_deriv_right_le_deriv_boundary
    (f := fun s => b 0 + α*‖d‖^2*s) (f' := fun _ => α*‖d‖^2)
    (fun s _ => (hline s).continuousAt.continuousWithinAt)
    (fun s _ => (hline s).hasDerivWithinAt)
    (B := b) (B' := fun s => ⟪A (path s) d, d⟫_ℝ)
    (by simp) (fun s hs => (hbd s hs).continuousAt.continuousWithinAt)
    (fun s hs => (hbd s ⟨hs.1, hs.2.le⟩).hasDerivWithinAt)
    (fun s hs => by
      have hcomm : ⟪A (path s) d, d⟫_ℝ = ⟪d, A (path s) d⟫_ℝ := real_inner_comm _ _
      dsimp only
      rw [hcomm]
      exact hA _ (hpΩ s ⟨hs.1, hs.2.le⟩) d)
  have hquad : ∀ s : ℝ,
      HasDerivAt (fun s => F x+s*b 0+α/2*‖d‖^2*s^2) (b 0+α*‖d‖^2*s) s := by
    intro s
    convert (((hasDerivAt_id s).mul_const (b 0)).const_add (F x)).add
      (((hasDerivAt_id s).pow 2).const_mul (α/2*‖d‖^2)) using 1 <;> simp <;> ring
  have hsecond := image_le_of_deriv_right_le_deriv_boundary
    (f := fun s => F x+s*b 0+α/2*‖d‖^2*s^2)
    (f' := fun s => b 0+α*‖d‖^2*s)
    (fun s _ => (hquad s).continuousAt.continuousWithinAt)
    (fun s _ => (hquad s).hasDerivWithinAt)
    (B := fun s => F (path s)) (B' := b)
    (by simp [path]) (fun s hs => (hfd s hs).continuousAt.continuousWithinAt)
    (fun s hs => (hfd s ⟨hs.1, hs.2.le⟩).hasDerivWithinAt)
    (fun s hs => hfirst ⟨hs.1, hs.2.le⟩)
    (x := 1) (by simp)
  simpa [b, path, d] using hsecond

/-- Strong convexity at a critical point gives the lower quadratic energy bound. -/
theorem distance_coercivity {F : E → ℝ} {G : E → E} {Ω : Set E} {α : ℝ}
    (hstrong : StrongConvexGradientOn F G Ω α) {z x : E}
    (hz : z ∈ Ω) (hx : x ∈ Ω) (hcrit : G z = 0) :
    α/2 * ‖x-z‖^2 ≤ F x-F z := by
  have h := hstrong z hz x hx
  simp only [hcrit, inner_zero_left, add_zero] at h
  linarith

/-- The Polyak--Łojasiewicz bound (4.15), proved from strong convexity using
Cauchy--Schwarz and completion of a scalar square. -/
theorem polyak_lojasiewicz {F : E → ℝ} {G : E → E} {Ω : Set E} {α : ℝ}
    (hα : 0 < α) (hstrong : StrongConvexGradientOn F G Ω α) {z x : E}
    (hz : z ∈ Ω) (hx : x ∈ Ω) :
    2*α * (F x-F z) ≤ ‖G x‖^2 := by
  have h := hstrong x hx z hz
  have hcs := (abs_le.mp (abs_real_inner_le_norm (G x) (z-x))).1
  have hgap : F x-F z ≤ ‖G x‖ * ‖z-x‖ - α/2 * ‖z-x‖^2 := by linarith
  have hmul := mul_le_mul_of_nonneg_left hgap (by positivity : 0 ≤ 2*α)
  nlinarith [sq_nonneg (‖G x‖ - α*‖z-x‖)]

/-- Exact energy dissipation for an actual trajectory of `q'=-P(q)G(q)`. -/
theorem hasDerivAt_energy {F : E → ℝ} {G : E → E}
    {P : E → E →L[ℝ] E} {q : ℝ → E} {t : ℝ}
    (hF : HasFDerivAt F (innerSL ℝ (G (q t))) (q t))
    (hq : HasDerivAt q (-(P (q t) (G (q t)))) t) :
    HasDerivAt (fun s => F (q s)) (-⟪G (q t), P (q t) (G (q t))⟫_ℝ) t := by
  simpa using hF.comp_hasDerivAt t hq

/-- Energy decay (4.13) for the preconditioned gradient ODE, derived from
strong convexity and mobility ellipticity along the trajectory. -/
theorem energy_exponential_decay {F : E → ℝ} {G : E → E}
    {P : E → E →L[ℝ] E} {q : ℝ → E} {Ω : Set E} {z : E}
    {α p t : ℝ} (hα : 0 < α) (hp : 0 ≤ p) (ht : 0 ≤ t)
    (hstrong : StrongConvexGradientOn F G Ω α) (hz : z ∈ Ω)
    (hF : ∀ x ∈ Ω, HasFDerivAt F (innerSL ℝ (G x)) x)
    (hq : ∀ s ∈ Icc 0 t, HasDerivAt q (-(P (q s) (G (q s)))) s)
    (hqΩ : ∀ s ∈ Icc 0 t, q s ∈ Ω)
    (hP : ∀ s ∈ Icc 0 t, ∀ v : E, p * ‖v‖^2 ≤ ⟪v, P (q s) v⟫_ℝ) :
    F (q t)-F z ≤ (F (q 0)-F z) * exp (-2*α*p*t) := by
  have hderiv : ∀ s ∈ Icc 0 t,
      HasDerivAt (fun s => F (q s)-F z)
        (-⟪G (q s), P (q s) (G (q s))⟫_ℝ) s := by
    intro s hs
    exact (hasDerivAt_energy (hF _ (hqΩ s hs)) (hq s hs)).sub_const (F z)
  have hbound : ∀ s ∈ Ico 0 t,
      -⟪G (q s), P (q s) (G (q s))⟫_ℝ ≤ (-2*α*p) * (F (q s)-F z) := by
    intro s hs
    have hpl := polyak_lojasiewicz hα hstrong hz (hqΩ s ⟨hs.1, hs.2.le⟩)
    have hell := hP s ⟨hs.1, hs.2.le⟩ (G (q s))
    have hmul := mul_le_mul_of_nonneg_left hpl hp
    nlinarith
  simpa only [sub_zero, mul_assoc] using Stability.scalar_exp_bound
    (fun s hs => (hderiv s hs).continuousAt.continuousWithinAt)
    (fun s hs => (hderiv s ⟨hs.1, hs.2.le⟩).hasDerivWithinAt) hbound ht

/-- A trajectory satisfying the actual preconditioned gradient ODE cannot leave
its initial energy sublevel while it stays in the gradient domain. -/
theorem sublevel_invariance {F : E → ℝ} {G : E → E}
    {P : E → E →L[ℝ] E} {q : ℝ → E} {Ω : Set E} {z : E}
    {α p R t : ℝ} (hα : 0 < α) (hp : 0 ≤ p) (ht : 0 ≤ t)
    (hstrong : StrongConvexGradientOn F G Ω α) (hz : z ∈ Ω) (hcrit : G z = 0)
    (hF : ∀ x ∈ Ω, HasFDerivAt F (innerSL ℝ (G x)) x)
    (hq : ∀ s ∈ Icc 0 t, HasDerivAt q (-(P (q s) (G (q s)))) s)
    (hqΩ : ∀ s ∈ Icc 0 t, q s ∈ Ω)
    (hP : ∀ s ∈ Icc 0 t, ∀ v : E, p * ‖v‖^2 ≤ ⟪v, P (q s) v⟫_ℝ)
    (hinitial : F (q 0)-F z ≤ R) : F (q t)-F z ≤ R := by
  have he := energy_exponential_decay hα hp ht hstrong hz hF hq hqΩ hP
  have hc := distance_coercivity hstrong hz (hqΩ 0 ⟨le_refl 0, ht⟩) hcrit
  have hgap0 : 0 ≤ F (q 0)-F z :=
    (mul_nonneg (by positivity : 0 ≤ α/2) (sq_nonneg _)).trans hc
  have hnonneg : 0 ≤ α*p*t := mul_nonneg (mul_nonneg hα.le hp) ht
  have hexp : exp (-2*α*p*t) ≤ 1 := exp_le_one_iff.mpr (by nlinarith)
  have hmul : (F (q 0)-F z) * exp (-2*α*p*t) ≤ F (q 0)-F z := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hexp hgap0
  exact he.trans (hmul.trans hinitial)

/-- The trajectory distance estimate (4.14) follows from the proved energy decay,
strong convexity, and an initial sublevel bound. -/
theorem distance_exponential_decay {F : E → ℝ} {G : E → E}
    {P : E → E →L[ℝ] E} {q : ℝ → E} {Ω : Set E} {z : E}
    {α p R t : ℝ} (hα : 0 < α) (hp : 0 ≤ p) (hR : 0 ≤ R) (ht : 0 ≤ t)
    (hstrong : StrongConvexGradientOn F G Ω α) (hz : z ∈ Ω) (hcrit : G z = 0)
    (hF : ∀ x ∈ Ω, HasFDerivAt F (innerSL ℝ (G x)) x)
    (hq : ∀ s ∈ Icc 0 t, HasDerivAt q (-(P (q s) (G (q s)))) s)
    (hqΩ : ∀ s ∈ Icc 0 t, q s ∈ Ω)
    (hP : ∀ s ∈ Icc 0 t, ∀ v : E, p * ‖v‖^2 ≤ ⟪v, P (q s) v⟫_ℝ)
    (hinitial : F (q 0)-F z ≤ R) :
    ‖q t-z‖ ≤ sqrt (2*R/α) * exp (-α*p*t) := by
  have he := energy_exponential_decay hα hp ht hstrong hz hF hq hqΩ hP
  have hc := distance_coercivity hstrong hz (hqΩ t ⟨ht, le_refl t⟩) hcrit
  have he' : F (q t)-F z ≤ R * exp (-2*α*p*t) :=
    he.trans (mul_le_mul_of_nonneg_right hinitial (exp_pos _).le)
  have hsqrt : sqrt (2*R/α)^2 = 2*R/α := sq_sqrt (by positivity)
  have hexp : exp (-2*α*p*t) = exp (-α*p*t)^2 := by
    rw [pow_two, ← exp_add]
    congr 1
    ring
  have hscaled : α/2 * ‖q t-z‖^2 ≤
      α/2 * (sqrt (2*R/α) * exp (-α*p*t))^2 := by
    calc
      α/2 * ‖q t-z‖^2 ≤ F (q t)-F z := hc
      _ ≤ R * exp (-2*α*p*t) := he'
      _ = α/2 * (sqrt (2*R/α) * exp (-α*p*t))^2 := by
        rw [mul_pow, hsqrt, hexp]
        field_simp
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  exact (mul_le_mul_left (by positivity : 0 < α/2)).mp hscaled

/-- The zero energy sublevel consists of the critical point, and every actual
trajectory starting there is stationary. This handles the `R=0` case. -/
theorem zero_sublevel_stationary {F : E → ℝ} {G : E → E}
    {P : E → E →L[ℝ] E} {q : ℝ → E} {Ω : Set E} {z : E}
    {α t : ℝ} (hα : 0 < α) (ht : 0 ≤ t)
    (hstrong : StrongConvexGradientOn F G Ω α) (hz : z ∈ Ω) (hcrit : G z = 0)
    (hF : ∀ x ∈ Ω, HasFDerivAt F (innerSL ℝ (G x)) x)
    (hq : ∀ s ∈ Icc 0 t, HasDerivAt q (-(P (q s) (G (q s)))) s)
    (hqΩ : ∀ s ∈ Icc 0 t, q s ∈ Ω)
    (hP : ∀ s ∈ Icc 0 t, ∀ v : E, 0 ≤ ⟪v, P (q s) v⟫_ℝ)
    (hinitial : F (q 0)-F z ≤ 0) : q t = z := by
  have h := distance_exponential_decay (p := 0) (R := 0) hα (le_refl 0) (le_refl 0) ht
    hstrong hz hcrit hF hq hqΩ (by simpa only [zero_mul] using hP) hinitial
  have hnorm : ‖q t-z‖ ≤ 0 := by simpa using h
  exact sub_eq_zero.mp (norm_le_zero_iff.mp hnorm)

/-- Invariance and attraction for an actual global trajectory, using global
semidefiniteness to establish invariance before applying sublevel ellipticity. -/
theorem trajectory_invariant_and_attracted {F : E → ℝ} {G : E → E}
    {P : E → E →L[ℝ] E} {q : ℝ → E} {Ω C : Set E} {z : E}
    {α p R : ℝ} (hα : 0 < α) (hp : 0 ≤ p) (hR : 0 ≤ R)
    (hstrong : StrongConvexGradientOn F G Ω α) (hz : z ∈ Ω) (hcrit : G z = 0)
    (hF : ∀ x ∈ Ω, HasFDerivAt F (innerSL ℝ (G x)) x)
    (hP0 : ∀ x ∈ Ω, ∀ v : E, 0 ≤ ⟪v, P x v⟫_ℝ)
    (hP : ∀ x ∈ Ω, F x-F z ≤ R → ∀ v : E, p * ‖v‖^2 ≤ ⟪v, P x v⟫_ℝ)
    (hcover : ∀ x ∈ Ω, F x-F z ≤ R → x ∈ C)
    (hq : ∀ s, 0 ≤ s → HasDerivAt q (-(P (q s) (G (q s)))) s)
    (hqΩ : ∀ s, 0 ≤ s → q s ∈ Ω) (hinitial : F (q 0)-F z ≤ R) :
    ∀ t, 0 ≤ t → q t ∈ C ∩ Ω ∧
      ‖q t-z‖ ≤ sqrt (2*R/α) * exp (-α*p*t) := by
  have hinvariant : ∀ t, 0 ≤ t → F (q t)-F z ≤ R := by
    intro t ht
    apply sublevel_invariance (p := 0) hα (le_refl 0) ht hstrong hz hcrit hF
      (fun s hs => hq s hs.1) (fun s hs => hqΩ s hs.1) _ hinitial
    intro s hs v
    simpa only [zero_mul] using hP0 (q s) (hqΩ s hs.1) v
  intro t ht
  refine ⟨⟨hcover _ (hqΩ t ht) (hinvariant t ht), hqΩ t ht⟩, ?_⟩
  exact distance_exponential_decay hα hp hR ht hstrong hz hcrit hF
    (fun s hs => hq s hs.1) (fun s hs => hqΩ s hs.1)
    (fun s hs => hP _ (hqΩ s hs.1) (hinvariant s hs.1)) hinitial

/-- General semiglobal stability of a strongly convex preconditioned gradient
system. Energy and trajectory convergence estimates are proved internally from
strong convexity and sublevel ellipticity. The solutions are genuine ODE paths.
Global existence and Gaussian-specific geometry are independent obligations. -/
theorem semiglobal_from_gradient_geometry {F : E → ℝ} {G : E → E}
    {P : E → E →L[ℝ] E} {J : E → E →L[ℝ] E} {Ω C : Set E} {z : E}
    (hΩ : Convex ℝ Ω) (hC : IsCompact C) (hCconvex : Convex ℝ C) (hCΩ : C ⊆ Ω)
    (H : E →L[ℝ] E)
    (hsymm : ∀ u v : E, ⟪u, H v⟫_ℝ = ⟪v, H u⟫_ℝ)
    {α p R k m K : ℝ} (hα : 0 < α) (hp : 0 < p) (hR : 0 ≤ R)
    (hk : 0 < k) (hm : 0 < m) (hK : 1 ≤ K)
    (hstrong : StrongConvexGradientOn F G Ω α) (hz : z ∈ Ω) (hcrit : G z = 0)
    (hF : ∀ x ∈ Ω, HasFDerivAt F (innerSL ℝ (G x)) x)
    (hP0 : ∀ x ∈ Ω, ∀ v : E, 0 ≤ ⟪v, P x v⟫_ℝ)
    (hP : ∀ x ∈ Ω, F x-F z ≤ R → ∀ v : E, p * ‖v‖^2 ≤ ⟪v, P x v⟫_ℝ)
    (hcover : ∀ x ∈ Ω, F x-F z ≤ R → x ∈ C)
    (hdf : ∀ x ∈ Ω, HasFDerivAt (fun x => -(P x (G x))) (J x) x)
    (hJC : ContinuousOn J C) (hJz : ContinuousAt J z)
    (hlower : ∀ v : E, m * ‖v‖^2 ≤ Stability.energy H v)
    (hupper : ∀ v : E, Stability.energy H v ≤ m * K^2 * ‖v‖^2)
    (hbase : ∀ v : E, ⟪v, H (J z v)⟫_ℝ ≤ -k * Stability.energy H v) :
    ∃ S > 0, ∃ T ≥ 0, ∀ q r : ℝ → E,
      (∀ s, 0 ≤ s → HasDerivAt q (-(P (q s) (G (q s)))) s) →
      (∀ s, 0 ≤ s → HasDerivAt r (-(P (r s) (G (r s)))) s) →
      (∀ s, 0 ≤ s → q s ∈ Ω) → (∀ s, 0 ≤ s → r s ∈ Ω) →
      F (q 0)-F z ≤ R → F (r 0)-F z ≤ R →
      (∀ t, 0 ≤ t → ‖q t-r t‖ ≤ S * ‖q 0-r 0‖) ∧
      (∀ t, T ≤ t → ‖q t-r t‖ ≤ S * exp (-k/2 * (t-T)) * ‖q 0-r 0‖) := by
  obtain ⟨L, hL⟩ := Stability.exists_lipschitz_on_compact hC hCconvex
    (fun x hx => hdf x (hCΩ hx)) hJC
  obtain ⟨T, hT, hstable⟩ := Stability.all_time_stability_of_attraction
    (B := sqrt (2*R/α)) (γ := α*p) hΩ H z hsymm hk hm hK (mul_pos hα hp)
    hlower hupper hL hdf hbase hJz
  refine ⟨K * exp (L*T), mul_pos (by linarith) (exp_pos _), T, hT, ?_⟩
  intro q r hq hr hqΩ hrΩ hqi hri
  have hqgeom := trajectory_invariant_and_attracted hα hp.le hR hstrong hz hcrit hF
    hP0 hP hcover hq hqΩ hqi
  have hrgeom := trajectory_invariant_and_attracted hα hp.le hR hstrong hz hcrit hF
    hP0 hP hcover hr hrΩ hri
  apply hstable q r hq hr
    (fun s hs => (hqgeom s hs).1) (fun s hs => (hrgeom s hs).1)
  · intro s hs
    simpa only [neg_mul, mul_assoc] using (hqgeom s hs).2
  · intro s hs
    simpa only [neg_mul, mul_assoc] using (hrgeom s hs).2

end Paper38.EnergyDecay
