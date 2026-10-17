import Paper38.EnergyDecay
import Paper38.GradientStability
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
# Global existence from energy trapping

The pinned Mathlib has local Picard--Lindelof existence but no maximal-solution
or compact-continuation theorem. `StandardMaximalODETheorem` is an explicit,
standard external theorem INPUT, not a new axiom and not a Gaussian globality
assumption. Its source is Gerald Teschl, *Ordinary Differential Equations and
Dynamical Systems*, AMS GSM 140 (2012), Theorem 2.13 and Corollary 2.16,
Section 2.6, printed pp. 51--53 (PDF pp. 61--63):
https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf

The theorem supplies a maximal forward branch and the finite-lifetime compact
escape alternative for any locally Lipschitz vector field on an open domain.
Below, actual chain-rule energy dissipation proves trapping for the
preconditioned gradient field. Compact escape is then contradicted, proving
infinite lifetime; no global source trajectory is an input.
-/

namespace Paper38.GlobalODE

open Set Real
open scoped InnerProductSpace NNReal Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Maximal forward-branch data and the standard finite-lifetime escape
alternative. The path is only constrained before its lifetime. -/
structure ForwardMaximalSolution (Ω : Set E) (f : E → E) (x₀ : E) where
  lifetime : WithTop ℝ
  lifetime_pos : (0 : WithTop ℝ) < lifetime
  path : ℝ → E
  initial : path 0 = x₀
  mem_domain : ∀ t : ℝ, 0 ≤ t → (t : WithTop ℝ) < lifetime → path t ∈ Ω
  ode : ∀ t : ℝ, 0 ≤ t → (t : WithTop ℝ) < lifetime →
    HasDerivAt path (f (path t)) t
  escapes_compact : lifetime ≠ ⊤ → ∀ K : Set E, IsCompact K → K ⊆ Ω →
    ∃ t : ℝ, 0 ≤ t ∧ (t : WithTop ℝ) < lifetime ∧ path t ∉ K

/-- External textbook input: Teschl Theorem 2.13 + Corollary 2.16 specialized
to an autonomous finite-dimensional real system and initial time zero.
This proposition is deliberately unproved in the pinned Mathlib environment. -/
def StandardMaximalODETheorem (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] : Prop :=
  ∀ (Ω : Set E) (f : E → E), IsOpen Ω → LocallyLipschitzOn Ω f →
    ∀ x₀ ∈ Ω, Nonempty (ForwardMaximalSolution Ω f x₀)

/-- `C¹` regularity on an open domain supplies the standard local-Lipschitz
hypothesis. This step is proved from Mathlib, rather than included externally. -/
theorem locallyLipschitzOn_of_contDiffOn {Ω : Set E} {f : E → E}
    (hΩ : IsOpen Ω) (hf : ContDiffOn ℝ 1 f Ω) : LocallyLipschitzOn Ω f := by
  intro x hx
  obtain ⟨K, U, hU, hLip⟩ := (hf.contDiffAt (hΩ.mem_nhds hx)).exists_lipschitzOnWith
  exact ⟨K, U, nhdsWithin_le_nhds hU, hLip⟩

/-- Energy cannot increase on any finite, actual preconditioned-gradient
trajectory segment. Strong convexity and ellipticity are not needed here. -/
theorem energy_nonincreasing {F : E → ℝ} {G : E → E} {P : E → E →L[ℝ] E}
    {q : ℝ → E} {Ω : Set E} {t : ℝ} (ht : 0 ≤ t)
    (hF : ∀ x ∈ Ω, HasFDerivAt F (innerSL ℝ (G x)) x)
    (hP : ∀ x ∈ Ω, ∀ v : E, 0 ≤ ⟪v, P x v⟫_ℝ)
    (hqΩ : ∀ s ∈ Icc 0 t, q s ∈ Ω)
    (hq : ∀ s ∈ Icc 0 t, HasDerivAt q (-(P (q s) (G (q s)))) s) :
    F (q t) ≤ F (q 0) := by
  have hd : ∀ s ∈ Icc 0 t,
      HasDerivAt (fun s => F (q s)) (-⟪G (q s), P (q s) (G (q s))⟫_ℝ) s :=
    fun s hs => EnergyDecay.hasDerivAt_energy (hF _ (hqΩ s hs)) (hq s hs)
  have h := Stability.scalar_exp_bound (c := 0)
    (fun s hs => (hd s hs).continuousAt.continuousWithinAt)
    (fun s hs => (hd s ⟨hs.1, hs.2.le⟩).hasDerivWithinAt)
    (fun s hs => by
      simp only [zero_mul]
      exact neg_nonpos.mpr (hP _ (hqΩ s ⟨hs.1, hs.2.le⟩) _)) ht
  simpa using h

/-- The actual energy sublevel trapped by the gradient flow. -/
def energySublevel (Ω : Set E) (F : E → ℝ) (c : ℝ) : Set E :=
  {x | x ∈ Ω ∧ F x ≤ c}

/-- Every pre-lifetime point of a maximal branch remains in its original
energy sublevel, derived by the chain rule and positive mobility. -/
theorem maximal_energy_trapping {F : E → ℝ} {G : E → E}
    {P : E → E →L[ℝ] E} {Ω : Set E} {x₀ : E}
    (s : ForwardMaximalSolution Ω (fun x => -(P x (G x))) x₀)
    (hF : ∀ x ∈ Ω, HasFDerivAt F (innerSL ℝ (G x)) x)
    (hP : ∀ x ∈ Ω, ∀ v : E, 0 ≤ ⟪v, P x v⟫_ℝ)
    {t : ℝ} (ht : 0 ≤ t) (htlife : (t : WithTop ℝ) < s.lifetime) :
    s.path t ∈ energySublevel Ω F (F x₀) := by
  have hinterval : ∀ u ∈ Icc 0 t, (u : WithTop ℝ) < s.lifetime := by
    intro u hu
    exact lt_of_le_of_lt (by exact_mod_cast hu.2) htlife
  refine ⟨s.mem_domain t ht htlife, ?_⟩
  have h := energy_nonincreasing ht hF hP
    (fun u hu => s.mem_domain u hu.1 (hinterval u hu))
    (fun u hu => s.ode u hu.1 (hinterval u hu))
  simpa only [s.initial] using h

/-- Compact energy trapping rules out a finite maximal lifetime. This is the
paper's continuation argument, with trapping itself proved above. -/
theorem maximal_lifetime_eq_top {F : E → ℝ} {G : E → E}
    {P : E → E →L[ℝ] E} {Ω : Set E} {x₀ : E}
    (s : ForwardMaximalSolution Ω (fun x => -(P x (G x))) x₀)
    (hF : ∀ x ∈ Ω, HasFDerivAt F (innerSL ℝ (G x)) x)
    (hP : ∀ x ∈ Ω, ∀ v : E, 0 ≤ ⟪v, P x v⟫_ℝ)
    (hcompact : IsCompact (energySublevel Ω F (F x₀))) : s.lifetime = ⊤ := by
  by_contra hfinite
  obtain ⟨t, ht, htlife, hout⟩ := s.escapes_compact hfinite
    (energySublevel Ω F (F x₀)) hcompact (fun _ hx => hx.1)
  exact hout (maximal_energy_trapping s hF hP ht htlife)

/-- Global forward existence for an actual preconditioned gradient field follows
from `C¹` regularity, positive mobility and compact energy sublevels, using only
the explicitly identified standard maximal-ODE input. -/
theorem exists_global_gradient_flow [FiniteDimensional ℝ E]
    (hstandard : StandardMaximalODETheorem E)
    {F : E → ℝ} {G : E → E} {P : E → E →L[ℝ] E} {Ω : Set E}
    (hΩ : IsOpen Ω) (hfield : ContDiffOn ℝ 1 (fun x => -(P x (G x))) Ω)
    (hF : ∀ x ∈ Ω, HasFDerivAt F (innerSL ℝ (G x)) x)
    (hP : ∀ x ∈ Ω, ∀ v : E, 0 ≤ ⟪v, P x v⟫_ℝ)
    (hcompact : ∀ c : ℝ, IsCompact (energySublevel Ω F c))
    {x₀ : E} (hx₀ : x₀ ∈ Ω) :
    ∃ q : ℝ → E, q 0 = x₀ ∧ ∀ t : ℝ, 0 ≤ t →
      q t ∈ Ω ∧ HasDerivAt q (-(P (q t) (G (q t)))) t ∧ F (q t) ≤ F x₀ := by
  obtain ⟨s⟩ := hstandard Ω (fun x => -(P x (G x))) hΩ
    (locallyLipschitzOn_of_contDiffOn hΩ hfield) x₀ hx₀
  have htop := maximal_lifetime_eq_top s hF hP (hcompact (F x₀))
  refine ⟨s.path, s.initial, ?_⟩
  intro t ht
  have htlife : (t : WithTop ℝ) < s.lifetime := by rw [htop]; simp
  have htrap := maximal_energy_trapping s hF hP ht htlife
  exact ⟨htrap.1, s.ode t ht htlife, htrap.2⟩

/-- Full global existence, sublevel invariance and the two exponential estimates
of Proposition 4.3 from standard gradient geometry. The path is constructed by
maximal continuation; global existence or energy convergence are not premises. -/
theorem exists_global_convergent_gradient_flow [FiniteDimensional ℝ E]
    (hstandard : StandardMaximalODETheorem E)
    {F : E → ℝ} {G : E → E} {P : E → E →L[ℝ] E} {Ω : Set E} {z x₀ : E}
    {α p R : ℝ} (hα : 0 < α) (hp : 0 ≤ p) (hR : 0 ≤ R)
    (hΩ : IsOpen Ω) (hfield : ContDiffOn ℝ 1 (fun x => -(P x (G x))) Ω)
    (hF : ∀ x ∈ Ω, HasFDerivAt F (innerSL ℝ (G x)) x)
    (hP0 : ∀ x ∈ Ω, ∀ v : E, 0 ≤ ⟪v, P x v⟫_ℝ)
    (hcompact : ∀ c : ℝ, IsCompact (energySublevel Ω F c))
    (hstrong : EnergyDecay.StrongConvexGradientOn F G Ω α)
    (hz : z ∈ Ω) (hcrit : G z = 0)
    (hP : ∀ x ∈ Ω, F x-F z ≤ R → ∀ v : E, p * ‖v‖^2 ≤ ⟪v, P x v⟫_ℝ)
    (hx₀ : x₀ ∈ Ω) (hinit : F x₀-F z ≤ R) :
    ∃ q : ℝ → E, q 0 = x₀ ∧ ∀ t : ℝ, 0 ≤ t →
      q t ∈ energySublevel Ω F (F z+R) ∧
      HasDerivAt q (-(P (q t) (G (q t)))) t ∧
      F (q t)-F z ≤ (F x₀-F z) * exp (-2*α*p*t) ∧
      ‖q t-z‖ ≤ sqrt (2*R/α) * exp (-α*p*t) := by
  obtain ⟨q, hqinit, hq⟩ := exists_global_gradient_flow hstandard hΩ hfield hF hP0 hcompact hx₀
  have hqR : ∀ t : ℝ, 0 ≤ t → F (q t)-F z ≤ R := by
    intro t ht
    linarith [(hq t ht).2.2]
  refine ⟨q, hqinit, ?_⟩
  intro t ht
  refine ⟨⟨(hq t ht).1, by linarith [hqR t ht]⟩, (hq t ht).2.1, ?_, ?_⟩
  · have h := EnergyDecay.energy_exponential_decay hα hp ht hstrong hz hF
      (fun s hs => (hq s hs.1).2.1) (fun s hs => (hq s hs.1).1)
      (fun s hs => hP _ (hq s hs.1).1 (hqR s hs.1))
    simpa only [hqinit] using h
  · apply EnergyDecay.distance_exponential_decay hα hp hR ht hstrong hz hcrit hF
      (fun s hs => (hq s hs.1).2.1) (fun s hs => (hq s hs.1).1)
      (fun s hs => hP _ (hq s hs.1).1 (hqR s hs.1))
    simpa only [hqinit] using hinit

/-- Global well-posedness and exponential convergence derived directly from C²
strongly convex energy geometry and C¹ positive mobility. All ellipticity and
stability constants, the minimizer and the global path are constructed. The
only external input is the standard maximal-ODE/compact-escape theorem. -/
theorem exists_unique_global_C2_gradient_flow [FiniteDimensional ℝ E]
    (hstandard : StandardMaximalODETheorem E)
    {F : E → ℝ} {P : E → E →L[ℝ] E} {Ω : Set E} {α : ℝ}
    (hα : 0 < α) (hΩ : IsOpen Ω) (hΩconv : Convex ℝ Ω)
    (hF : ContDiffOn ℝ 2 F Ω)
    (hH : ∀ x ∈ Ω, ∀ v : E, α * ‖v‖^2 ≤ (fderiv ℝ (fderiv ℝ F) x v) v)
    (hP : ContDiffOn ℝ 1 P Ω)
    (hPpos : ∀ x ∈ Ω, ∀ v : E, v ≠ 0 → 0 < ⟪v, P x v⟫_ℝ)
    (hcompact : ∀ c : ℝ, IsCompact {x | x ∈ Ω ∧ F x ≤ c})
    {x₀ : E} (hx₀ : x₀ ∈ Ω) :
    ∃ z ∈ Ω, (∀ x ∈ Ω, F z ≤ F x) ∧ gradient F z = 0 ∧
    ∃ p > 0, ∃ q : ℝ → E, q 0 = x₀ ∧
      (∀ t : ℝ, 0 ≤ t → q t ∈ Ω ∧
        HasDerivAt q (-(P (q t) (gradient F (q t)))) t ∧
        F (q t)-F z ≤ (F x₀-F z) * exp (-2*α*p*t) ∧
        ‖q t-z‖ ≤ sqrt (2*(F x₀-F z)/α) * exp (-α*p*t)) ∧
      (∀ r : ℝ → E, r 0 = x₀ → (∀ t, 0 ≤ t → r t ∈ Ω) →
        (∀ t, 0 ≤ t → HasDerivAt r (-(P (r t) (gradient F (r t)))) t) →
        ∀ t, 0 ≤ t → r t = q t) := by
  obtain ⟨z,hz,hmin⟩ := GradientGeometry.exists_minimizer_of_compact_sublevel
    hx₀ hF.continuousOn (hcompact (F x₀))
  have hcrit := GradientGeometry.gradient_eq_zero_of_minimizer hΩ hz hmin
  let R := F x₀-F z
  have hR : 0 ≤ R := sub_nonneg.mpr (hmin x₀ hx₀)
  have hstrong := GradientGeometry.strongConvexGradientOn_of_second_fderiv_lower hΩ hΩconv hF hH
  have hFderiv : ∀ x ∈ Ω, HasFDerivAt F (innerSL ℝ (gradient F x)) x := by
    intro x hx
    exact GradientGeometry.hasFDerivAt_gradient_repr
      ((hF.contDiffAt (hΩ.mem_nhds hx)).differentiableAt (by norm_num))
  have hP0 : ∀ x ∈ Ω, ∀ v : E, 0 ≤ ⟪v,P x v⟫_ℝ := by
    intro x hx v
    by_cases hv : v = 0
    · simp [hv]
    · exact (hPpos x hx v hv).le
  have hfield : ContDiffOn ℝ 1 (fun x => -(P x (gradient F x))) Ω :=
    (hP.clm_apply (GradientGeometry.gradient_contDiffOn hΩ hF)).neg
  let K : Set E := {x | x ∈ Ω ∧ F x ≤ F x₀}
  have hKΩ : K ⊆ Ω := fun _ hx => hx.1
  obtain ⟨p,hp,hpell⟩ := CompactEllipticity.exists_uniform_lower (K := K)
    (hcompact (F x₀)) (hP.continuousOn.mono hKΩ) (fun x hx => hPpos x hx.1)
  have hPell : ∀ x ∈ Ω, F x-F z ≤ R → ∀ v : E, p * ‖v‖^2 ≤ ⟪v,P x v⟫_ℝ := by
    intro x hx hRx
    exact hpell x ⟨hx,by dsimp [R] at hRx; linarith⟩
  obtain ⟨q,hq0,hq⟩ := exists_global_convergent_gradient_flow hstandard hα hp.le hR
    hΩ hfield hFderiv hP0 hcompact hstrong hz hcrit hPell hx₀ (le_refl R)
  refine ⟨z,hz,hmin,hcrit,p,hp,q,hq0,?_,?_⟩
  · intro t ht
    have hqt := hq t ht
    exact ⟨hqt.1.1,hqt.2.1,hqt.2.2.1,hqt.2.2.2⟩
  · intro r hr0 hrΩ hrode t ht
    obtain ⟨S,hS,T,hT,k,hk,hstable⟩ := GradientStability.semiglobal
      hα hR hΩ hΩconv hF hH hP hPpos hcompact hz hmin
    have h := (hstable q r (fun s hs => (hq s hs).2.1) hrode
      (fun s hs => (hq s hs).1.1) hrΩ
      (by simpa only [hq0] using (le_refl R))
      (by simpa only [hr0] using (le_refl R))).1 t ht
    rw [hq0,hr0,sub_self,norm_zero,mul_zero] at h
    exact (sub_eq_zero.mp (norm_le_zero_iff.mp h)).symm

end Paper38.GlobalODE
