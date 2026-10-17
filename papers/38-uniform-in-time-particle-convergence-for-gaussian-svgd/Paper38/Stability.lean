import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Analytic core of Section 5

These lemmas prove contraction and its finite-time patch for actual differentiable
trajectories.  They do not assert that the Gaussian vector field has the local
Jacobian bound or the uniform entry time: those are separate geometric obligations.
-/

namespace Paper38.Stability

open Set Real Filter
open scoped InnerProductSpace NNReal Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The fixed Hessian quadratic form used in (5.2)--(5.5). -/
def energy (H : E →L[ℝ] E) (v : E) : ℝ := ⟪v, H v⟫_ℝ

/-- Scalar differential inequality, with no positivity restriction on the exponent. -/
theorem scalar_exp_bound {g g' : ℝ → ℝ} {a t c : ℝ}
    (hcont : ContinuousOn g (Icc a t))
    (hderiv : ∀ s ∈ Ico a t, HasDerivWithinAt g (g' s) (Ici s) s)
    (hbound : ∀ s ∈ Ico a t, g' s ≤ c * g s) (hat : a ≤ t) :
    g t ≤ g a * exp (c * (t - a)) := by
  have h := le_gronwallBound_of_liminf_deriv_right_le (K := c) (ε := 0) hcont
    (fun s hs r hr => (hderiv s hs).liminf_right_slope_le hr)
    (le_refl (g a)) (by intro s hs; simpa using hbound s hs) t ⟨hat, le_refl t⟩
  simpa only [gronwallBound_ε0] using h

/-- A Jacobian bound on a convex region implies the corresponding finite-difference
one-sided Lipschitz bound; this is the segment argument in Section 5. -/
theorem one_sided_of_jacobian {f : E → E} {J : E → E →L[ℝ] E}
    {U : Set E} (hU : Convex ℝ U) (H : E →L[ℝ] E) (k : ℝ)
    (hdf : ∀ z ∈ U, HasFDerivAt f (J z) z)
    (hdiss : ∀ z ∈ U, ∀ v : E, ⟪v, H (J z v)⟫_ℝ ≤ -k * energy H v)
    {x y : E} (hx : x ∈ U) (hy : y ∈ U) :
    ⟪x-y, H (f x - f y)⟫_ℝ ≤ -k * energy H (x-y) := by
  let v := x-y
  let path : ℝ → E := fun s => y + s • v
  let g : ℝ → ℝ := fun s => ⟪v, H (f (path s))⟫_ℝ
  have hpath : ∀ s ∈ Icc (0:ℝ) 1, path s ∈ U := by
    intro s hs
    have h := hU hy hx (sub_nonneg.mpr hs.2) hs.1 (by ring : (1-s)+s=1)
    convert h using 1 <;> simp [path, v, smul_sub, sub_smul] <;> module
  have hgd : ∀ s ∈ Icc (0:ℝ) 1,
      HasDerivAt g ⟪v, H (J (path s) v)⟫_ℝ s := by
    intro s hs
    have hp : HasDerivAt path v s := by
      simpa only [one_smul] using ((hasDerivAt_id s).smul_const v).const_add y
    simpa only [g, Function.comp_apply, inner_zero_left, add_zero] using
      (hasDerivAt_const s v).inner ℝ
        (H.hasFDerivAt.comp_hasDerivAt s ((hdf _ (hpath s hs)).comp_hasDerivAt s hp))
  have hcmp := image_le_of_deriv_right_le_deriv_boundary
    (f := g) (f' := fun s => ⟪v, H (J (path s) v)⟫_ℝ)
    (fun s hs => (hgd s hs).continuousAt.continuousWithinAt)
    (fun s hs => (hgd s ⟨hs.1, hs.2.le⟩).hasDerivWithinAt)
    (B := fun s => g 0 + s * (-k * energy H v))
    (B' := fun _ => -k * energy H v)
    (by simp)
    (by fun_prop)
    (fun s _ => by simpa using (((hasDerivAt_id s).mul_const (-k * energy H v)).const_add (g 0)).hasDerivWithinAt)
    (fun s hs => hdiss _ (hpath s ⟨hs.1, hs.2.le⟩) v)
    (x := 1) (by simp)
  simpa [g, path, v, map_sub, inner_sub_right, add_comm] using hcmp

/-- The exact weighted squared-distance decay (5.5), derived from the ODE and
one-sided dissipativity of the vector field in a fixed symmetric metric. -/
theorem weighted_decay {f : E → E} {q r : ℝ → E} (H : E →L[ℝ] E)
    (hsymm : ∀ u v : E, ⟪u, H v⟫_ℝ = ⟪v, H u⟫_ℝ)
    {a t k : ℝ} (hat : a ≤ t)
    (hq : ∀ s ∈ Icc a t, HasDerivAt q (f (q s)) s)
    (hr : ∀ s ∈ Icc a t, HasDerivAt r (f (r s)) s)
    (hdiss : ∀ s ∈ Ico a t,
      ⟪q s-r s, H (f (q s)-f (r s))⟫_ℝ ≤ -k/2 * energy H (q s-r s)) :
    energy H (q t-r t) ≤ energy H (q a-r a) * exp (-k * (t-a)) := by
  have hed : ∀ s ∈ Icc a t,
      HasDerivAt (fun s => energy H (q s-r s))
        (2 * ⟪q s-r s, H (f (q s)-f (r s))⟫_ℝ) s := by
    intro s hs
    have he := (hq s hs).sub (hr s hs)
    have hh := he.inner ℝ (H.hasFDerivAt.comp_hasDerivAt s he)
    unfold energy
    convert hh using 1
    dsimp only [Function.comp_apply, Pi.sub_apply]
    rw [hsymm (f (q s)-f (r s)) (q s-r s)]
    ring
  apply scalar_exp_bound (fun s hs => (hed s hs).continuousAt.continuousWithinAt)
    (fun s hs => (hed s ⟨hs.1, hs.2.le⟩).hasDerivWithinAt)
    (fun s hs => by nlinarith [hdiss s hs]) hat

/-- A continuously differentiable vector field has a uniform Lipschitz constant on
a common convex compact region. This constructs the finite `ℓ_R` used in (5.7). -/
theorem exists_lipschitz_on_compact {f : E → E} {J : E → E →L[ℝ] E} {C : Set E}
    (hcompact : IsCompact C) (hconvex : Convex ℝ C)
    (hdf : ∀ z ∈ C, HasFDerivAt f (J z) z) (hJ : ContinuousOn J C) :
    ∃ L : ℝ≥0, LipschitzOnWith L f C := by
  obtain ⟨M, hM⟩ := hcompact.exists_bound_of_continuousOn hJ
  refine ⟨⟨max 0 M, le_max_left _ _⟩, ?_⟩
  apply hconvex.lipschitzOnWith_of_nnnorm_hasFDerivWithin_le
    (fun z hz => (hdf z hz).hasFDerivWithinAt)
  intro z hz
  exact NNReal.coe_le_coe.mp ((hM z hz).trans (le_max_right _ _))

/-- Early-time Grönwall for exact trajectories staying in a region where the vector
field is Lipschitz. This is (5.7), with the actual ODE in the hypotheses. -/
theorem early_norm_bound {f : E → E} {q r : ℝ → E} {C : Set E} {L : ℝ≥0}
    (hf : LipschitzOnWith L f C) {t : ℝ} (ht : 0 ≤ t)
    (hq : ∀ s ∈ Icc 0 t, HasDerivAt q (f (q s)) s)
    (hr : ∀ s ∈ Icc 0 t, HasDerivAt r (f (r s)) s)
    (hqc : ∀ s ∈ Icc 0 t, q s ∈ C) (hrc : ∀ s ∈ Icc 0 t, r s ∈ C) :
    ‖q t-r t‖ ≤ ‖q 0-r 0‖ * exp (L * t) := by
  simpa only [dist_eq_norm, sub_zero] using
    dist_le_of_trajectories_ODE_of_mem
      (v := fun _ => f) (s := fun _ => C)
      (fun _ _ => hf)
      (fun s hs => (hq s hs).continuousAt.continuousWithinAt)
      (fun s hs => (hq s ⟨hs.1, hs.2.le⟩).hasDerivWithinAt)
      (fun s hs => hqc s ⟨hs.1, hs.2.le⟩)
      (fun s hs => (hr s hs).continuousAt.continuousWithinAt)
      (fun s hs => (hr s ⟨hs.1, hs.2.le⟩).hasDerivWithinAt)
      (fun s hs => hrc s ⟨hs.1, hs.2.le⟩)
      (le_refl (dist (q 0) (r 0))) t ⟨ht, le_refl t⟩

/-- Convert the weighted contraction to Euclidean norm contraction using norm
equivalence.  The constant `K` is the square root of the metric condition number. -/
theorem late_norm_bound {f : E → E} {q r : ℝ → E} (H : E →L[ℝ] E)
    (hsymm : ∀ u v : E, ⟪u, H v⟫_ℝ = ⟪v, H u⟫_ℝ)
    {a t k m K : ℝ} (hat : a ≤ t) (hm : 0 < m) (hK : 0 ≤ K)
    (hlower : ∀ v : E, m * ‖v‖^2 ≤ energy H v)
    (hupper : ∀ v : E, energy H v ≤ m * K^2 * ‖v‖^2)
    (hq : ∀ s ∈ Icc a t, HasDerivAt q (f (q s)) s)
    (hr : ∀ s ∈ Icc a t, HasDerivAt r (f (r s)) s)
    (hdiss : ∀ s ∈ Ico a t,
      ⟪q s-r s, H (f (q s)-f (r s))⟫_ℝ ≤ -k/2 * energy H (q s-r s)) :
    ‖q t-r t‖ ≤ K * exp (-k/2 * (t-a)) * ‖q a-r a‖ := by
  have hdecay := weighted_decay H hsymm hat hq hr hdiss
  have hexp : exp (-k * (t-a)) = exp (-k/2 * (t-a)) ^ 2 := by
    rw [pow_two, ← exp_add]
    congr 1
    ring
  have hscaled : m * ‖q t-r t‖^2 ≤
      m * (K * exp (-k/2 * (t-a)) * ‖q a-r a‖)^2 := calc
    m * ‖q t-r t‖^2 ≤ energy H (q t-r t) := hlower _
    _ ≤ energy H (q a-r a) * exp (-k * (t-a)) := hdecay
    _ ≤ (m * K^2 * ‖q a-r a‖^2) * exp (-k * (t-a)) :=
      mul_le_mul_of_nonneg_right (hupper _) (exp_pos _).le
    _ = m * (K * exp (-k/2 * (t-a)) * ‖q a-r a‖)^2 := by rw [hexp]; ring
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp ((mul_le_mul_left hm).mp hscaled)

/-- Patch the genuine early ODE Grönwall estimate with genuine late metric
contraction.  The entry and Jacobian assumptions are geometric input; the
uniform-in-time estimate and eventual exponential estimate are conclusions. -/
theorem semiglobal_from_entry {f : E → E} {J : E → E →L[ℝ] E}
    {q r : ℝ → E} {C U : Set E} (hU : Convex ℝ U)
    (H : E →L[ℝ] E)
    (hsymm : ∀ u v : E, ⟪u, H v⟫_ℝ = ⟪v, H u⟫_ℝ)
    {T k m K : ℝ} {L : ℝ≥0}
    (hT : 0 ≤ T) (hk : 0 ≤ k) (hm : 0 < m) (hK : 1 ≤ K)
    (hlower : ∀ v : E, m * ‖v‖^2 ≤ energy H v)
    (hupper : ∀ v : E, energy H v ≤ m * K^2 * ‖v‖^2)
    (hL : LipschitzOnWith L f C)
    (hdf : ∀ z ∈ U, HasFDerivAt f (J z) z)
    (hJ : ∀ z ∈ U, ∀ v : E, ⟪v, H (J z v)⟫_ℝ ≤ -k/2 * energy H v)
    (hq : ∀ s, 0 ≤ s → HasDerivAt q (f (q s)) s)
    (hr : ∀ s, 0 ≤ s → HasDerivAt r (f (r s)) s)
    (hqc : ∀ s ∈ Icc 0 T, q s ∈ C) (hrc : ∀ s ∈ Icc 0 T, r s ∈ C)
    (hqu : ∀ s, T ≤ s → q s ∈ U) (hru : ∀ s, T ≤ s → r s ∈ U) :
    (∀ t, 0 ≤ t → ‖q t-r t‖ ≤ K * exp (L*T) * ‖q 0-r 0‖) ∧
    (∀ t, T ≤ t → ‖q t-r t‖ ≤
      K * exp (L*T) * exp (-k/2 * (t-T)) * ‖q 0-r 0‖) := by
  have hK0 : 0 ≤ K := le_trans zero_le_one hK
  have hearly : ∀ t ∈ Icc 0 T,
      ‖q t-r t‖ ≤ ‖q 0-r 0‖ * exp (L*t) := by
    intro t ht
    exact early_norm_bound hL ht.1
      (fun s hs => hq s hs.1) (fun s hs => hr s hs.1)
      (fun s hs => hqc s ⟨hs.1, hs.2.trans ht.2⟩)
      (fun s hs => hrc s ⟨hs.1, hs.2.trans ht.2⟩)
  have hlate : ∀ t, T ≤ t → ‖q t-r t‖ ≤
      K * exp (L*T) * exp (-k/2 * (t-T)) * ‖q 0-r 0‖ := by
    intro t ht
    have hd := late_norm_bound H hsymm ht hm hK0 hlower hupper
      (fun s hs => hq s (hT.trans hs.1))
      (fun s hs => hr s (hT.trans hs.1))
      (fun s hs => by
        simpa only [neg_div] using one_sided_of_jacobian hU H (k/2) hdf
          (by simpa only [neg_div] using hJ) (hqu s hs.1) (hru s hs.1))
    calc
      ‖q t-r t‖ ≤ K * exp (-k/2 * (t-T)) * ‖q T-r T‖ := hd
      _ ≤ K * exp (-k/2 * (t-T)) * (‖q 0-r 0‖ * exp (L*T)) :=
        mul_le_mul_of_nonneg_left (hearly T ⟨hT, le_refl T⟩) (by positivity)
      _ = K * exp (L*T) * exp (-k/2 * (t-T)) * ‖q 0-r 0‖ := by ring
  refine ⟨?_, hlate⟩
  intro t ht
  by_cases htime : t ≤ T
  · calc
      ‖q t-r t‖ ≤ ‖q 0-r 0‖ * exp (L*t) := hearly t ⟨ht, htime⟩
      _ ≤ ‖q 0-r 0‖ * exp (L*T) :=
        mul_le_mul_of_nonneg_left (exp_le_exp.mpr
          (mul_le_mul_of_nonneg_left htime L.coe_nonneg)) (norm_nonneg _)
      _ ≤ K * exp (L*T) * ‖q 0-r 0‖ := by
        nlinarith [mul_nonneg (exp_pos (L*T)).le (norm_nonneg (q 0-r 0))]
  · have hTt : T ≤ t := (lt_of_not_ge htime).le
    have hexp : exp (-k/2 * (t-T)) ≤ 1 := by
      apply exp_le_one_iff.mpr
      exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (sub_nonneg.mpr hTt)
    calc
      ‖q t-r t‖ ≤ K * exp (L*T) * exp (-k/2 * (t-T)) * ‖q 0-r 0‖ := hlate t hTt
      _ ≤ K * exp (L*T) * ‖q 0-r 0‖ := by
        have hmul := mul_le_mul_of_nonneg_left hexp
          (mul_nonneg (mul_nonneg hK0 (exp_pos (L*T)).le) (norm_nonneg (q 0-r 0)))
        nlinarith

/-- Dissipativity is preserved under a sufficiently small operator perturbation.
The coercivity assumption is on the fixed metric, not on the vector field. -/
theorem dissipative_perturbation (H A A₀ : E →L[ℝ] E) {k m : ℝ}
    (hk : 0 ≤ k)
    (hlower : ∀ v : E, m * ‖v‖^2 ≤ energy H v)
    (hbase : ∀ v : E, ⟪v, H (A₀ v)⟫_ℝ ≤ -k * energy H v)
    (hclose : ‖H‖ * ‖A-A₀‖ ≤ k*m/2) (v : E) :
    ⟪v, H (A v)⟫_ℝ ≤ -k/2 * energy H v := by
  have herror : ⟪v, H ((A-A₀) v)⟫_ℝ ≤ k/2 * energy H v := calc
    ⟪v, H ((A-A₀) v)⟫_ℝ ≤ ‖v‖ * ‖H ((A-A₀) v)‖ := real_inner_le_norm _ _
    _ ≤ ‖v‖ * (‖H‖ * (‖A-A₀‖ * ‖v‖)) := by
      gcongr
      exact (H.le_opNorm _).trans
        (mul_le_mul_of_nonneg_left ((A-A₀).le_opNorm v) (norm_nonneg H))
    _ = ‖v‖^2 * (‖H‖ * ‖A-A₀‖) := by ring
    _ ≤ ‖v‖^2 * (k*m/2) := mul_le_mul_of_nonneg_left hclose (sq_nonneg _)
    _ = k/2 * (m * ‖v‖^2) := by ring
    _ ≤ k/2 * energy H v := mul_le_mul_of_nonneg_left (hlower v) (by positivity)
  have hsplit : ⟪v, H (A v)⟫_ℝ =
      ⟪v, H (A₀ v)⟫_ℝ + ⟪v, H ((A-A₀) v)⟫_ℝ := by
    simp only [ContinuousLinearMap.sub_apply, map_sub, inner_sub_right]
    ring
  rw [hsplit]
  nlinarith [hbase v]

/-- Continuity of the Jacobian produces a common dissipative neighborhood, as in
(5.3). There is no assumption on a third derivative. -/
theorem exists_dissipative_ball (H : E →L[ℝ] E) {J : E → E →L[ℝ] E} {z₀ : E}
    {k m : ℝ} (hk : 0 < k) (hm : 0 < m)
    (hlower : ∀ v : E, m * ‖v‖^2 ≤ energy H v)
    (hbase : ∀ v : E, ⟪v, H (J z₀ v)⟫_ℝ ≤ -k * energy H v)
    (hcont : ContinuousAt J z₀) :
    ∃ δ > 0, ∀ z, dist z z₀ < δ → ∀ v : E,
      ⟪v, H (J z v)⟫_ℝ ≤ -k/2 * energy H v := by
  let ε : ℝ := (k*m/2)/(‖H‖+1)
  have hε : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨δ, hδ, hJ⟩ := Metric.continuousAt_iff.mp hcont ε hε
  refine ⟨δ, hδ, ?_⟩
  intro z hz v
  apply dissipative_perturbation H (J z) (J z₀) hk.le hlower hbase
  have hdiff : ‖J z-J z₀‖ < ε := by simpa only [dist_eq_norm] using hJ hz
  have hnorm : 0 < ‖H‖+1 := by positivity
  calc
    ‖H‖ * ‖J z-J z₀‖ ≤ (‖H‖+1) * ‖J z-J z₀‖ := by nlinarith [norm_nonneg (J z-J z₀)]
    _ ≤ (‖H‖+1) * ε := mul_le_mul_of_nonneg_left hdiff.le hnorm.le
    _ = k*m/2 := by dsimp [ε]; field_simp

/-- Uniform exponential attraction gives a common entry time for every positive
Euclidean radius.  The time depends only on the attraction constants and radius. -/
theorem exists_entry_time (C γ δ : ℝ) (hγ : 0 < γ) (hδ : 0 < δ) :
    ∃ T ≥ 0, ∀ t ≥ T, C * exp (-γ*t) < δ := by
  have hlim : Tendsto (fun t : ℝ => C * exp (-γ*t)) atTop (𝓝 0) := by
    have hexp := tendsto_exp_neg_atTop_nhds_zero.comp
      (Filter.Tendsto.const_mul_atTop hγ (tendsto_id : Tendsto (fun t : ℝ => t) atTop atTop))
    simpa only [mul_zero, neg_mul] using tendsto_const_nhds.mul hexp
  obtain ⟨T, hT⟩ := eventually_atTop.mp ((tendsto_order.mp hlim).2 δ hδ)
  exact ⟨max 0 T, le_max_left _ _, fun t ht => hT t ((le_max_right _ _).trans ht)⟩

/-- Abstract semiglobal all-time stability from uniform exponential attraction,
a dissipative linearization, and a common Lipschitz region.  The entry time is
chosen before the trajectories, so every constant is uniform over that family.
This isolates the full analytic two-regime argument of Lemma 5.1. -/
theorem all_time_stability_of_attraction {f : E → E} {J : E → E →L[ℝ] E}
    {C Ω : Set E} (hΩ : Convex ℝ Ω) (H : E →L[ℝ] E) (z₀ : E)
    (hsymm : ∀ u v : E, ⟪u, H v⟫_ℝ = ⟪v, H u⟫_ℝ)
    {k m K B γ : ℝ} {L : ℝ≥0}
    (hk : 0 < k) (hm : 0 < m) (hK : 1 ≤ K) (hγ : 0 < γ)
    (hlower : ∀ v : E, m * ‖v‖^2 ≤ energy H v)
    (hupper : ∀ v : E, energy H v ≤ m * K^2 * ‖v‖^2)
    (hL : LipschitzOnWith L f C)
    (hdf : ∀ z ∈ Ω, HasFDerivAt f (J z) z)
    (hbase : ∀ v : E, ⟪v, H (J z₀ v)⟫_ℝ ≤ -k * energy H v)
    (hcont : ContinuousAt J z₀) :
    ∃ T ≥ 0, ∀ q r : ℝ → E,
      (∀ s, 0 ≤ s → HasDerivAt q (f (q s)) s) →
      (∀ s, 0 ≤ s → HasDerivAt r (f (r s)) s) →
      (∀ s, 0 ≤ s → q s ∈ C ∩ Ω) →
      (∀ s, 0 ≤ s → r s ∈ C ∩ Ω) →
      (∀ s, 0 ≤ s → ‖q s-z₀‖ ≤ B * exp (-γ*s)) →
      (∀ s, 0 ≤ s → ‖r s-z₀‖ ≤ B * exp (-γ*s)) →
      (∀ t, 0 ≤ t → ‖q t-r t‖ ≤ K * exp (L*T) * ‖q 0-r 0‖) ∧
      (∀ t, T ≤ t → ‖q t-r t‖ ≤
        K * exp (L*T) * exp (-k/2 * (t-T)) * ‖q 0-r 0‖) := by
  obtain ⟨δ, hδ, hdiss⟩ := exists_dissipative_ball H hk hm hlower hbase hcont
  obtain ⟨T, hT, hentry⟩ := exists_entry_time B γ δ hγ hδ
  refine ⟨T, hT, ?_⟩
  intro q r hq hr hqc hrc hqconv hrconv
  have hqu : ∀ s, T ≤ s → q s ∈ Metric.ball z₀ δ ∩ Ω := by
    intro s hs
    refine ⟨?_, (hqc s (hT.trans hs)).2⟩
    rw [Metric.mem_ball, dist_eq_norm]
    exact (hqconv s (hT.trans hs)).trans_lt (hentry s hs)
  have hru : ∀ s, T ≤ s → r s ∈ Metric.ball z₀ δ ∩ Ω := by
    intro s hs
    refine ⟨?_, (hrc s (hT.trans hs)).2⟩
    rw [Metric.mem_ball, dist_eq_norm]
    exact (hrconv s (hT.trans hs)).trans_lt (hentry s hs)
  exact semiglobal_from_entry ((convex_ball z₀ δ).inter hΩ) H hsymm hT hk.le hm hK
    hlower hupper hL
    (fun z hz => hdf z hz.2)
    (fun z hz v => hdiss z hz.1 v)
    hq hr
    (fun s hs => (hqc s hs.1).1) (fun s hs => (hrc s hs.1).1)
    hqu hru

/-- At a critical point the derivative of the mobility makes no contribution:
`D(-P ∇F) = -P D(∇F)`.  This proves the linearization identity used in Section 5. -/
theorem gradient_flow_linearization {P : E → E →L[ℝ] E} {G : E → E} {z₀ : E}
    {P' : E →L[ℝ] E →L[ℝ] E} {H : E →L[ℝ] E}
    (hP : HasFDerivAt P P' z₀) (hG : HasFDerivAt G H z₀) (hcrit : G z₀ = 0) :
    HasFDerivAt (fun z => -(P z (G z))) (-((P z₀).comp H)) z₀ := by
  simpa [hcrit] using (hP.clm_apply hG).neg

/-- A coercive self-adjoint Hessian controls its own squared norm.  This is the
spectral inequality needed for (5.2), proved directly using Cauchy--Schwarz. -/
theorem hessian_norm_sq_lower (H : E →L[ℝ] E) {h : ℝ} (hh : 0 ≤ h)
    (hcoerce : ∀ v : E, h * ‖v‖^2 ≤ energy H v) (v : E) :
    h * energy H v ≤ ‖H v‖^2 := by
  by_cases he : energy H v ≤ 0
  · exact (mul_nonpos_of_nonneg_of_nonpos hh he).trans (sq_nonneg _)
  · have hepos : 0 < energy H v := lt_of_not_ge he
    have hcs : energy H v ^ 2 ≤ ‖v‖^2 * ‖H v‖^2 := by
      simpa [energy, pow_two, real_inner_self_eq_norm_sq] using
        real_inner_mul_inner_self_le v (H v)
    have h1 := mul_le_mul_of_nonneg_left hcs hh
    have h2 := mul_le_mul_of_nonneg_right (hcoerce v) (sq_nonneg ‖H v‖)
    have h3 : energy H v * (h * energy H v) ≤ energy H v * ‖H v‖^2 := by
      nlinarith
    exact (mul_le_mul_left hepos).mp h3

/-- Linearization at a critical point of a preconditioned strongly convex gradient
flow is dissipative in the fixed Hessian metric, as in (5.2). -/
theorem linearization_dissipative (H P : E →L[ℝ] E)
    (hsymm : ∀ u v : E, ⟪u, H v⟫_ℝ = ⟪v, H u⟫_ℝ)
    {h p : ℝ} (hh : 0 ≤ h) (hp : 0 ≤ p)
    (hH : ∀ v : E, h * ‖v‖^2 ≤ energy H v)
    (hP : ∀ v : E, p * ‖v‖^2 ≤ ⟪v, P v⟫_ℝ) (v : E) :
    ⟪v, H (-(P (H v)))⟫_ℝ ≤ -(p*h) * energy H v := by
  have hlower := hessian_norm_sq_lower H hh hH v
  have hmul := mul_le_mul_of_nonneg_left hlower hp
  have hcoerce := hP (H v)
  rw [map_neg, inner_neg_right, hsymm]
  have hcomm : ⟪P (H v), H v⟫_ℝ = ⟪H v, P (H v)⟫_ℝ := real_inner_comm _ _
  rw [hcomm]
  nlinarith

/-- Actual Jacobian dissipativity for a preconditioned gradient field at a critical
point, combining its derivative identity and the two coercivity bounds. -/
theorem critical_point_dissipativity {P : E → E →L[ℝ] E} {G : E → E} {z₀ : E}
    {P' : E →L[ℝ] E →L[ℝ] E} {H : E →L[ℝ] E}
    (hP : HasFDerivAt P P' z₀) (hG : HasFDerivAt G H z₀) (hcrit : G z₀ = 0)
    (hsymm : ∀ u v : E, ⟪u, H v⟫_ℝ = ⟪v, H u⟫_ℝ)
    {h p : ℝ} (hh : 0 ≤ h) (hp : 0 ≤ p)
    (hH : ∀ v : E, h * ‖v‖^2 ≤ energy H v)
    (hPcoerce : ∀ v : E, p * ‖v‖^2 ≤ ⟪v, P z₀ v⟫_ℝ) (v : E) :
    ⟪v, H (fderiv ℝ (fun z => -(P z (G z))) z₀ v)⟫_ℝ ≤
      -(p*h) * energy H v := by
  rw [(gradient_flow_linearization hP hG hcrit).fderiv]
  simpa using linearization_dissipative H (P z₀) hsymm hh hp hH hPcoerce v

end Paper38.Stability
