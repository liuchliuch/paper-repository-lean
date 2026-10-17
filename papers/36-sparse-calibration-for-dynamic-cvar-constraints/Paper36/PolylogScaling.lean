import Paper36.SourceScaling

/-! Uniform multivariate parameter envelopes behind Theorem 4.2's soft-O text.
Every factor is explicit. In particular no polynomial dimension or rare-weight
dependence is hidden in an unnamed fixed-instance asymptotic coefficient. -/
namespace Paper36.PolylogScaling
noncomputable section

def B (s a h : ℝ) : ℝ := Real.log (h+1) + Real.log (8*s*a*h) + 6
def G (s a h : ℝ) : ℝ := (B s a h + 3*Target.M0 h)/2
def F (s a h w Δ : ℝ) : ℝ :=
  Real.sqrt (B s a h * Target.M0 h) + 2*G s a h *
    Real.log (1 + 16*Real.sqrt 2*G s a h*w*s*Real.sqrt a/Δ)

lemma B_nonneg {s a h : ℝ} (hs : 1 ≤ s) (ha : 1 ≤ a) (hh : 1 ≤ h) :
    0 ≤ B s a h := by
  have hsa := one_le_mul_of_one_le_of_one_le hs ha
  have hsah := one_le_mul_of_one_le_of_one_le hsa hh
  have hlog := Real.log_nonneg (show (1:ℝ) ≤ 8*s*a*h by nlinarith)
  have hlogh := Real.log_nonneg (show (1:ℝ) ≤ h+1 by linarith)
  unfold B
  linarith

lemma G_nonneg {s a h : ℝ} (hs : 1 ≤ s) (ha : 1 ≤ a) (hh : 1 ≤ h) :
    0 ≤ G s a h := by
  have hb := B_nonneg hs ha hh
  have hm := (Target.parameter_bounds hs ha hh).2.2
  unfold G
  linarith

lemma A0_le {s a h : ℝ} (hs : 1 ≤ s) (ha : 1 ≤ a) (hh : 1 ≤ h) :
    Target.A0 s a h ≤ s*B s a h := by
  have hsa := one_le_mul_of_one_le_of_one_le hs ha
  have hsah := one_le_mul_of_one_le_of_one_le hsa hh
  have hlog := Real.log_nonneg (show (1:ℝ) ≤ 8*s*a*h by nlinarith)
  unfold Target.A0 Target.lambda0 Target.nu B
  nlinarith [mul_nonneg (sub_nonneg.mpr hs) hlog]

lemma nu_le {s : ℝ} (hs : 1 ≤ s) : Target.nu s ≤ 3*s := by
  unfold Target.nu
  linarith

/-- The normalized dimension coefficients used in the paper's residual. -/
theorem normalized_parameters {s a h : ℝ} (hs : 1 ≤ s) (ha : 1 ≤ a) (hh : 1 ≤ h) :
    Target.A0 s a h / s ≤ B s a h ∧ Target.nu s / s ≤ 3 ∧
    Target.G₀ (Target.A0 s a h) (Target.M0 h) / Real.sqrt s ≤
      Real.sqrt (B s a h * Target.M0 h) ∧
    Target.gamma₀ (Target.A0 s a h) (Target.nu s) (Target.M0 h) / Real.sqrt s ≤ G s a h := by
  have hs0 : 0 < s := by linarith
  have hsqrt : 0 < Real.sqrt s := Real.sqrt_pos.2 hs0
  have hp := Target.parameter_bounds hs ha hh
  have hm : 0 ≤ Target.M0 h := by linarith [hp.2.2]
  have hb := B_nonneg hs ha hh
  have hg := G_nonneg hs ha hh
  have hA := A0_le hs ha hh
  have hν := nu_le hs
  have hAlower : s ≤ Target.A0 s a h := by
    have hn : s ≤ Target.nu s := by unfold Target.nu; linarith
    linarith [hp.2.1]
  have hprod : s ≤ Target.A0 s a h * Target.M0 h := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hAlower) hm]
  have hlower : Real.sqrt s ≤ Target.G₀ (Target.A0 s a h) (Target.M0 h) :=
    Real.sqrt_le_sqrt hprod
  have hGpos : 0 < Target.G₀ (Target.A0 s a h) (Target.M0 h) := lt_of_lt_of_le hsqrt hlower
  have hupper : Target.G₀ (Target.A0 s a h) (Target.M0 h) ≤
      Real.sqrt s * Real.sqrt (B s a h * Target.M0 h) := by
    unfold Target.G₀
    calc
      _ ≤ Real.sqrt (s * (B s a h * Target.M0 h)) :=
        Real.sqrt_le_sqrt (by nlinarith [mul_le_mul_of_nonneg_right hA hm])
      _ = _ := Real.sqrt_mul hs0.le _
  have hnum : Target.A0 s a h + Target.nu s * Target.M0 h ≤ 2*s*G s a h := by
    have hn := mul_le_mul_of_nonneg_right hν hm
    unfold G
    nlinarith
  have hden : 2*s*G s a h ≤
      (2*Target.G₀ (Target.A0 s a h) (Target.M0 h)) * (Real.sqrt s * G s a h) := by
    calc
      _ = (2*Real.sqrt s)*(Real.sqrt s*G s a h) := by
        calc
          _ = 2*(Real.sqrt s*Real.sqrt s)*G s a h := by rw [Real.mul_self_sqrt hs0.le]
          _ = _ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith : 2*Real.sqrt s ≤
        2*Target.G₀ (Target.A0 s a h) (Target.M0 h)) (mul_nonneg hsqrt.le hg)
  have hgamma : Target.gamma₀ (Target.A0 s a h) (Target.nu s) (Target.M0 h) ≤
      Real.sqrt s * G s a h := by
    unfold Target.gamma₀
    exact (div_le_iff₀ (by positivity : 0 < 2*Target.G₀ (Target.A0 s a h) (Target.M0 h))).2
      (by nlinarith [hnum.trans hden])
  exact ⟨(div_le_iff₀ hs0).2 (by nlinarith [hA]),
    (div_le_iff₀ hs0).2 (by linarith [hν]),
    (div_le_iff₀ hsqrt).2 (by nlinarith [hupper]),
    (div_le_iff₀ hsqrt).2 (by nlinarith [hgamma])⟩

lemma scale_mul_sqrt {s a w : ℝ} (hs : 0 ≤ s) :
    Target.scale w s a * Real.sqrt s = 4*Real.sqrt 2*w*s*Real.sqrt a := by
  unfold Target.scale
  rw [Real.sqrt_mul hs]
  calc
    _ = 4*Real.sqrt 2*w*(Real.sqrt s*Real.sqrt s)*Real.sqrt a := by ring
    _ = _ := by rw [Real.mul_self_sqrt hs]

/-- The exact normalized residual coefficient is bounded uniformly by F;
its dependence on w/Delta occurs only inside the displayed logarithm. -/
theorem residualLogFactor_le {s a h w Δ : ℝ} (hs : 1 ≤ s) (ha : 1 ≤ a)
    (hh : 1 ≤ h) (hw : 0 ≤ w) (hΔ : 0 < Δ) :
    SourceScaling.residualLogFactor s a h w Δ ≤ F s a h w Δ := by
  have hs0 : 0 < s := by linarith
  have hsqrt : 0 < Real.sqrt s := Real.sqrt_pos.2 hs0
  have hp := normalized_parameters hs ha hh
  have hg := G_nonneg hs ha hh
  have hparam := Target.parameter_bounds hs ha hh
  have hA : 0 ≤ Target.A0 s a h := by linarith [hparam.1,hparam.2.1]
  have hν : 0 ≤ Target.nu s := hparam.1.le
  have hm : 0 ≤ Target.M0 h := by linarith [hparam.2.2]
  have hgamma : 0 ≤ Target.gamma₀ (Target.A0 s a h) (Target.nu s) (Target.M0 h) := by
    unfold Target.gamma₀ Target.G₀
    positivity
  have hscale := Target.scale_nonneg (s := s) (a := a) hw
  have hrat : 0 ≤ Target.gamma₀ (Target.A0 s a h) (Target.nu s) (Target.M0 h) / Real.sqrt s :=
    div_nonneg hgamma hsqrt.le
  have harg : 4*Target.gamma₀ (Target.A0 s a h) (Target.nu s) (Target.M0 h) * Target.scale w s a / Δ ≤
      16*Real.sqrt 2*G s a h*w*s*Real.sqrt a/Δ := by
    have hb := (div_le_iff₀ hsqrt).1 hp.2.2.2
    calc
      _ = Target.gamma₀ (Target.A0 s a h) (Target.nu s) (Target.M0 h) *
        (4*Target.scale w s a/Δ) := by ring
      _ ≤ (G s a h*Real.sqrt s)*(4*Target.scale w s a/Δ) :=
        mul_le_mul_of_nonneg_right hb (by positivity)
      _ = (4*G s a h/Δ)*(Target.scale w s a*Real.sqrt s) := by ring
      _ = _ := by rw [scale_mul_sqrt hs0.le]; ring
  have hold : 0 ≤ Real.log (1 + 4*Target.gamma₀ (Target.A0 s a h) (Target.nu s) (Target.M0 h) * Target.scale w s a/Δ) :=
    Real.log_nonneg (by linarith [show 0 ≤ 4*Target.gamma₀ (Target.A0 s a h) (Target.nu s) (Target.M0 h) * Target.scale w s a/Δ by positivity])
  have hlog : Real.log (1 + 4*Target.gamma₀ (Target.A0 s a h) (Target.nu s) (Target.M0 h) * Target.scale w s a/Δ) ≤
      Real.log (1 + 16*Real.sqrt 2*G s a h*w*s*Real.sqrt a/Δ) :=
    Real.log_le_log (by positivity) (by linarith)
  have hmul := mul_le_mul hp.2.2.2 hlog hold hg
  unfold SourceScaling.residualLogFactor F
  have he : (Target.G₀ (Target.A0 s a h) (Target.M0 h) +
      2*Target.gamma₀ (Target.A0 s a h) (Target.nu s) (Target.M0 h)*
        Real.log (1+4*Target.gamma₀ (Target.A0 s a h) (Target.nu s) (Target.M0 h)*Target.scale w s a/Δ)) / Real.sqrt s =
      Target.G₀ (Target.A0 s a h) (Target.M0 h)/Real.sqrt s +
        2*(Target.gamma₀ (Target.A0 s a h) (Target.nu s) (Target.M0 h)/Real.sqrt s)*
          Real.log (1+4*Target.gamma₀ (Target.A0 s a h) (Target.nu s) (Target.M0 h)*Target.scale w s a/Δ) := by ring
  rw [he]
  nlinarith [hp.2.2.1]

/-- The source residual has the advertised S^2 A W^2/Delta prefactor and a
uniform explicit polylogarithmic remainder. -/
theorem residual_uniform {s a h w Δ : ℝ} (hs : 1 ≤ s) (ha : 1 ≤ a)
    (hh : 1 ≤ h) (hw : 0 ≤ w) (hΔ : 0 < Δ) :
    BankTarget.paperResidual s a h w Δ ≤ 16*s^2*a*w^2/Δ * (F s a h w Δ)^2 := by
  have hs0 : 0 < s := by linarith
  have hcoef : 0 ≤ 16*s^2*a*w^2/Δ := by positivity
  have hlow : 0 ≤ SourceScaling.residualLogFactor s a h w Δ := by
    unfold SourceScaling.residualLogFactor
    have hp := Target.parameter_bounds hs ha hh
    have hA : 0 ≤ Target.A0 s a h := by linarith [hp.1,hp.2.1]
    have hm : 0 ≤ Target.M0 h := by linarith [hp.2.2]
    have hν := hp.1.le
    have hg : 0 ≤ Target.gamma₀ (Target.A0 s a h) (Target.nu s) (Target.M0 h) := by
      unfold Target.gamma₀ Target.G₀; positivity
    have hc := Target.scale_nonneg (s := s) (a := a) hw
    have hl := Real.log_nonneg (show (1:ℝ) ≤ 1+4*Target.gamma₀ (Target.A0 s a h) (Target.nu s) (Target.M0 h)*Target.scale w s a/Δ by
      linarith [show 0 ≤ 4*Target.gamma₀ (Target.A0 s a h) (Target.nu s) (Target.M0 h)*Target.scale w s a/Δ by positivity])
    exact div_nonneg (add_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (mul_nonneg (by norm_num) hg) hl)) (Real.sqrt_nonneg s)
  rw [SourceScaling.residual_parameter_identity hs0 (by linarith) hΔ]
  exact mul_le_mul_of_nonneg_left (by nlinarith [residualLogFactor_le hs ha hh hw hΔ]) hcoef

/-- The source target, with uniform S sqrt(A) W sqrt(K) prefactor. -/
theorem target_uniform {s a h w : ℝ} (hs : 1 ≤ s) (ha : 1 ≤ a)
    (hh : 1 ≤ h) (hw : 0 ≤ w) {K : ℕ} (hK : 1 ≤ K) :
    BankTarget.paperTarget s a h w K ≤ 4*Real.sqrt 2*w*s*Real.sqrt a*Real.sqrt (K:ℝ)*
      Real.sqrt ((B s a h+3*Real.log (K:ℝ))*(Target.M0 h+Real.log (K:ℝ))) := by
  have hs0 : 0 ≤ s := by linarith
  have hk0 := Nat.cast_nonneg (α := ℝ) K
  have hl : 0 ≤ Real.log (K:ℝ) := Real.log_nonneg (by exact_mod_cast hK)
  have hp := Target.parameter_bounds hs ha hh
  have hm : 0 ≤ Target.M0 h+Real.log (K:ℝ) := by linarith [hp.2.2]
  have hfactor : Target.A0 s a h+Target.nu s*Real.log (K:ℝ) ≤ s*(B s a h+3*Real.log (K:ℝ)) := by
    have hn := mul_le_mul_of_nonneg_right (nu_le hs) hl
    nlinarith [A0_le hs ha hh]
  have hroot := Real.sqrt_le_sqrt
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hfactor hk0) hm)
  have hscale := Target.scale_nonneg (s := s) (a := a) hw
  have hbound := mul_le_mul_of_nonneg_left hroot hscale
  unfold BankTarget.paperTarget Target.target
  rw [if_neg (show K ≠ 0 by omega)]
  calc
    _ ≤ Target.scale w s a * Real.sqrt ((K:ℝ)*(s*(B s a h+3*Real.log (K:ℝ)))*(Target.M0 h+Real.log (K:ℝ))) := hbound
    _ = Target.scale w s a * (Real.sqrt s * Real.sqrt (K:ℝ) *
        Real.sqrt ((B s a h+3*Real.log (K:ℝ))*(Target.M0 h+Real.log (K:ℝ)))) := by
      congr 1
      rw [show (K:ℝ)*(s*(B s a h+3*Real.log (K:ℝ)))*(Target.M0 h+Real.log (K:ℝ)) =
        s*((K:ℝ)*((B s a h+3*Real.log (K:ℝ))*(Target.M0 h+Real.log (K:ℝ)))) by ring,
        Real.sqrt_mul hs0, Real.sqrt_mul hk0]
      ring
    _ = _ := by rw [← mul_assoc, ← mul_assoc, scale_mul_sqrt hs0]

/-- The reward-model term has a uniform S sqrt(A) H^(3/2) sqrt(K)
prefactor; the remaining dimension dependence occurs only in logarithms. -/
theorem reward_model_uniform {s a h : ℝ} (hs : 1 ≤ s) (ha : 1 ≤ a)
    (hh : 1 ≤ h) {K : ℕ} (hK : 1 ≤ K) :
    8*h*Real.sqrt h*Real.sqrt (s*a*(K:ℝ)*Bounds.rewardLog s a h K) ≤
      8*s*Real.sqrt a*h*Real.sqrt h*Real.sqrt (K:ℝ)*
        Real.sqrt (Real.log 2+Real.log (8*s*a*h*(K:ℝ)^2)) := by
  have hs0 : 0 ≤ s := by linarith
  have ha0 : 0 ≤ a := by linarith
  have hk0 := Nat.cast_nonneg (α := ℝ) K
  have hlog := Real.log_nonneg (show (1:ℝ) ≤ Bounds.budget s a h K from (by have := Bounds.budget_lower hs ha hh hK; linarith))
  have hL : Bounds.rewardLog s a h K ≤ s*(Real.log 2+Real.log (Bounds.budget s a h K)) := by
    unfold Bounds.rewardLog
    nlinarith [mul_nonneg (sub_nonneg.mpr hs) hlog]
  have hroot := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hL
    (show 0 ≤ s*a*(K:ℝ) by positivity))
  calc
    _ ≤ 8*h*Real.sqrt h*Real.sqrt (s*a*(K:ℝ)*(s*(Real.log 2+Real.log (Bounds.budget s a h K)))) :=
      mul_le_mul_of_nonneg_left hroot (by positivity)
    _ = _ := by
      rw [show s*a*(K:ℝ)*(s*(Real.log 2+Real.log (Bounds.budget s a h K))) =
        s^2*(a*((K:ℝ)*(Real.log 2+Real.log (Bounds.budget s a h K)))) by ring,
        Real.sqrt_mul (sq_nonneg s), Real.sqrt_sq hs0, Real.sqrt_mul ha0, Real.sqrt_mul hk0]
      unfold Bounds.budget
      ring

/-- The first transition term alone gives W >= H for every source H >= 2. -/
theorem horizon_le_W {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {H : ℕ} (hH : 2 ≤ H) :
    (H : ℝ) ≤ Weights.W α H := by
  have hmem : 1 ∈ Finset.Icc 1 (H-1) := by simp; omega
  have hterm := Finset.single_le_sum
    (f := fun j : ℕ => ((H-j+1 : ℕ) : ℝ)^2*(α⁻¹)^j)
    (fun j _ => by positivity) hmem
  have hind : H-1+1=H := by omega
  simp only [pow_one, hind] at hterm
  have hinv : 1 ≤ α⁻¹ := (one_le_inv₀ hα).2 hα1
  have hsq : (H : ℝ)^2 ≤ Weights.Wsq α H := by
    change (H : ℝ)^2*α⁻¹ ≤ Weights.Wsq α H at hterm
    nlinarith [mul_nonneg (sq_nonneg (H:ℝ)) (sub_nonneg.mpr hinv)]
  exact (Real.le_sqrt (Nat.cast_nonneg H) (Weights.Wsq_nonneg hα H)).2 hsq

/-- The same first-stage argument applies to the heterogeneous prefix-product
weight in B.3; only beta(1) is needed for its lower bound. -/
theorem horizon_le_stageW (β : ℕ → ℝ) (hβ : ∀ j, 0 < β j ∧ β j ≤ 1)
    {H : ℕ} (hH : 2 ≤ H) : (H : ℝ) ≤ Real.sqrt (Weights.stageWsq β H) := by
  have hmem : 1 ∈ Finset.Icc 1 (H-1) := by simp; omega
  have hpos (j : ℕ) : 0 < Weights.prefixMass β j :=
    Weights.prefixMass_pos (fun i _ => (hβ i).1)
  have hterm := Finset.single_le_sum
    (f := fun j : ℕ => ((H-j+1 : ℕ) : ℝ)^2/Weights.prefixMass β j)
    (fun j _ => div_nonneg (sq_nonneg _) (hpos j).le) hmem
  have hind : H-1+1=H := by omega
  have hfirst : Weights.prefixMass β 1 = β 1 := by simp [Weights.prefixMass]
  simp only [hind, hfirst] at hterm
  have hsq : (H : ℝ)^2 ≤ Weights.stageWsq β H := by
    change (H : ℝ)^2/β 1 ≤ Weights.stageWsq β H at hterm
    exact ((le_div_iff₀ (hβ 1).1).2
      (by nlinarith [mul_nonneg (sq_nonneg (H:ℝ)) (sub_nonneg.mpr (hβ 1).2)])).trans hterm
  have hnonneg : 0 ≤ Weights.stageWsq β H :=
    Finset.sum_nonneg (fun j _ => div_nonneg (sq_nonneg _) (hpos j).le)
  exact (Real.le_sqrt (Nat.cast_nonneg H) hnonneg).2 hsq

def rewardPolylog (s a h : ℝ) (K : ℕ) : ℝ :=
  8*Real.sqrt (Real.log 2+Real.log (8*s*a*h*(K:ℝ)^2)) +
    4*Real.sqrt 2*Real.sqrt ((B s a h+3*Real.log (K:ℝ))*(Target.M0 h+Real.log (K:ℝ))) + 3/2

/-- A uniform literal version of the source multivariate soft-O reward bound.
The displayed multiplier contains only logarithms of dimensions and K. -/
theorem reward_performance_uniform {s a h w Δ τ : ℝ} (hs : 1 ≤ s) (ha : 1 ≤ a)
    (hh : 1 ≤ h) (hw : h ≤ w) (hΔ : 0 < Δ) (hτ : τ ≤ Δ+h)
    {K : ℕ} (hK : 1 ≤ K) :
    8*h*Real.sqrt h*Real.sqrt (s*a*(K:ℝ)*Bounds.rewardLog s a h K)+h/2+
      h*((BankTarget.paperTarget s a h w K+τ)/Δ) ≤
      s*Real.sqrt a*(h*Real.sqrt h+h*w/Δ)*Real.sqrt (K:ℝ)*rewardPolylog s a h K := by
  let U := Real.sqrt ((B s a h+3*Real.log (K:ℝ))*(Target.M0 h+Real.log (K:ℝ)))
  let V := Real.sqrt (Real.log 2+Real.log (8*s*a*h*(K:ℝ)^2))
  let p := s*Real.sqrt a*h*Real.sqrt h*Real.sqrt (K:ℝ)
  let q := s*Real.sqrt a*h*w/Δ*Real.sqrt (K:ℝ)
  have hs0 : 0 ≤ s := by linarith
  have hh0 : 0 ≤ h := by linarith
  have hw0 : 0 ≤ w := by linarith
  have ha0 : 0 ≤ a := by linarith
  have hk0 := Nat.cast_nonneg (α := ℝ) K
  have hp0 : 0 ≤ p := by dsimp [p]; positivity
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hU : 0 ≤ U := Real.sqrt_nonneg _
  have hV : 0 ≤ V := Real.sqrt_nonneg _
  have hsa : 1 ≤ s*Real.sqrt a*Real.sqrt (K:ℝ) :=
    one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le hs ((Real.le_sqrt (by norm_num) ha0).2 (by simpa using ha)))
      ((Real.le_sqrt (by norm_num) hk0).2 (by simpa using (show (1:ℝ)≤K by exact_mod_cast hK)))
  have hsh : 1 ≤ Real.sqrt h := (Real.le_sqrt (by norm_num) hh0).2 (by simpa using hh)
  have hp : h ≤ p := by
    have hm := mul_le_mul_of_nonneg_right (one_le_mul_of_one_le_of_one_le hsa hsh) hh0
    dsimp [p]
    nlinarith [hm]
  have hq : h^2/Δ ≤ q := by
    have hsw : h ≤ (s*Real.sqrt a*Real.sqrt (K:ℝ))*w :=
      hw.trans (by nlinarith [mul_nonneg (sub_nonneg.mpr hsa) hw0])
    have hm := mul_le_mul_of_nonneg_left hsw (show 0 ≤ h/Δ by positivity)
    dsimp [q]
    convert hm using 1 <;> ring
  have htau : h*τ/Δ ≤ h+h^2/Δ := by
    calc
      _ ≤ h*(Δ+h)/Δ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hτ hh0) hΔ.le
      _ = _ := by field_simp
  have hconstant : h/2+h*τ/Δ ≤ (3/2)*(p+q) := by linarith
  have hr : 8*h*Real.sqrt h*Real.sqrt (s*a*(K:ℝ)*Bounds.rewardLog s a h K) ≤ 8*p*V := by
    convert reward_model_uniform hs ha hh hK using 1
    dsimp [p,V]
    ring
  have ht : h*BankTarget.paperTarget s a h w K/Δ ≤ 4*Real.sqrt 2*q*U := by
    have hb := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (target_uniform hs ha hh hw0 hK) hh0) hΔ.le
    convert hb using 1
    dsimp [q,U]
    ring
  calc
    _ = 8*h*Real.sqrt h*Real.sqrt (s*a*(K:ℝ)*Bounds.rewardLog s a h K)+
        h*BankTarget.paperTarget s a h w K/Δ+(h/2+h*τ/Δ) := by ring
    _ ≤ 8*p*V+4*Real.sqrt 2*q*U+(3/2)*(p+q) := add_le_add (add_le_add hr ht) hconstant
    _ ≤ (p+q)*(8*V+4*Real.sqrt 2*U+3/2) := by
      nlinarith [mul_nonneg hp0 hU, mul_nonneg hq0 hV,
        mul_nonneg (mul_nonneg (Real.sqrt_nonneg (2:ℝ)) hp0) hU]
    _ = _ := by unfold rewardPolylog; dsimp [p,q,U,V]; ring

end
end Paper36.PolylogScaling
