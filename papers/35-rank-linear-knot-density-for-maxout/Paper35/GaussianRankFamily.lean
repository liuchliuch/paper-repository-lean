import Paper35.GaussianFactors
import Paper35.GaussianLayer
import Paper35.GaussianMomentTail
import Mathlib.Analysis.Asymptotics.Theta

/-!
# Strict Gaussian rank-family orders from source §8.p13

The family consists of actual `GaussianLayer.Layer` models, indexed by a real
parameter R tending to +infinity and a fixed finite depth. Widths, input
dimensions, candidate ranks, bias scales, and covariance matrices may vary
with R. `UniformBounds` records precisely the source quantitative hypotheses.

The source factors are the exact D and A of (8.17)--(8.18), not unrelated
numerical sequences. We first prove finite-width Rayleigh/spectral bounds,
then uniformly compare all ranks aR≤K≤bR with log R. Upper orders require no
lower nondegeneracy. Theta orders require one uniformly positive covariance
eigenvalue in each layer; the witnessing unit may change with R and the layer.
The only classical asymptotic input is the already registered scalar
`GaussianExtremeMeanLaw`; no network asymptotic is assumed.
-/

noncomputable section
open Set Filter Matrix
open scoped Topology BigOperators

namespace Paper35.GaussianRankFamily
open Source Deep GaussianIndependent GaussianFactors GaussianLayer

def logScale (R : ℝ) : ℝ := Real.sqrt (Real.log R)

/-- Linear rank comparison gives logarithmic comparison uniformly over every
rank in the allowed interval, not only along a separately fixed sequence. -/
lemma eventually_log_comparison (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ∀ᶠ R : ℝ in atTop, ∀ K : ℕ, a*(R : ℝ) ≤ K → (K : ℝ) ≤ b*R →
      (1/2 : ℝ)*Real.log R ≤ Real.log K ∧ Real.log K ≤ 2*Real.log R := by
  have hlog : ∀ᶠ R : ℝ in atTop,
      max (2*|Real.log a|) (|Real.log b|) ≤ Real.log R :=
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop _)
  filter_upwards [hlog, eventually_ge_atTop (1 : ℝ)] with R hR hRp
  intro K hKa hKb
  have hRpos : (0 : ℝ) < R := lt_of_lt_of_le zero_lt_one hRp
  have hKpos : (0 : ℝ) < K := lt_of_lt_of_le (mul_pos ha hRpos) hKa
  have hlo := Real.log_le_log (mul_pos ha hRpos) hKa
  have hup := Real.log_le_log hKpos hKb
  rw [Real.log_mul ha.ne' hRpos.ne'] at hlo
  rw [Real.log_mul hb.ne' hRpos.ne'] at hup
  constructor
  · nlinarith [le_abs_self (-Real.log a), abs_neg (Real.log a), (le_max_left _ _).trans hR]
  · nlinarith [le_abs_self (Real.log b), (le_max_right _ _).trans hR]

lemma eventually_rank_above (a : ℝ) (ha : 0 < a) (N : ℕ) :
    ∀ᶠ R : ℝ in atTop, ∀ K : ℕ, a*(R : ℝ) ≤ K → N ≤ K := by
  filter_upwards [eventually_ge_atTop ((N : ℝ)/a)] with R hR
  intro K hK
  have hRN : (N : ℝ)/a ≤ R := hR
  have hNR : (N : ℝ) ≤ a*R := by nlinarith [(div_le_iff₀ ha).mp hRN]
  exact_mod_cast hNR.trans hK

/-- Quantitative simultaneous bounds for the actual c_K and q_K under
aR≤K≤bR. The only classical asymptotic input concerns the scalar maximum mean. -/
theorem eventually_rank_scalar_bounds
    (hext : Paper35.RankAsymptotics.GaussianExtremeMeanLaw)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ∀ᶠ R : ℝ in atTop, ∀ K : ℕ, a*(R : ℝ) ≤ K → (K : ℝ) ≤ b*R →
      (1/(2*Real.sqrt Real.pi))*logScale R ≤ Paper35.gaussianRankCoefficient K ∧
      Paper35.gaussianRankCoefficient K ≤ (4/Real.sqrt Real.pi)*logScale R ∧
      (1/4 : ℝ)*Real.log R ≤ gaussianLengthCorrection K ∧
      gaussianLengthCorrection K ≤ 12*Real.log R := by
  have hmean : ∀ᶠ K : ℕ in atTop,
      (1/2 : ℝ) ≤ Paper35.gaussianMaxMean K / Real.sqrt (2*Real.log K) ∧
      Paper35.gaussianMaxMean K / Real.sqrt (2*Real.log K) ≤ 2 := by
    filter_upwards [(tendsto_order.mp hext.1).1 (1/2) (by norm_num),
      (tendsto_order.mp hext.1).2 2 (by norm_num)] with K hlo hhi
    exact ⟨hlo.le,hhi.le⟩
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hmean.and
    (GaussianMomentTail.gaussianLengthCorrection_eventual_bounds hext))
  filter_upwards [eventually_log_comparison a b ha hb,
    eventually_rank_above a ha (max N 2)] with R hlog hlarge
  intro K hKa hKb
  have hKN : N ≤ K := (le_max_left _ _).trans (hlarge K hKa)
  have hK2 : 2 ≤ K := (le_max_right _ _).trans (hlarge K hKa)
  obtain ⟨hmeanK,hq⟩ := hN K hKN
  obtain ⟨hlo,hhi⟩ := hlog K hKa hKb
  have hlogK : 0 < Real.log K := Real.log_pos (by exact_mod_cast (show 1 < K by omega))
  have hsK : 0 < Real.sqrt (2*Real.log K) := Real.sqrt_pos.mpr (by positivity)
  have hmlo := (le_div_iff₀ hsK).mp hmeanK.1
  have hmhi := (div_le_iff₀ hsK).mp hmeanK.2
  have hrootlo : logScale R ≤ Real.sqrt (2*Real.log K) := Real.sqrt_le_sqrt (by linarith)
  have hroothi : Real.sqrt (2*Real.log K) ≤ 2*logScale R := by
    have H := Real.sqrt_le_sqrt (show 2*Real.log K ≤ 4*Real.log R by linarith)
    simpa only [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4),
      show Real.sqrt (4 : ℝ) = 2 by norm_num, logScale] using H
  have hp : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  refine ⟨?_,?_,by linarith [hq.1],by linarith [hq.2]⟩
  · change _ ≤ Paper35.gaussianMaxMean K / Real.sqrt Real.pi
    calc
      _ = ((1/2 : ℝ)*logScale R)/Real.sqrt Real.pi := by ring
      _ ≤ _ := div_le_div_of_nonneg_right (by linarith) hp.le
  · change Paper35.gaussianMaxMean K / Real.sqrt Real.pi ≤ _
    calc
      _ ≤ (4*logScale R)/Real.sqrt Real.pi := div_le_div_of_nonneg_right (by linarith) hp.le
      _ = _ := by ring

/-- Uniform finite-width Rayleigh-cost bound for the actual Gaussian D factor. -/
theorem D_le_uniform {d q : ℕ} (K : Fin q → ℕ)
    (C : Fin q → Matrix (Fin d) (Fin d) ℝ) (σ : Fin q → ℝ)
    (Q : ℕ) (hq : q ≤ Q) (T β σlo Cmax : ℝ)
    (hT : 0 ≤ T) (hβ : 0 ≤ β) (hσlo : 0 < σlo)
    (hσ : ∀ r, σlo ≤ σ r)
    (hc : ∀ r, Paper35.gaussianRankCoefficient (K r) ≤ β*T)
    (hC : ∀ r, covarianceMax (C r) ≤ Cmax) :
    D K C σ ≤ ((Q : ℝ)*β/σlo*Real.sqrt Cmax)*T := by
  have hσpos r : 0 < σ r := lt_of_lt_of_le hσlo (hσ r)
  have hβT : 0 ≤ β*T := mul_nonneg hβ hT
  calc
    _ ≤ ∑ r, Paper35.gaussianRankCoefficient (K r)/σ r*Real.sqrt (covarianceMax (C r)) :=
      D_upper K C σ hσpos
    _ ≤ ∑ _r : Fin q, (β*T/σlo)*Real.sqrt Cmax := by
      apply Finset.sum_le_sum
      intro r _
      have hdiv : Paper35.gaussianRankCoefficient (K r)/σ r ≤ β*T/σlo :=
        (div_le_div_of_nonneg_right (hc r) (hσpos r).le).trans
          (div_le_div_of_nonneg_left hβT hσlo (hσ r))
      exact mul_le_mul hdiv (Real.sqrt_le_sqrt (hC r)) (Real.sqrt_nonneg _)
        (div_nonneg hβT hσlo.le)
    _ = (q : ℝ)*((β*T/σlo)*Real.sqrt Cmax) := by simp
    _ ≤ (Q : ℝ)*((β*T/σlo)*Real.sqrt Cmax) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hq)
        (mul_nonneg (div_nonneg hβT hσlo.le) (Real.sqrt_nonneg _))
    _ = _ := by ring

/-- Uniform finite-width spectral bound for the actual Gaussian A factor. -/
theorem A_le_uniform {d q : ℕ} (K : Fin q → ℕ)
    (C : Fin q → Matrix (Fin d) (Fin d) ℝ) (Q : ℕ) (hq : q ≤ Q)
    (T γ Cmax : ℝ) (hT : 0 ≤ T) (hγ : 0 ≤ γ) (hCmax : 0 ≤ Cmax)
    (hqK : ∀ r, gaussianLengthCorrection (K r) ≤ γ*T^2)
    (hC : ∀ r, covarianceMax (C r) ≤ Cmax) :
    A K C ≤ Real.sqrt ((Q : ℝ)*γ*Cmax)*T := by
  calc
    _ ≤ Real.sqrt (∑ r, gaussianLengthCorrection (K r)*covarianceMax (C r)) := A_upper K C
    _ ≤ Real.sqrt ((Q : ℝ)*γ*Cmax*T^2) := by
      apply Real.sqrt_le_sqrt
      calc
        _ ≤ ∑ _r : Fin q, (γ*T^2)*Cmax := by
          apply Finset.sum_le_sum
          intro r _
          exact mul_le_mul (hqK r) (hC r) (norm_nonneg _)
            (mul_nonneg hγ (sq_nonneg _))
        _ = (q : ℝ)*((γ*T^2)*Cmax) := by simp
        _ ≤ (Q : ℝ)*((γ*T^2)*Cmax) := mul_le_mul_of_nonneg_right (by exact_mod_cast hq)
          (mul_nonneg (mul_nonneg hγ (sq_nonneg _)) hCmax)
        _ = _ := by ring
    _ = _ := by rw [Real.sqrt_mul (mul_nonneg (mul_nonneg (by positivity) hγ) hCmax), Real.sqrt_sq hT]

theorem D_ge_uniform {d q : ℕ} (K : Fin q → ℕ)
    (C : Fin q → Matrix (Fin d) (Fin d) ℝ) (σ : Fin q → ℝ)
    (hC : ∀ r, (C r).PosSemidef) (hσ : ∀ r, 0 < σ r)
    (j : Fin q) (T α σhi c : ℝ)
    (hσhi : 0 < σhi) (hσj : σ j ≤ σhi) (hc : 0 < c)
    (hCovLow : c ≤ covarianceMax (C j)) (hcK : α*T ≤ Paper35.gaussianRankCoefficient (K j)) :
    (α/σhi*Real.sqrt c)*T ≤ D K C σ := by
  calc
    _ = (α*T/σhi)*Real.sqrt c := by ring
    _ ≤ (Paper35.gaussianRankCoefficient (K j)/σhi)*Real.sqrt c :=
      mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hcK hσhi.le) (Real.sqrt_nonneg _)
    _ ≤ (Paper35.gaussianRankCoefficient (K j)/σ j)*Real.sqrt c :=
      mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left
        (Paper35.gaussianRankCoefficient_nonneg _) (hσ j) hσj) (Real.sqrt_nonneg _)
    _ ≤ (Paper35.gaussianRankCoefficient (K j)/σ j)*Real.sqrt (covarianceMax (C j)) :=
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hCovLow)
        (div_nonneg (Paper35.gaussianRankCoefficient_nonneg _) (hσ j).le)
    _ ≤ _ := D_lower K C σ hC hσ j (lt_of_lt_of_le hc hCovLow)

theorem A_ge_uniform {d q : ℕ} (K : Fin q → ℕ)
    (C : Fin q → Matrix (Fin d) (Fin d) ℝ) (hC : ∀ r, (C r).PosSemidef)
    (j : Fin q) (T γ c : ℝ) (hT : 0 ≤ T) (hγ : 0 ≤ γ) (hc : 0 < c)
    (hCovLow : c ≤ covarianceMax (C j)) (hqK : γ*T^2 ≤ gaussianLengthCorrection (K j)) :
    Real.sqrt (γ*c)*T ≤ A K C := by
  calc
    _ = Real.sqrt ((γ*T^2)*c) := by
      rw [show (γ*T^2)*c = (γ*c)*T^2 by ring,
        Real.sqrt_mul (mul_nonneg hγ hc.le), Real.sqrt_sq hT]
    _ ≤ Real.sqrt (gaussianLengthCorrection (K j)*covarianceMax (C j)) := by
      apply Real.sqrt_le_sqrt
      exact mul_le_mul hqK hCovLow hc.le
        ((by norm_num : (0 : ℝ) ≤ 1).trans (gaussianLengthCorrection_ge_one _))
    _ ≤ _ := A_lower K C hC j (lt_of_lt_of_le hc hCovLow)

/-- An actual family of Gaussian layers. Both input dimension and width may
vary with R; depth is fixed and each layer retains its genuine marginal laws. -/
structure Family (depth : ℕ) where
  dim : ℝ → Fin depth → ℕ
  width : ℝ → Fin depth → ℕ
  layer : (R : ℝ) → (ℓ : Fin depth) → Layer (dim R ℓ) (width R ℓ)

namespace Family
variable {depth : ℕ} (f : Family depth)

def rank (R : ℝ) (ℓ : Fin depth) (r : Fin (f.width R ℓ)) : ℕ :=
  (f.layer R ℓ).rankMinusOne r + 1

def switchFactor (R : ℝ) (ℓ : Fin depth) : ℝ :=
  D (f.rank R ℓ) (fun r => ((f.layer R ℓ).unit r).covariance)
    (fun r => ((f.layer R ℓ).unit r).biasSd)

def lengthFactor (R : ℝ) (ℓ : Fin depth) : ℝ :=
  A (f.rank R ℓ) (fun r => ((f.layer R ℓ).unit r).covariance)

/-- Exactly the source uniform hypotheses on the actual ranks, bias scales,
covariance operator norms, and finite widths. No order bound is a field. -/
structure UniformBounds where
  a : ℝ
  b : ℝ
  σlo : ℝ
  σhi : ℝ
  C : ℝ
  Q : ℕ
  a_pos : 0 < a
  a_le_b : a ≤ b
  σlo_pos : 0 < σlo
  σlo_le_σhi : σlo ≤ σhi
  bounds : ∀ᶠ R : ℝ in atTop, ∀ ℓ : Fin depth,
    f.width R ℓ ≤ Q ∧ ∀ r : Fin (f.width R ℓ),
      a*(R : ℝ) ≤ f.rank R ℓ r ∧ (f.rank R ℓ r : ℝ) ≤ b*R ∧
      σlo ≤ ((f.layer R ℓ).unit r).biasSd ∧ ((f.layer R ℓ).unit r).biasSd ≤ σhi ∧
      covarianceMax ((f.layer R ℓ).unit r).covariance ≤ C

def Dupper (u : f.UniformBounds) : ℝ :=
  (u.Q : ℝ)*(4/Real.sqrt Real.pi)/u.σlo*Real.sqrt (max u.C 0)

def Aupper (u : f.UniformBounds) : ℝ := Real.sqrt ((u.Q : ℝ)*12*(max u.C 0))

/-- Quantitative uniform O(sqrt(log R)) bounds for both source factors,
simultaneously for every layer and every actual unit in the family. -/
theorem eventual_upper_bounds
    (hext : Paper35.RankAsymptotics.GaussianExtremeMeanLaw) (u : f.UniformBounds) :
    ∀ᶠ R : ℝ in atTop, ∀ ℓ : Fin depth,
      0 ≤ f.switchFactor R ℓ ∧ f.switchFactor R ℓ ≤ f.Dupper u * logScale R ∧
      0 ≤ f.lengthFactor R ℓ ∧ f.lengthFactor R ℓ ≤ f.Aupper u * logScale R := by
  filter_upwards [u.bounds, eventually_rank_scalar_bounds hext u.a u.b u.a_pos
    (lt_of_lt_of_le u.a_pos u.a_le_b), eventually_ge_atTop (1 : ℝ)] with R hR hs hRone
  intro ℓ
  obtain ⟨hq,hr⟩ := hR ℓ
  have hscalar r := hs (f.rank R ℓ r) (hr r).1 (hr r).2.1
  have hqK r : gaussianLengthCorrection (f.rank R ℓ r) ≤ 12*(logScale R)^2 := by
    rw [logScale, Real.sq_sqrt (Real.log_nonneg hRone)]
    exact (hscalar r).2.2.2
  refine ⟨D_nonneg _ _ _ (fun r => ((f.layer R ℓ).unit r).biasSd_pos), ?_, A_nonneg _ _, ?_⟩
  · exact D_le_uniform _ _ _ u.Q hq (logScale R) (4/Real.sqrt Real.pi) u.σlo (max u.C 0)
      (Real.sqrt_nonneg _) (by positivity) u.σlo_pos (fun r => (hr r).2.2.1)
      (fun r => (hscalar r).2.1) (fun r => (hr r).2.2.2.2.trans (le_max_left _ _))
  · exact A_le_uniform _ _ u.Q hq (logScale R) 12 (max u.C 0) (Real.sqrt_nonneg _)
      (by norm_num) (le_max_right _ _) hqK (fun r => (hr r).2.2.2.2.trans (le_max_left _ _))

/-- Original upper-order claim, expressed with mathlib's IsBigO. Constants
in `eventual_upper_bounds` are independent of the layer index. -/
theorem factors_isBigO
    (hext : Paper35.RankAsymptotics.GaussianExtremeMeanLaw) (u : f.UniformBounds) :
    (∀ ℓ : Fin depth, Asymptotics.IsBigO atTop (fun R => f.switchFactor R ℓ) logScale) ∧
    (∀ ℓ : Fin depth, Asymptotics.IsBigO atTop (fun R => f.lengthFactor R ℓ) logScale) := by
  constructor
  · intro ℓ
    apply Asymptotics.isBigO_iff.mpr
    refine ⟨f.Dupper u, ?_⟩
    filter_upwards [f.eventual_upper_bounds hext u] with R hR
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hR ℓ).1,
      abs_of_nonneg (show 0 ≤ logScale R from Real.sqrt_nonneg _)] using (hR ℓ).2.1
  · intro ℓ
    apply Asymptotics.isBigO_iff.mpr
    refine ⟨f.Aupper u, ?_⟩
    filter_upwards [f.eventual_upper_bounds hext u] with R hR
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hR ℓ).2.2.1,
      abs_of_nonneg (show 0 ≤ logScale R from Real.sqrt_nonneg _)] using (hR ℓ).2.2.2

def Dlower (u : f.UniformBounds) (c : ℝ) : ℝ :=
  (1/(2*Real.sqrt Real.pi))/u.σhi*Real.sqrt c

def Alower (c : ℝ) : ℝ := Real.sqrt ((1/4 : ℝ)*c)

/-- The lower nondegeneracy assumption is exactly one uniformly positive
largest covariance eigenvalue in every layer. The witnessing unit may depend
on R and on the layer. -/
theorem eventual_lower_bounds
    (hext : Paper35.RankAsymptotics.GaussianExtremeMeanLaw) (u : f.UniformBounds)
    (c : ℝ) (hc : 0 < c)
    (hnd : ∀ᶠ R : ℝ in atTop, ∀ ℓ : Fin depth, ∃ r : Fin (f.width R ℓ),
      c ≤ covarianceMax ((f.layer R ℓ).unit r).covariance) :
    ∀ᶠ R : ℝ in atTop, ∀ ℓ : Fin depth,
      f.Dlower u c * logScale R ≤ f.switchFactor R ℓ ∧
      Alower c * logScale R ≤ f.lengthFactor R ℓ := by
  filter_upwards [u.bounds, eventually_rank_scalar_bounds hext u.a u.b u.a_pos
    (lt_of_lt_of_le u.a_pos u.a_le_b), hnd, eventually_ge_atTop (1 : ℝ)] with R hR hs hnondeg hRone
  intro ℓ
  obtain ⟨j,hj⟩ := hnondeg ℓ
  have hr := (hR ℓ).2
  have hscalar := hs (f.rank R ℓ j) (hr j).1 (hr j).2.1
  have hqK : (1/4 : ℝ)*(logScale R)^2 ≤ gaussianLengthCorrection (f.rank R ℓ j) := by
    rw [logScale, Real.sq_sqrt (Real.log_nonneg hRone)]
    exact hscalar.2.2.1
  constructor
  · exact D_ge_uniform _ _ _ (fun r => ((f.layer R ℓ).unit r).covariance_psd)
      (fun r => ((f.layer R ℓ).unit r).biasSd_pos) j (logScale R)
      (1/(2*Real.sqrt Real.pi)) u.σhi c
      (lt_of_lt_of_le u.σlo_pos u.σlo_le_σhi) (hr j).2.2.2.1 hc hj hscalar.1
  · exact A_ge_uniform _ _ (fun r => ((f.layer R ℓ).unit r).covariance_psd) j
      (logScale R) (1/4) c (Real.sqrt_nonneg _) (by norm_num) hc hj hqK

/-- Full strict rank-family Theta claim of source §8.p13. The quantitative
upper and lower constants above are common to all layers. Without `hnd`, only
`factors_isBigO` is asserted. -/
theorem factors_isTheta
    (hext : Paper35.RankAsymptotics.GaussianExtremeMeanLaw) (u : f.UniformBounds)
    (c : ℝ) (hc : 0 < c)
    (hnd : ∀ᶠ R : ℝ in atTop, ∀ ℓ : Fin depth, ∃ r : Fin (f.width R ℓ),
      c ≤ covarianceMax ((f.layer R ℓ).unit r).covariance) :
    (∀ ℓ : Fin depth, Asymptotics.IsTheta atTop (fun R => f.switchFactor R ℓ) logScale) ∧
    (∀ ℓ : Fin depth, Asymptotics.IsTheta atTop (fun R => f.lengthFactor R ℓ) logScale) := by
  have hDpos : 0 < f.Dlower u c :=
    mul_pos (div_pos (by positivity : (0 : ℝ) < 1/(2*Real.sqrt Real.pi))
      (lt_of_lt_of_le u.σlo_pos u.σlo_le_σhi)) (Real.sqrt_pos.mpr hc)
  have hApos : 0 < Alower c := Real.sqrt_pos.mpr (mul_pos (by norm_num) hc)
  have hup := f.factors_isBigO hext u
  constructor
  · intro ℓ
    refine ⟨hup.1 ℓ, Asymptotics.isBigO_iff.mpr ⟨(f.Dlower u c)⁻¹, ?_⟩⟩
    filter_upwards [f.eventual_lower_bounds hext u c hc hnd, f.eventual_upper_bounds hext u] with R hlo hhi
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (show 0 ≤ logScale R from Real.sqrt_nonneg _), abs_of_nonneg (hhi ℓ).1]
    have H : logScale R ≤ f.switchFactor R ℓ / f.Dlower u c :=
      (le_div_iff₀ hDpos).mpr (by nlinarith [(hlo ℓ).1])
    simpa only [div_eq_mul_inv, mul_comm] using H
  · intro ℓ
    refine ⟨hup.2 ℓ, Asymptotics.isBigO_iff.mpr ⟨(Alower c)⁻¹, ?_⟩⟩
    filter_upwards [f.eventual_lower_bounds hext u c hc hnd, f.eventual_upper_bounds hext u] with R hlo hhi
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (show 0 ≤ logScale R from Real.sqrt_nonneg _), abs_of_nonneg (hhi ℓ).2.2.1]
    have H : logScale R ≤ f.lengthFactor R ℓ / Alower c :=
      (le_div_iff₀ hApos).mpr (by nlinarith [(hlo ℓ).2])
    simpa only [div_eq_mul_inv, mul_comm] using H

theorem uniform_factors_isBigO
    (hext : Paper35.RankAsymptotics.GaussianExtremeMeanLaw) (u : f.UniformBounds) :
    Asymptotics.IsBigO atTop (fun R => f.switchFactor R) logScale ∧
    Asymptotics.IsBigO atTop (fun R => f.lengthFactor R) logScale := by
  have H := f.factors_isBigO hext u
  exact ⟨Asymptotics.isBigO_pi.mpr H.1, Asymptotics.isBigO_pi.mpr H.2⟩

/-- Uniform finite-depth Theta statements in the Pi norm, in addition to
the quantitative simultaneous layerwise lower bounds. -/
theorem uniform_factors_isTheta
    (hext : Paper35.RankAsymptotics.GaussianExtremeMeanLaw) (u : f.UniformBounds)
    (hdepth : 0 < depth) (c : ℝ) (hc : 0 < c)
    (hnd : ∀ᶠ R : ℝ in atTop, ∀ ℓ : Fin depth, ∃ r : Fin (f.width R ℓ),
      c ≤ covarianceMax ((f.layer R ℓ).unit r).covariance) :
    Asymptotics.IsTheta atTop (fun R => f.switchFactor R) logScale ∧
    Asymptotics.IsTheta atTop (fun R => f.lengthFactor R) logScale := by
  have H := f.factors_isTheta hext u c hc hnd
  have hup := f.uniform_factors_isBigO hext u
  let ℓ : Fin depth := ⟨0,hdepth⟩
  constructor
  · refine ⟨hup.1, ?_⟩
    obtain ⟨M,hM⟩ := Asymptotics.isBigO_iff.mp (H.1 ℓ).2
    refine Asymptotics.isBigO_iff.mpr ⟨|M|, ?_⟩
    filter_upwards [hM] with R hR
    exact hR.trans ((mul_le_mul_of_nonneg_right (le_abs_self M) (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_left (norm_le_pi_norm (f.switchFactor R) ℓ) (abs_nonneg M)))
  · refine ⟨hup.2, ?_⟩
    obtain ⟨M,hM⟩ := Asymptotics.isBigO_iff.mp (H.2 ℓ).2
    refine Asymptotics.isBigO_iff.mpr ⟨|M|, ?_⟩
    filter_upwards [hM] with R hR
    exact hR.trans ((mul_le_mul_of_nonneg_right (le_abs_self M) (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_left (norm_le_pi_norm (f.lengthFactor R) ℓ) (abs_nonneg M)))

end Family
end Paper35.GaussianRankFamily
