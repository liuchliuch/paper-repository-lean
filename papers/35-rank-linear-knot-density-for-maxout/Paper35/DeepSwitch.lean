import Paper35.LayerMoment
import Paper35.ArclengthSwitch
import Paper35.RandomProbes
import Paper35.DistributionFree

/-! Actual source D factor and the one-layer switch estimate, using the proved
single-unit theorem as an internal dependency. Generic monotone arclength
factorization is the only curve input. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal NNReal
namespace Paper35.DeepModel.Network
open Paper35.Source Paper35.Source.WeightedModel Paper35.Deep
open Paper35.CurveCalculus Paper35.ClassicalInputs

/-- The source within-unit iid marginal and bounded conditional-density model.
Same-layer dependence between different units is arbitrary. No estimate is a
field of this structure. -/
structure LayerSource (m : DeepModel.Network) (n : ℕ) where
  unit : Fin (m.width (n+1)) → WeightedModel (m.width n)
  B : Fin (m.width (n+1)) → ℝ≥0
  envelope : ∀ r, ∀ᵐ w ∂(unit r).weights, (unit r).b₀ w = B r
  rank_two : ∀ r, 2 ≤ m.rank n r
  marginal : ∀ r, (m.layerLaw n).map (fun θ => θ r) = (unit r).iid (m.rank n r)

namespace LayerSource
variable {m : DeepModel.Network} {n : ℕ} (s : m.LayerSource n)

def directionalCost (u : Space (m.width n)) : ℝ≥0∞ :=
  ∑ r, ((m.rank n r : ℝ≥0∞)*s.B r/2) * (s.unit r).directionalGini u

/-- Exactly the source D supremum, with extended values allowed. -/
def sourceD : ℝ≥0∞ := sSup (s.directionalCost '' {u | ‖u‖=1})

lemma measurable_directionalGini {d : ℕ} (a : WeightedModel d) :
    Measurable a.directionalGini := by
  have H : Measurable (fun p : (Space d × Space d) × Space d =>
      ENNReal.ofReal |inner ℝ p.1.1 (p.1.2-p.2)|) := by fun_prop
  exact (H.lintegral_prod_right (ν := a.tilted)).lintegral_prod_right (ν := a.tilted)

lemma measurable_directionalCost : Measurable s.directionalCost := by
  apply Finset.measurable_sum
  intro r hr
  exact (measurable_directionalGini (s.unit r)).const_mul _

lemma directionalCost_unit_le (u : Space (m.width n)) (hu : ‖u‖=1) :
    s.directionalCost u ≤ s.sourceD := le_sSup ⟨u,hu,rfl⟩

/-- The actual one-layer union count is bounded by the sum of the original
single-unit visibility estimates, retaining the original within-unit iid law. -/
theorem probe_count_bound (hLN : LusinNovikovLaw) (hUP : BorelProjectionLaw)
    (p : Probe (m.width n)) :
    (∫⁻ θ, m.layerSwitchCount n θ p.curve p.length ∂m.layerLaw n) ≤
      ∫⁻ t in Icc 0 p.length, s.directionalCost (deriv p.curve t) := by
  have hc (r : Fin (m.width (n+1))) :
      Measurable (fun θ : m.Parameter n =>
        Paper35.switchCount (m.layerScores n θ p.curve r) p.length) := by
    exact (Paper35.RandomCount.measurable_affineSwitchCount p.curve p.length p.length_pos
      p.lipschitz.continuousOn (hLN _ _)).comp (measurable_pi_apply r)
  calc
    _ ≤ ∑ r, Paper35.expectedSwitchCount (m.layerLaw n)
        (fun θ => m.layerScores n θ p.curve r) p.length :=
      expected_jointSwitchCount_le (m.layerLaw n) (m.rank n)
        (fun θ r => m.layerScores n θ p.curve r) p.length hc
    _ = ∑ r, (s.unit r).expectedCount (m.rank n r) p := by
      apply Finset.sum_congr rfl
      intro r hr
      exact Paper35.RandomProbes.expectedCount_eq_of_marginal (m.layerLaw n) (s.unit r)
        (m.rank n r) p (fun θ => θ r) (measurable_pi_apply r) (s.marginal r) (hLN _ _)
    _ ≤ ∑ r, ((m.rank n r : ℝ≥0∞)*s.B r/2) *
        ∫⁻ t in Icc 0 p.length, (s.unit r).directionalGini (deriv p.curve t) := by
      apply Finset.sum_le_sum
      intro r hr
      have H := Paper35.DistributionFree.weighted_visibility hLN hUP (s.unit r)
        (m.rank n r) (s.rank_two r) p
      rwa [Paper35.Source.WeightedModel.average_eq_of_constant (s.unit r) (s.B r) (s.envelope r)] at H
    _ = _ := by
      rw [show (∫⁻ t in Icc 0 p.length, s.directionalCost (deriv p.curve t)) =
        ∑ r, ∫⁻ t in Icc 0 p.length,
          ((m.rank n r : ℝ≥0∞)*s.B r/2)*(s.unit r).directionalGini (deriv p.curve t) from
        lintegral_finset_sum _ (fun r _ =>
          ((measurable_directionalGini (s.unit r)).comp (measurable_deriv p.curve)).const_mul _)]
      apply Finset.sum_congr rfl
      intro r hr
      exact (lintegral_const_mul _
        ((measurable_directionalGini (s.unit r)).comp (measurable_deriv p.curve))).symm

/-- Actual switch sets depend only on the scores on the probe interval. -/
lemma switchSet_congrOn {K : ℕ} (f g : Fin K → ℝ → ℝ) (L : ℝ)
    (hfg : ∀ k, EqOn (f k) (g k) (Icc 0 L)) : Paper35.switchSet f L = Paper35.switchSet g L := by
  ext t
  constructor <;> rintro ⟨ht0,htL,i,j,hij,heq,hvis,hsgn⟩
  · have ht : t ∈ Icc 0 L := ⟨ht0.le,htL.le⟩
    refine ⟨ht0,htL,i,j,hij,?_,?_,?_⟩
    · simpa only [← hfg i ht,← hfg j ht] using heq
    · intro k hki hkj
      simpa only [← hfg k ht,← hfg i ht] using hvis k hki hkj
    · exact Paper35.RandomCount.signChanges_of_congrOn_interval ht0 htL
        (fun a ha => by rw [hfg i ha,hfg j ha]) hsgn
  · have ht : t ∈ Icc 0 L := ⟨ht0.le,htL.le⟩
    refine ⟨ht0,htL,i,j,hij,?_,?_,?_⟩
    · simpa only [hfg i ht,hfg j ht] using heq
    · intro k hki hkj
      simpa only [hfg k ht,hfg i ht] using hvis k hki hkj
    · exact Paper35.RandomCount.signChanges_of_congrOn_interval ht0 htL
        (fun a ha => by rw [hfg i ha,hfg j ha]) hsgn

set_option maxHeartbeats 600000 in
/-- The source one-layer D estimate for the actual input curve. The entire
arclength-collapse/count injection and the within-unit theorem assembly are
proved here, including constant curves. -/
theorem oneLayer_count_bound (hLN : LusinNovikovLaw) (hUP : BorelProjectionLaw)
    (harc : ArclengthFactorizationInput)
    (η : ℝ → Space (m.width n)) (L : ℝ) (hL : 0 ≤ L)
    (hcont : ContinuousOn η (Icc 0 L)) (hfinite : eVariationOn η (Icc 0 L) ≠ ∞) :
    (∫⁻ θ, m.layerSwitchCount n θ η L ∂m.layerLaw n) ≤
      s.sourceD * eVariationOn η (Icc 0 L) := by
  obtain ⟨x,u,σ,hx,hmu,hu,hderiv,hσcont,hσmono,himage,hfactor⟩ :=
    harc _ (m.width_pos n) η L hL hcont hfinite
  let T := (eVariationOn η (Icc 0 L)).toReal
  have hcollapse (θ : m.Parameter n) :
      m.layerSwitchCount n θ η L ≤ m.layerSwitchCount n θ x T := by
    have heq (r : Fin (m.width (n+1))) :
        Paper35.switchSet (m.layerScores n θ η r) L =
          Paper35.switchSet (fun j => m.layerScores n θ x r j ∘ σ) L := by
      apply switchSet_congrOn
      intro j t ht
      dsimp [layerScores,Function.comp_def]
      rw [hfactor ht]
      rfl
    change ((⋃ r, Paper35.switchSet (m.layerScores n θ η r) L).encard : ℝ≥0∞) ≤ _
    simp_rw [heq]
    exact Paper35.ArclengthSwitch.joint_count_comp_le (m.rank n)
      (m.layerScores n θ x) σ L T hσmono himage
  apply (lintegral_mono hcollapse).trans
  by_cases hT : 0 < T
  · have hvar : eVariationOn x (Icc 0 T) = ENNReal.ofReal T := by
      calc
        _ = eVariationOn (x ∘ σ) (Icc 0 L) := by
          rw [eVariationOn.comp_eq_of_monotoneOn _ _ hσmono,himage]
        _ = eVariationOn η (Icc 0 L) := (eVariationOn.eq_of_eqOn hfactor).symm
        _ = _ := (ENNReal.ofReal_toReal hfinite).symm
    let p : Probe (m.width n) := ⟨x,T,hT,hx.lipschitzOnWith,hvar⟩
    calc
      _ ≤ ∫⁻ t in Icc 0 T, s.directionalCost (deriv x t) := s.probe_count_bound hLN hUP p
      _ = ∫⁻ t in Icc 0 T, s.directionalCost (u t) := by
        apply lintegral_congr_ae
        filter_upwards [hderiv] with t ht
        rw [ht.deriv]
      _ ≤ ∫⁻ _t in Icc 0 T, s.sourceD := lintegral_mono (fun t => s.directionalCost_unit_le (u t) (hu t))
      _ = _ := by
        rw [lintegral_const]
        simp only [Measure.restrict_apply_univ,Real.volume_Icc,sub_zero,T,
          ENNReal.ofReal_toReal hfinite]
  · have hT0 : T=0 := le_antisymm (le_of_not_gt hT) ENNReal.toReal_nonneg
    have heq (θ : m.Parameter n) : m.layerSwitchCount n θ x T=0 := by
      have hset : m.layerSwitchTimes n θ x T=∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro t ht
        rcases mem_iUnion.mp ht with ⟨r,ht0,htT,hrest⟩
        exact (not_lt_of_ge ht0.le) (hT0 ▸ htT)
      simp [layerSwitchCount,hset]
    simp_rw [heq]
    simp

/-- Covariance aggregate in the source rough factor bound (8.8), computed
from each original weight law. -/
def covarianceSum (u : Space (m.width n)) : ℝ≥0∞ :=
  ∑ r, (m.rank n r : ℝ≥0∞)*s.B r * ENNReal.ofReal
    (Real.sqrt (Paper35.RandomProbes.originalProjectedVariance (s.unit r) u))

/-- The covariance rough bound (8.8), with the original source weight moments.
The sharp Gini constant and constant-envelope tilt identity are both proved
internal theorems, not additional inputs. -/
theorem sourceD_le_covariance_sup
    (hW : ∀ r, MemLp (fun w => w) 2 (s.unit r).weights) :
    s.sourceD ≤ (1/ENNReal.ofReal (Real.sqrt 3)) *
      sSup (s.covarianceSum '' {u | ‖u‖=1}) := by
  apply sSup_le
  rintro a ⟨u,hu,rfl⟩
  calc
    s.directionalCost u ≤ (1/ENNReal.ofReal (Real.sqrt 3))*s.covarianceSum u := by
      rw [covarianceSum,Finset.mul_sum]
      apply Finset.sum_le_sum
      intro r hr
      have ht : MemLp (fun w => w) 2 (s.unit r).tilted := by
        rw [tilted_eq_weights_of_constant (s.unit r) (s.B r) (s.envelope r)]
        exact hW r
      have H := (s.unit r).directionalGini_le_sqrt_projectedVariance ht u
      calc
        _ ≤ ((m.rank n r : ℝ≥0∞)*s.B r/2) * (ENNReal.ofReal (2/Real.sqrt 3) *
            ENNReal.ofReal (Real.sqrt ((s.unit r).projectedVariance u))) := mul_le_mul_left' H _
        _ = ((m.rank n r : ℝ≥0∞)*s.B r/ENNReal.ofReal (Real.sqrt 3)) *
            ENNReal.ofReal (Real.sqrt (Paper35.RandomProbes.originalProjectedVariance (s.unit r) u)) := by
          rw [← mul_assoc,covariance_coefficient_cancellation,
            Paper35.RandomProbes.projectedVariance_eq_original_of_constant (s.unit r) (s.B r) (s.envelope r)]
        _ = _ := by simp only [div_eq_mul_inv,one_mul]; ac_rfl
    _ ≤ _ := by
      have H : s.covarianceSum u ≤ sSup (s.covarianceSum '' {u | ‖u‖=1}) := le_sSup ⟨u,hu,rfl⟩
      exact mul_le_mul_left' H _

end LayerSource
variable (m : DeepModel.Network)

/-- Product-law count recursion with the actual (possibly extended) source D.
Length measurability, rather than count measurability, justifies the final
factor pullout. -/
theorem expectedCount_step_ennreal (D : ℕ → ℝ≥0∞) (n : ℕ)
    (γ : ℝ → Space (m.width 0)) (L : ℝ)
    (hstep : ∀ ω : m.Sample n,
      (∫⁻ θ, m.layerSwitchCount n θ (m.curve n ω γ) L ∂m.layerLaw n) ≤
        D n * m.curveLength n ω γ L) :
    m.expectedCount (n+1) γ L ≤ m.expectedCount n γ L + D n * m.expectedLength n γ L := by
  letI := m.layer_probability n
  calc
    _ ≤ ∫⁻ ω : m.Sample n, ∫⁻ θ, m.switchCount (n+1) (ω,θ) γ L ∂m.layerLaw n ∂m.law n :=
      lintegral_prod_le _
    _ ≤ ∫⁻ ω : m.Sample n, ∫⁻ θ,
        m.switchCount n ω γ L + m.layerSwitchCount n θ (m.curve n ω γ) L ∂m.layerLaw n ∂m.law n :=
      lintegral_mono (fun ω => lintegral_mono (fun θ => m.switchCount_step_le n (ω,θ) γ L))
    _ = ∫⁻ ω : m.Sample n, m.switchCount n ω γ L +
        (∫⁻ θ, m.layerSwitchCount n θ (m.curve n ω γ) L ∂m.layerLaw n) ∂m.law n := by
      apply lintegral_congr
      intro ω
      rw [lintegral_add_left measurable_const,lintegral_const]
      simp
    _ ≤ ∫⁻ ω : m.Sample n, m.switchCount n ω γ L +
        D n * m.curveLength n ω γ L ∂m.law n :=
      lintegral_mono (fun ω => add_le_add_left (hstep ω) _)
    _ = _ := by
      rw [lintegral_add_right _ (measurable_const.mul (m.measurable_curveLength n γ L)),
        lintegral_const_mul _ (m.measurable_curveLength n γ L)]
      rfl

/-- The source sum/product formula, with all one-layer source estimates proved
from actual parameters and the internal distribution-free theorem. This is the
switch-count conclusion (8.7) of Theorem 8.1. -/
theorem source_network_switch_bound
    (hLN : LusinNovikovLaw) (hUP : BorelProjectionLaw)
    (harc : ArclengthFactorizationInput) (hlinear : LinearACCalculusInput)
    (hmax : FiniteMaxACCalculusInput) (models : ∀ n, m.LayerSource n)
    (hW : ∀ n r j, MemLp (fun θ : m.Parameter n => (θ r j).1) 2 (m.layerLaw n))
    (γ : ℝ → Space (m.width 0)) (L : ℝ) (hL : 0 ≤ L)
    (hcont : ContinuousOn γ (Icc 0 L)) (hfinite : eVariationOn γ (Icc 0 L) ≠ ∞) :
    ∀ N, m.expectedCount N γ L ≤ eVariationOn γ (Icc 0 L) *
      ∑ n ∈ Finset.range N, (models n).sourceD *
        ∏ k ∈ Finset.range n, (m.sourceA k : ℝ≥0∞) := by
  have hcalculus := maxoutArclengthCalculus_of_classical
    (arclengthRepresentation_of_factorization harc) hlinear hmax
  have hlen := m.source_network_length_bound hcalculus hW γ L hcont hfinite
  have hstep (n : ℕ) (ω : m.Sample n) :
      (∫⁻ θ, m.layerSwitchCount n θ (m.curve n ω γ) L ∂m.layerLaw n) ≤
        (models n).sourceD * m.curveLength n ω γ L := by
    obtain ⟨C,hC⟩ := m.networkMap_lipschitz n ω
    exact (models n).oneLayer_count_bound hLN hUP harc _ L hL
      (hC.continuous.comp_continuousOn hcont) (hC.comp_boundedVariationOn hfinite)
  intro N
  induction N with
  | zero => simp [expectedCount,switchCount,switchTimes]
  | succ N ih =>
    calc
      _ ≤ m.expectedCount N γ L + (models N).sourceD * m.expectedLength N γ L :=
        m.expectedCount_step_ennreal (fun n => (models n).sourceD) N γ L (hstep N)
      _ ≤ eVariationOn γ (Icc 0 L) * (∑ n ∈ Finset.range N, (models n).sourceD *
            ∏ k ∈ Finset.range n, (m.sourceA k : ℝ≥0∞)) +
          (models N).sourceD * (eVariationOn γ (Icc 0 L) *
            ∏ k ∈ Finset.range N, (m.sourceA k : ℝ≥0∞)) :=
        add_le_add ih (mul_le_mul_left' (hlen N) _)
      _ = _ := by rw [Finset.sum_range_succ,mul_add]; ac_rfl

/-- Theorem 8.1 length conclusion (8.6), using only the generic original
classical statements; finite-max Lipschitz and all own layer/network bridges
are proved in Lean. -/
theorem source_network_length_bound_classical
    (harc : ArclengthFactorizationInput) (hlinear : LinearACCalculusInput)
    (hmax : FiniteMaxACCalculusInput)
    (hW : ∀ n r j, MemLp (fun θ : m.Parameter n => (θ r j).1) 2 (m.layerLaw n))
    (γ : ℝ → Space (m.width 0)) (L : ℝ)
    (hcont : ContinuousOn γ (Icc 0 L)) (hfinite : eVariationOn γ (Icc 0 L) ≠ ∞) :
    ∀ N, m.expectedLength N γ L ≤ eVariationOn γ (Icc 0 L) *
      ∏ n ∈ Finset.range N, (m.sourceA n : ℝ≥0∞) :=
  m.source_network_length_bound (maxoutArclengthCalculus_of_classical
    (arclengthRepresentation_of_factorization harc) hlinear hmax) hW γ L hcont hfinite

end Paper35.DeepModel.Network
