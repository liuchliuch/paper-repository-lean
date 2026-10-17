import Paper35.DeepModel
import Paper35.CurveCalculus
import Mathlib.MeasureTheory.SpecificCodomains.WithLp
import Mathlib.MeasureTheory.Function.L2Space

/-!
# The source one-layer length factor: actual projected-weight moments

All moment estimates in this file are proved in Lean. No independence between
units is used. Finite maximum chain rules, arclength change of parameter and
Tonelli for curve length are separate classical calculus dependencies.
-/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal NNReal
namespace Paper35.LayerMoment
open Paper35.Deep Paper35.DeepModel

/-- A measurable finite selection of L² real marks remains in L². -/
theorem memLp_finite_selection {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι] (μ : Measure Ω)
    (f : ι → Ω → ℝ) (hf : ∀ i, MemLp (f i) 2 μ)
    (J : Ω → ι) (hJ : Measurable J) : MemLp (fun ω => f (J ω) ω) 2 μ := by
  classical
  have H := memLp_finset_sum Finset.univ (fun i _ =>
    (hf i).indicator (hJ (measurableSet_singleton i)))
  convert H using 1
  ext ω
  simp only [Set.indicator_apply, Set.mem_preimage, Set.mem_singleton_iff]
  simp

/-- Integrability of a finite maximum, proved from the integrability of each mark. -/
theorem integrable_finset_max {Ω ι : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (s : Finset ι) (hs : s.Nonempty) (f : ι → Ω → ℝ)
    (hf : ∀ i ∈ s, Integrable (f i) μ) :
    Integrable (fun ω => s.sup' hs (fun i => f i ω)) μ := by
  have H : Integrable (s.sup' hs f) μ :=
    Finset.sup'_induction hs f (p := fun g : Ω → ℝ => Integrable g μ)
      (fun a ha b hb => ha.sup hb) hf
  convert H using 1
  funext ω
  exact (Finset.sup'_apply hs f ω).symm

end Paper35.LayerMoment
namespace Paper35.DeepModel.Network
open Paper35.LayerMoment
variable (m : Paper35.DeepModel.Network)

/-- The maximum squared candidate projection in a real unit, before selection. -/
def maxProjectedSquare (n : ℕ) (v : Space (m.width n))
    (θ : m.Parameter n) (r : Fin (m.width (n+1))) : ℝ :=
  Finset.univ.sup' ⟨⟨0, m.rank_pos n r⟩, Finset.mem_univ _⟩
    (fun j => |inner ℝ v (θ r j).1|^2)

/-- The actual directional second-moment aggregate in (8.4). -/
def directionalEnergy (n : ℕ) (v : Space (m.width n)) : ℝ :=
  ∑ r, ∫ θ, m.maxProjectedSquare n v θ r ∂m.layerLaw n

/-- Exactly the source length factor A_ell: supremum of sqrt of the aggregate
second moment over the Euclidean unit sphere. -/
def lengthFactor (n : ℕ) : ℝ :=
  sSup ((fun v : Space (m.width n) => Real.sqrt (m.directionalEnergy n v)) '' {v | ‖v‖=1})

/-- Actual projected active-weight vector for any measurable candidate selector.
The selector may depend on all candidates and need not be independent of weights. -/
def selectedProjection (n : ℕ) (v : Space (m.width n))
    (J : (θ : m.Parameter n) → (r : Fin (m.width (n+1))) → Fin (m.rank n r))
    (θ : m.Parameter n) : Space (m.width (n+1)) :=
  WithLp.toLp 2 (fun r => inner ℝ v (θ r (J θ r)).1)

lemma maxProjectedSquare_nonneg (n : ℕ) (v : Space (m.width n))
    (θ : m.Parameter n) (r : Fin (m.width (n+1))) : 0 ≤ m.maxProjectedSquare n v θ r := by
  exact (sq_nonneg |inner ℝ v (θ r ⟨0,m.rank_pos n r⟩).1|).trans
    (Finset.le_sup' (fun j => |inner ℝ v (θ r j).1|^2) (Finset.mem_univ _))

/-- The active derivative in a unit is one of the candidate projections, so its
square is bounded by the maximum. This estimate holds for arbitrary selectors. -/
lemma selectedProjection_sq_le (n : ℕ) (v : Space (m.width n))
    (J : (θ : m.Parameter n) → (r : Fin (m.width (n+1))) → Fin (m.rank n r))
    (θ : m.Parameter n) :
    ‖m.selectedProjection n v J θ‖^2 ≤ ∑ r, m.maxProjectedSquare n v θ r := by
  rw [EuclideanSpace.norm_sq_eq]
  apply Finset.sum_le_sum
  intro r hr
  change ‖inner ℝ v (θ r (J θ r)).1‖^2 ≤ _
  simpa only [Real.norm_eq_abs] using
    (Finset.le_sup' (fun j => |inner ℝ v (θ r j).1|^2) (Finset.mem_univ (J θ r)))

lemma maxProjectedSquare_integrable (n : ℕ) (v : Space (m.width n))
    (hW : ∀ r j, MemLp (fun θ : m.Parameter n => (θ r j).1) 2 (m.layerLaw n))
    (r : Fin (m.width (n+1))) : Integrable (fun θ => m.maxProjectedSquare n v θ r) (m.layerLaw n) := by
  apply integrable_finset_max
  intro j hj
  simpa only [sq_abs] using ((hW r j).const_inner v).integrable_sq

lemma selectedProjection_memLp (n : ℕ) (v : Space (m.width n))
    (hW : ∀ r j, MemLp (fun θ : m.Parameter n => (θ r j).1) 2 (m.layerLaw n))
    (J : (θ : m.Parameter n) → (r : Fin (m.width (n+1))) → Fin (m.rank n r))
    (hJ : ∀ r, Measurable (fun θ => J θ r)) :
    MemLp (m.selectedProjection n v J) 2 (m.layerLaw n) := by
  apply MemLp.of_eval_piLp
  intro r
  exact memLp_finite_selection (m.layerLaw n)
    (fun j θ => inner ℝ v (θ r j).1) (fun j => (hW r j).const_inner v)
    (fun θ => J θ r) (hJ r)

/-- Source moment estimate, including Jensen, the finite max bound and all
integrability justifications. It permits arbitrary same-layer dependence. -/
theorem expected_selectedProjection_norm_le (n : ℕ) (v : Space (m.width n))
    (hW : ∀ r j, MemLp (fun θ : m.Parameter n => (θ r j).1) 2 (m.layerLaw n))
    (J : (θ : m.Parameter n) → (r : Fin (m.width (n+1))) → Fin (m.rank n r))
    (hJ : ∀ r, Measurable (fun θ => J θ r)) :
    (∫ θ, ‖m.selectedProjection n v J θ‖ ∂m.layerLaw n) ≤
      Real.sqrt (m.directionalEnergy n v) := by
  letI := m.layer_probability n
  have hB := m.selectedProjection_memLp n v hW J hJ
  have hmean := Paper35.Deep.mean_square_le_second_moment (m.layerLaw n)
    (fun θ => ‖m.selectedProjection n v J θ‖) hB.norm
  apply Real.le_sqrt_of_sq_le
  apply hmean.trans
  calc
    _ ≤ ∫ θ, ∑ r, m.maxProjectedSquare n v θ r ∂m.layerLaw n :=
      integral_mono hB.norm.integrable_sq
        (integrable_finset_sum _ (fun r _ => m.maxProjectedSquare_integrable n v hW r))
        (m.selectedProjection_sq_le n v J)
    _ = _ := integral_finset_sum _ (fun r _ => m.maxProjectedSquare_integrable n v hW r)

/-- A uniform finite second-moment envelope on the unit sphere, obtained by
summing the actual candidate weight second moments. -/
lemma directionalEnergy_unit_bound (n : ℕ) (v : Space (m.width n)) (hv : ‖v‖=1)
    (hW : ∀ r j, MemLp (fun θ : m.Parameter n => (θ r j).1) 2 (m.layerLaw n)) :
    m.directionalEnergy n v ≤
      ∑ r, ∑ j, ∫ θ : m.Parameter n, ‖(θ r j).1‖^2 ∂m.layerLaw n := by
  apply Finset.sum_le_sum
  intro r hr
  calc
    (∫ θ, m.maxProjectedSquare n v θ r ∂m.layerLaw n) ≤
        ∫ θ : m.Parameter n, ∑ j, ‖(θ r j).1‖^2 ∂m.layerLaw n := by
      apply integral_mono (m.maxProjectedSquare_integrable n v hW r)
        (integrable_finset_sum _ (fun j _ => (hW r j).norm.integrable_sq))
      intro θ
      apply Finset.sup'_le
      intro j hj
      have hi : |inner ℝ v (θ r j).1| ≤ ‖(θ r j).1‖ := by
        simpa only [Real.norm_eq_abs, hv, one_mul] using abs_real_inner_le_norm v (θ r j).1
      exact ((sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).2 hi).trans
        (Finset.single_le_sum (fun k _ => sq_nonneg ‖(θ r k).1‖) hj)
    _ = _ := integral_finset_sum _ (fun j _ => (hW r j).norm.integrable_sq)

lemma lengthFactor_range_bddAbove (n : ℕ)
    (hW : ∀ r j, MemLp (fun θ : m.Parameter n => (θ r j).1) 2 (m.layerLaw n)) :
    BddAbove ((fun u : Space (m.width n) => Real.sqrt (m.directionalEnergy n u)) '' {u | ‖u‖=1}) := by
  refine ⟨Real.sqrt (∑ r, ∑ j, ∫ θ : m.Parameter n, ‖(θ r j).1‖^2 ∂m.layerLaw n), ?_⟩
  rintro a ⟨v,hv,rfl⟩
  exact Real.sqrt_le_sqrt (m.directionalEnergy_unit_bound n v hv hW)

lemma lengthFactor_nonneg (n : ℕ)
    (hW : ∀ r j, MemLp (fun θ : m.Parameter n => (θ r j).1) 2 (m.layerLaw n)) :
    0 ≤ m.lengthFactor n := by
  let v : Space (m.width n) := EuclideanSpace.single ⟨0,m.width_pos n⟩ 1
  have hv : ‖v‖=1 := by simp [v, EuclideanSpace.norm_single]
  exact (Real.sqrt_nonneg (m.directionalEnergy n v)).trans
    (le_csSup (m.lengthFactor_range_bddAbove n hW) ⟨v,hv,rfl⟩)

/-- The source length factor A controls every active directional mean, with
all boundedness and moment hypotheses discharged from candidate L² moments. -/
theorem expected_unit_selectedProjection_norm_le_factor (n : ℕ) (v : Space (m.width n))
    (hv : ‖v‖=1)
    (hW : ∀ r j, MemLp (fun θ : m.Parameter n => (θ r j).1) 2 (m.layerLaw n))
    (J : (θ : m.Parameter n) → (r : Fin (m.width (n+1))) → Fin (m.rank n r))
    (hJ : ∀ r, Measurable (fun θ => J θ r)) :
    (∫ θ, ‖m.selectedProjection n v J θ‖ ∂m.layerLaw n) ≤ m.lengthFactor n := by
  exact (m.expected_selectedProjection_norm_le n v hW J hJ).trans
    (le_csSup (m.lengthFactor_range_bddAbove n hW) ⟨v,hv,rfl⟩)

end Paper35.DeepModel.Network

namespace Paper35.LayerMoment
open Paper35.DeepModel

/-- Internal interface for the one-layer specialization. It is proved from
network-independent classical inputs below and is not an external theorem. -/
def MaxoutArclengthCalculusInput : Prop :=
  ∀ (m : DeepModel.Network) (n : ℕ) (η : ℝ → Space (m.width n)) (L : ℝ),
    (∀ r j, MemLp (fun θ : m.Parameter n => (θ r j).1) 2 (m.layerLaw n)) →
    ContinuousOn η (Icc 0 L) → eVariationOn η (Icc 0 L) ≠ ∞ →
    ∃ (x u : ℝ → Space (m.width n))
      (J : ℝ → (θ : m.Parameter n) → (r : Fin (m.width (n+1))) → Fin (m.rank n r)),
      (∀ s, ‖u s‖ = 1) ∧
      (∀ s r, Measurable (fun θ => J s θ r)) ∧
      (∀ s (θ : m.Parameter n) (r : Fin (m.width (n+1))) (j : Fin (m.rank n r)), inner ℝ (θ r j).1 (x s) + (θ r j).2 ≤
        inner ℝ (θ r (J s θ r)).1 (x s) + (θ r (J s θ r)).2) ∧
      (∫⁻ θ, eVariationOn (fun t => m.layerMap n θ (η t)) (Icc 0 L) ∂m.layerLaw n) ≤
        ∫⁻ s in Icc 0 (eVariationOn η (Icc 0 L)).toReal,
          ENNReal.ofReal (∫ θ, ‖m.selectedProjection n (u s) (J s) θ‖ ∂m.layerLaw n)

end Paper35.LayerMoment

namespace Paper35.DeepModel.Network
open Paper35.LayerMoment
variable (m : Paper35.DeepModel.Network)

/-- Actual global Lipschitz regularity is elementary and fully proved. -/
theorem layerMap_lipschitz (n : ℕ) (θ : m.Parameter n) :
    ∃ C : ℝ≥0, LipschitzWith C (m.layerMap n θ) :=
  Paper35.CurveCalculus.affineMax_lipschitz _ _ (m.rank n) (m.rank_pos n)
    (fun r j => (θ r j).1) (fun r j => (θ r j).2)

/-- The source nonnegative length factor, with its value justified above. -/
def sourceA (n : ℕ) : ℝ≥0 := (m.lengthFactor n).toNNReal

/-- The full actual one-layer source-A estimate. The max/selection moment
inequality, Jensen and the supremum estimate are the proved steps above. -/
theorem oneLayer_length_bound (hcalculus : MaxoutArclengthCalculusInput)
    (n : ℕ) (η : ℝ → Space (m.width n)) (L : ℝ)
    (hcont : ContinuousOn η (Icc 0 L)) (hfinite : eVariationOn η (Icc 0 L) ≠ ∞)
    (hW : ∀ r j, MemLp (fun θ : m.Parameter n => (θ r j).1) 2 (m.layerLaw n)) :
    (∫⁻ θ, eVariationOn (fun t => m.layerMap n θ (η t)) (Icc 0 L) ∂m.layerLaw n) ≤
      m.sourceA n * eVariationOn η (Icc 0 L) := by
  obtain ⟨x,u,J,hu,hJ,hactive,hbound⟩ := hcalculus m n η L hW hcont hfinite
  calc
    _ ≤ ∫⁻ s in Icc 0 (eVariationOn η (Icc 0 L)).toReal,
        ENNReal.ofReal (∫ θ, ‖m.selectedProjection n (u s) (J s) θ‖ ∂m.layerLaw n) := hbound
    _ ≤ ∫⁻ s in Icc 0 (eVariationOn η (Icc 0 L)).toReal,
        ENNReal.ofReal (m.lengthFactor n) := by
      apply lintegral_mono
      intro s
      exact ENNReal.ofReal_le_ofReal
        (m.expected_unit_selectedProjection_norm_le_factor n (u s) (hu s) hW (J s) (hJ s))
    _ = _ := by
      rw [lintegral_const]
      simp only [Measure.restrict_apply_univ, Real.volume_Icc, sub_zero,
        ENNReal.ofReal_toReal hfinite]
      have he : ENNReal.ofReal (m.lengthFactor n) = (m.sourceA n : ℝ≥0∞) := rfl
      rw [he]

lemma networkMap_lipschitz (n : ℕ) (ω : m.Sample n) :
    ∃ C : ℝ≥0, LipschitzWith C (m.networkMap n ω) := by
  induction n with
  | zero => exact ⟨1, LipschitzWith.id⟩
  | succ n ih =>
    obtain ⟨C,hC⟩ := ih ω.1
    obtain ⟨B,hB⟩ := m.layerMap_lipschitz n ω.2
    exact ⟨B*C,hB.comp hC⟩

/-- Equation (8.6), with the actual network law, actual source-A factor and
actual rectifiable input curve. Only classical curve calculus is external. -/
theorem source_network_length_bound (hcalculus : MaxoutArclengthCalculusInput)
    (hW : ∀ n r j, MemLp (fun θ : m.Parameter n => (θ r j).1) 2 (m.layerLaw n))
    (γ : ℝ → Space (m.width 0)) (L : ℝ)
    (hcont : ContinuousOn γ (Icc 0 L)) (hfinite : eVariationOn γ (Icc 0 L) ≠ ∞) :
    ∀ n, m.expectedLength n γ L ≤ eVariationOn γ (Icc 0 L) *
      ∏ h ∈ Finset.range n, (m.sourceA h : ℝ≥0∞) := by
  apply m.network_length_propagation
  intro n ω
  obtain ⟨C,hC⟩ := m.networkMap_lipschitz n ω
  exact m.oneLayer_length_bound hcalculus n (m.curve n ω γ) L
    (hC.continuous.comp_continuousOn hcont)
    (hC.comp_boundedVariationOn hfinite) (hW n)

set_option maxHeartbeats 800000 in
/-- The original Maxout-specific first-moment/arclength interface follows
from arbitrary-curve classical statements. The actual affine derivatives,
active selectors, layer maps and the probability integrals are assembled here. -/
theorem maxoutArclengthCalculus_of_classical
    (harc : Paper35.CurveCalculus.ArclengthRepresentationInput)
    (hlinear : Paper35.CurveCalculus.LinearACCalculusInput)
    (hmax : Paper35.CurveCalculus.FiniteMaxACCalculusInput) :
    MaxoutArclengthCalculusInput := by
  intro m n η L hW hcont hfinite
  letI := m.layer_probability n
  obtain ⟨x,u,hx,hmu,hu,hderiv,hrep⟩ := harc _ (m.width_pos n) η L hcont hfinite
  let T := (eVariationOn η (Icc 0 L)).toReal
  let J : ℝ → (θ : m.Parameter n) → (r : Fin (m.width (n+1))) → Fin (m.rank n r) :=
    fun s θ r => Paper35.CurveCalculus.winner (m.rank_pos n r)
      (fun j => inner ℝ (θ r j).1 (x s)+(θ r j).2)
  have hJ (r : Fin (m.width (n+1))) :
      Measurable (fun p : ℝ × m.Parameter n => J p.1 p.2 r) := by
    apply (Paper35.CurveCalculus.measurable_winner (m.rank_pos n r)).comp
    apply measurable_pi_lambda
    intro j
    have hw : Measurable (fun p : ℝ × m.Parameter n => (p.2 r j).1) := by fun_prop
    have hb : Measurable (fun p : ℝ × m.Parameter n => (p.2 r j).2) := by fun_prop
    exact (hw.inner (hx.continuous.measurable.comp measurable_fst)).add hb
  have hactive (s) (θ : m.Parameter n) (r) (j) :
      inner ℝ (θ r j).1 (x s)+(θ r j).2 ≤
        inner ℝ (θ r (J s θ r)).1 (x s)+(θ r (J s θ r)).2 :=
    Paper35.CurveCalculus.winner_is_max (m.rank_pos n r)
      (fun j => inner ℝ (θ r j).1 (x s)+(θ r j).2) j
  have hxAC : AbsolutelyContinuousOnInterval x 0 T :=
    hx.lipschitzOnWith.absolutelyContinuousOnInterval
  have hscalar := (hlinear _ T x hxAC).2
  have hvar (θ : m.Parameter n) :
      eVariationOn (fun t => m.layerMap n θ (x t)) (Icc 0 T) =
        ∫⁻ s in Icc 0 T, ENNReal.ofReal ‖m.selectedProjection n (u s) (J s) θ‖ := by
    apply hmax _ (m.rank n) (m.rank_pos n) T
      (fun r j s => inner ℝ (θ r j).1 (x s)+(θ r j).2)
      (fun r j s => inner ℝ (u s) (θ r j).1) (fun s r => J s θ r)
    · intro r j
      exact hscalar (innerSL ℝ (θ r j).1) (θ r j).2
    · intro r j
      filter_upwards [hderiv] with s hs
      have H := ((hasDerivAt_const s (θ r j).1).inner ℝ hs).add_const (θ r j).2
      simpa only [inner_zero_left, add_zero, real_inner_comm] using H
    · exact fun s r j => hactive s θ r j
  have hB : Measurable (fun p : ℝ × m.Parameter n =>
      m.selectedProjection n (u p.1) (J p.1) p.2) := by
    apply (PiLp.continuous_toLp 2 _).measurable.comp
    apply measurable_pi_lambda
    intro r
    have hweight : Measurable (fun p : ℝ × m.Parameter n =>
        (p.2 r (J p.1 p.2 r)).1) :=
      Paper35.CurveCalculus.measurable_finite_selection _
        (fun j (p : ℝ × m.Parameter n) => (p.2 r j).1)
        (fun j => by fun_prop) _ (hJ r)
    exact (hmu.comp measurable_fst).inner hweight
  have ht := Paper35.CurveCalculus.expected_variation_from_derivative (m.layerLaw n) _ T
    (fun θ t => m.layerMap n θ (x t)) (fun s θ => m.selectedProjection n (u s) (J s) θ)
    hB.aemeasurable (fun s => (m.selectedProjection_memLp n (u s) hW (J s)
      (fun r => (hJ r).comp (measurable_const.prodMk measurable_id))).norm.integrable (by norm_num)) hvar
  refine ⟨x,u,J,hu,?_,hactive,?_⟩
  · exact fun s r => (hJ r).comp (measurable_const.prodMk measurable_id)
  · have heq (θ : m.Parameter n) :
        eVariationOn (fun t => m.layerMap n θ (η t)) (Icc 0 L) =
          eVariationOn (fun t => m.layerMap n θ (x t)) (Icc 0 T) := by
        obtain ⟨C,hC⟩ := m.layerMap_lipschitz n θ
        exact hrep _ (m.layerMap n θ) C hC
    simp_rw [heq]
    exact ht.le

end Paper35.DeepModel.Network
