import Paper35.Deep
import Paper35.SourceModel
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.FunProp

/-!
# Actual independent-layer Maxout network: probability/curve recursion

The parameters below are the weights and biases of actual Maxout maps. The
sample law is the iterated product of the layer laws, so independence of layers
is represented in the probability space itself. The propagation theorems prove
the passage from deterministic incoming-curve one-layer estimates to the actual
network's expectations. The deterministic one-layer estimates remain explicitly
named internal dependencies, rather than fields of the random-network model.
-/

noncomputable section
open MeasureTheory Set Matrix
open scoped ENNReal NNReal BigOperators
namespace Paper35.DeepModel
open Paper35.Deep

abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin d)
abbrev LayerParameter (d q : ℕ) (K : Fin q → ℕ) := (r : Fin q) → Fin (K r) → Space d × ℝ

structure Network where
  width : ℕ → ℕ
  width_pos : ∀ n, 0 < width n
  rank : (n : ℕ) → Fin (width (n+1)) → ℕ
  rank_pos : ∀ n r, 0 < rank n r
  layerLaw : (n : ℕ) → Measure (LayerParameter (width n) (width (n+1)) (rank n))
  layer_probability : ∀ n, IsProbabilityMeasure (layerLaw n)

namespace Network
variable (m : Network)

abbrev Parameter (n : ℕ) := LayerParameter (m.width n) (m.width (n+1)) (m.rank n)

def Sample (m : Network) : ℕ → Type
  | 0 => PUnit
  | n+1 => Sample m n × m.Parameter n

instance sampleMeasurable (m : Network) : (n : ℕ) → MeasurableSpace (m.Sample n)
  | 0 => inferInstanceAs (MeasurableSpace PUnit)
  | n+1 => MeasurableSpace.prod (sampleMeasurable m n) inferInstance

instance sampleTopology (m : Network) : (n : ℕ) → TopologicalSpace (m.Sample n)
  | 0 => inferInstanceAs (TopologicalSpace PUnit)
  | n+1 => @instTopologicalSpaceProd _ _ (sampleTopology m n) inferInstance

instance sampleBorel (n : ℕ) : BorelSpace (m.Sample n) := by
  induction n with
  | zero => exact inferInstanceAs (BorelSpace PUnit)
  | succ n ih => exact inferInstanceAs (BorelSpace (m.Sample n × m.Parameter n))

def law (m : Network) : (n : ℕ) → Measure (m.Sample n)
  | 0 => Measure.dirac PUnit.unit
  | n+1 => (law m n).prod (m.layerLaw n)

instance law_probability (n : ℕ) : IsProbabilityMeasure (m.law n) := by
  induction n with
  | zero => exact inferInstanceAs (IsProbabilityMeasure (Measure.dirac PUnit.unit))
  | succ n ih =>
    letI := m.layer_probability n
    exact inferInstanceAs (IsProbabilityMeasure ((m.law n).prod (m.layerLaw n)))

/-- The actual vector Maxout layer. -/
def layerMap (n : ℕ) (θ : m.Parameter n) (x : Space (m.width n)) : Space (m.width (n+1)) :=
  WithLp.toLp 2 (fun r => Finset.univ.sup'
    ⟨⟨0, m.rank_pos n r⟩, Finset.mem_univ _⟩
      (fun j => inner ℝ (θ r j).1 x + (θ r j).2))

/-- Actual feedforward composition z_n, with the first n independently sampled layers. -/
def networkMap (m : Network) : (n : ℕ) → m.Sample n → Space (m.width 0) → Space (m.width n)
  | 0, _, x => x
  | n+1, ω, x => m.layerMap n ω.2 (networkMap m n ω.1 x)

def curve (n : ℕ) (ω : m.Sample n) (γ : ℝ → Space (m.width 0)) : ℝ → Space (m.width n) :=
  fun t => m.networkMap n ω (γ t)

/-- Parameterized length, including all retracing, as in the source paper. -/
def curveLength (n : ℕ) (ω : m.Sample n) (γ : ℝ → Space (m.width 0)) (L : ℝ) : ℝ≥0∞ :=
  eVariationOn (m.curve n ω γ) (Icc 0 L)

/-- Actual unit scores along the incoming curve, measured in the original time. -/
def layerScores (n : ℕ) (θ : m.Parameter n) (η : ℝ → Space (m.width n))
    (r : Fin (m.width (n+1))) : Fin (m.rank n r) → ℝ → ℝ :=
  fun j t => inner ℝ (θ r j).1 (η t) + (θ r j).2

/-- All switch times created by one actual layer, with simultaneous unit switches identified. -/
def layerSwitchTimes (n : ℕ) (θ : m.Parameter n) (η : ℝ → Space (m.width n)) (L : ℝ) : Set ℝ :=
  ⋃ r, Paper35.switchSet (m.layerScores n θ η r) L

def layerSwitchCount (n : ℕ) (θ : m.Parameter n) (η : ℝ → Space (m.width n)) (L : ℝ) : ℝ≥0∞ :=
  (m.layerSwitchTimes n θ η L).encard

/-- The original source count S_D: the union across all actual layers, rather
than a sum of counts or a count of final-output breakpoints. -/
def switchTimes (m : Network) : (n : ℕ) → m.Sample n → (ℝ → Space (m.width 0)) → ℝ → Set ℝ
  | 0, _, _, _ => ∅
  | n+1, ω, γ, L => switchTimes m n ω.1 γ L ∪
      m.layerSwitchTimes n ω.2 (m.curve n ω.1 γ) L

def switchCount (n : ℕ) (ω : m.Sample n) (γ : ℝ → Space (m.width 0)) (L : ℝ) : ℝ≥0∞ :=
  (m.switchTimes n ω γ L).encard

def expectedLength (n : ℕ) (γ : ℝ → Space (m.width 0)) (L : ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, m.curveLength n ω γ L ∂m.law n

def expectedCount (n : ℕ) (γ : ℝ → Space (m.width 0)) (L : ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, m.switchCount n ω γ L ∂m.law n

lemma continuous_layerEval (n : ℕ) :
    Continuous (fun p : m.Parameter n × Space (m.width n) => m.layerMap n p.1 p.2) := by
  unfold layerMap
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro r
  apply Continuous.finset_sup'_apply
  intro j hj
  fun_prop

lemma continuous_network_parameter (n : ℕ) (x : Space (m.width 0)) :
    Continuous (fun ω : m.Sample n => m.networkMap n ω x) := by
  induction n with
  | zero => exact continuous_const
  | succ n ih =>
    change Continuous (fun ω : m.Sample n × m.Parameter n =>
      m.layerMap n ω.2 (m.networkMap n ω.1 x))
    have hp : Continuous (fun ω : m.Sample n × m.Parameter n =>
        (ω.2, m.networkMap n ω.1 x)) :=
      continuous_snd.prodMk (ih.comp continuous_fst)
    have H := (m.continuous_layerEval n).comp hp
    dsimp only [Function.comp_def] at H
    exact H

/-- Length measurability is proved from its supremum over finite partitions;
no measurability of random zero-set counts is silently assumed. -/
lemma measurable_curveLength (n : ℕ) (γ : ℝ → Space (m.width 0)) (L : ℝ) :
    Measurable (fun ω : m.Sample n => m.curveLength n ω γ L) := by
  apply LowerSemicontinuous.measurable
  unfold curveLength eVariationOn
  apply lowerSemicontinuous_iSup
  intro p
  apply Continuous.lowerSemicontinuous
  apply continuous_finset_sum
  intro i hi
  exact (m.continuous_network_parameter n (γ (p.2.1 (i+1)))).edist
    (m.continuous_network_parameter n (γ (p.2.1 i)))

lemma switchCount_step_le (n : ℕ) (ω : m.Sample (n+1)) (γ : ℝ → Space (m.width 0)) (L : ℝ) :
    m.switchCount (n+1) ω γ L ≤ m.switchCount n ω.1 γ L +
      m.layerSwitchCount n ω.2 (m.curve n ω.1 γ) L := by
  simpa only [ENat.toENNReal_add] using ENat.toENNReal_mono
    (Set.encard_union_le (m.switchTimes n ω.1 γ L) (m.layerSwitchTimes n ω.2 (m.curve n ω.1 γ) L))

/-- Integrating a deterministic incoming-curve length estimate against the
past-layer law gives the actual unconditional one-step length bound. -/
theorem expectedLength_step (A : ℕ → ℝ≥0) (n : ℕ)
    (γ : ℝ → Space (m.width 0)) (L : ℝ)
    (hstep : ∀ ω : m.Sample n,
      (∫⁻ θ, eVariationOn (fun t => m.layerMap n θ (m.curve n ω γ t)) (Icc 0 L) ∂m.layerLaw n) ≤
        A n * m.curveLength n ω γ L) :
    m.expectedLength (n+1) γ L ≤ A n * m.expectedLength n γ L := by
  letI := m.layer_probability n
  calc
    _ ≤ ∫⁻ ω : m.Sample n, ∫⁻ θ, m.curveLength (n+1) (ω, θ) γ L ∂m.layerLaw n ∂m.law n :=
      lintegral_prod_le _
    _ ≤ ∫⁻ ω : m.Sample n, (A n : ℝ≥0∞) * m.curveLength n ω γ L ∂m.law n :=
      lintegral_mono hstep
    _ = _ := lintegral_const_mul' _ _ ENNReal.coe_ne_top

/-- The actual distinct-time count recursion. The proof uses the product law
and the exact union of switch times; no independence between same-layer units
is introduced, and no count-measurability assumption is needed. -/
theorem expectedCount_step (D : ℕ → ℝ≥0) (n : ℕ)
    (γ : ℝ → Space (m.width 0)) (L : ℝ)
    (hstep : ∀ ω : m.Sample n,
      (∫⁻ θ, m.layerSwitchCount n θ (m.curve n ω γ) L ∂m.layerLaw n) ≤
        D n * m.curveLength n ω γ L) :
    m.expectedCount (n+1) γ L ≤ m.expectedCount n γ L + D n * m.expectedLength n γ L := by
  letI := m.layer_probability n
  calc
    _ ≤ ∫⁻ ω : m.Sample n, ∫⁻ θ, m.switchCount (n+1) (ω, θ) γ L ∂m.layerLaw n ∂m.law n :=
      lintegral_prod_le _
    _ ≤ ∫⁻ ω : m.Sample n, ∫⁻ θ,
        m.switchCount n ω γ L + m.layerSwitchCount n θ (m.curve n ω γ) L ∂m.layerLaw n ∂m.law n :=
      lintegral_mono (fun ω => lintegral_mono (fun θ => m.switchCount_step_le n (ω, θ) γ L))
    _ = ∫⁻ ω : m.Sample n, m.switchCount n ω γ L +
        (∫⁻ θ, m.layerSwitchCount n θ (m.curve n ω γ) L ∂m.layerLaw n) ∂m.law n := by
      apply lintegral_congr
      intro ω
      rw [lintegral_add_left measurable_const, lintegral_const]
      simp
    _ ≤ ∫⁻ ω : m.Sample n, m.switchCount n ω γ L +
        (D n : ℝ≥0∞) * m.curveLength n ω γ L ∂m.law n := by
      exact lintegral_mono (fun ω => add_le_add_left (hstep ω) _)
    _ = _ := by
      rw [lintegral_add_right _ (measurable_const.mul (m.measurable_curveLength n γ L)),
        lintegral_const_mul' _ _ ENNReal.coe_ne_top]
      rfl

lemma expectedLength_zero (γ : ℝ → Space (m.width 0)) (L : ℝ) :
    m.expectedLength 0 γ L = eVariationOn γ (Icc 0 L) := by
  change (∫⁻ _ : PUnit, eVariationOn γ (Icc 0 L) ∂Measure.dirac PUnit.unit) = _
  simp

/-- The original source product bound, now for the expectation of the actual
composed Maxout curve. Only the deterministic one-layer estimate is an internal
dependency; the independent-layer passage and iteration are proved here. -/
theorem network_length_propagation (A : ℕ → ℝ≥0)
    (γ : ℝ → Space (m.width 0)) (L : ℝ)
    (hstep : ∀ n (ω : m.Sample n),
      (∫⁻ θ, eVariationOn (fun t => m.layerMap n θ (m.curve n ω γ t)) (Icc 0 L) ∂m.layerLaw n) ≤
        A n * m.curveLength n ω γ L) :
    ∀ n, m.expectedLength n γ L ≤ eVariationOn γ (Icc 0 L) * ∏ h ∈ Finset.range n, (A h : ℝ≥0∞) := by
  intro n
  induction n with
  | zero => simpa using (le_of_eq (m.expectedLength_zero γ L))
  | succ n ih =>
    calc
      _ ≤ (A n : ℝ≥0∞) * m.expectedLength n γ L := m.expectedLength_step A n γ L (hstep n)
      _ ≤ (A n : ℝ≥0∞) * (eVariationOn γ (Icc 0 L) * ∏ h ∈ Finset.range n, (A h : ℝ≥0∞)) :=
        mul_le_mul_left' ih _
      _ = _ := by rw [Finset.prod_range_succ]; ac_rfl

/-- The original source sum/product bound for the union of actual switches.
This is the genuine one-layer-to-independent-network theorem, not a recurrence
on unrelated numerical sequences. -/
theorem network_switch_propagation (A D : ℕ → ℝ≥0)
    (γ : ℝ → Space (m.width 0)) (L : ℝ)
    (hA : ∀ n (ω : m.Sample n),
      (∫⁻ θ, eVariationOn (fun t => m.layerMap n θ (m.curve n ω γ t)) (Icc 0 L) ∂m.layerLaw n) ≤
        A n * m.curveLength n ω γ L)
    (hD : ∀ n (ω : m.Sample n),
      (∫⁻ θ, m.layerSwitchCount n θ (m.curve n ω γ) L ∂m.layerLaw n) ≤
        D n * m.curveLength n ω γ L) :
    ∀ n, m.expectedCount n γ L ≤ eVariationOn γ (Icc 0 L) *
      ∑ h ∈ Finset.range n, (D h : ℝ≥0∞) * ∏ k ∈ Finset.range h, (A k : ℝ≥0∞) := by
  intro n
  induction n with
  | zero => simp [expectedCount, switchCount, switchTimes]
  | succ n ih =>
    have hlen := m.network_length_propagation A γ L hA n
    calc
      _ ≤ m.expectedCount n γ L + (D n : ℝ≥0∞) * m.expectedLength n γ L :=
        m.expectedCount_step D n γ L (hD n)
      _ ≤ eVariationOn γ (Icc 0 L) * (∑ h ∈ Finset.range n, (D h : ℝ≥0∞) *
          ∏ k ∈ Finset.range h, (A k : ℝ≥0∞)) +
          (D n : ℝ≥0∞) * (eVariationOn γ (Icc 0 L) * ∏ k ∈ Finset.range n, (A k : ℝ≥0∞)) :=
        add_le_add ih (mul_le_mul_left' hlen _)
      _ = _ := by rw [Finset.sum_range_succ, mul_add]; ac_rfl

end Network
end Paper35.DeepModel
