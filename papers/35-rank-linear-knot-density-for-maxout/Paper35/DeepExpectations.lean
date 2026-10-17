import Paper35.DeepSpectral
import Paper35.RandomCount

/-! Actual network union-count measurability and ordinary real expectations.
The same source Lusin–Novikov theorem is used only on a Borel graph with
countable sections. No network count or moment conclusion is an input. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal
namespace Paper35.DeepModel.Network
open Paper35.Source Paper35.VisibleCrossing Paper35.RandomCount Paper35.ClassicalInputs

lemma activeSwitch_congrOn {K : ℕ} {f g : Fin K → ℝ → ℝ} {L s : ℝ}
    (hfg : ∀ k, EqOn (f k) (g k) (Icc 0 L)) :
    ActiveSwitch f L s ↔ ActiveSwitch g L s := by
  constructor <;> rintro ⟨hs0,hsL,i,j,hij,heq,hvis,hsgn⟩
  · have hs : s ∈ Icc 0 L := ⟨hs0.le,hsL.le⟩
    refine ⟨hs0,hsL,i,j,hij,?_,?_,?_⟩
    · simpa only [← hfg i hs, ← hfg j hs] using heq
    · intro k hki hkj
      simpa only [← hfg k hs, ← hfg i hs] using hvis k hki hkj
    · exact signChanges_of_congrOn_interval hs0 hsL
        (fun t ht => by rw [hfg i ht,hfg j ht]) hsgn
  · have hs : s ∈ Icc 0 L := ⟨hs0.le,hsL.le⟩
    refine ⟨hs0,hsL,i,j,hij,?_,?_,?_⟩
    · simpa only [hfg i hs,hfg j hs] using heq
    · intro k hki hkj
      simpa only [hfg k hs,hfg i hs] using hvis k hki hkj
    · exact signChanges_of_congrOn_interval hs0 hsL
        (fun t ht => by rw [hfg i ht,hfg j ht]) hsgn

lemma activeSwitch_normalized {d K : ℕ} (γ : ℝ → Space d) (L : ℝ) (hL : 0 < L)
    (hγ : ContinuousOn γ (Icc 0 L)) (θ : Fin K → Candidate d) (s : ℝ) :
    ActiveSwitch (codeScores (normalizedCurve γ L hL.le hγ,θ)) 1 (s/L) ↔
      ActiveSwitch (fun k t => inner ℝ (θ k).1 (γ t)+(θ k).2) L s := by
  have hc : ∀ k, EqOn (codeScores (normalizedCurve γ L hL.le hγ,θ) k)
      (fun t => inner ℝ (θ k).1 (γ (L*t))+(θ k).2) (Icc 0 1) := by
    intro k t ht
    simp only [codeScores,projIcc_of_mem zero_le_one ht,normalizedCurve,ContinuousMap.coe_mk]
  rw [activeSwitch_congrOn hc,
    activeSwitch_comp_pos_mul (fun k t => inner ℝ (θ k).1 (γ t)+(θ k).2) hL]
  rw [mul_div_cancel₀ s hL.ne']

lemma measurableSet_affineSwitchGraph {Ω : Type*} [MeasurableSpace Ω] {d K : ℕ}
    (γ : Ω → ℝ → Space d) (L : ℝ) (hL : 0 < L)
    (hc : ∀ ω, ContinuousOn (γ ω) (Icc 0 L))
    (hm : ∀ t, Measurable (fun ω => γ ω t))
    (θ : Ω → Fin K → Candidate d) (hθ : Measurable θ) :
    MeasurableSet {z : Ω × ℝ | z.2 ∈
      switchSet (fun k t => inner ℝ (θ z.1 k).1 (γ z.1 t)+(θ z.1 k).2) L} := by
  have hcode : Measurable (fun ω => normalizedCurve (γ ω) L hL.le (hc ω)) := by
    apply measurable_pathCode_of_eval
    intro t
    exact hm (L*t)
  have hgraph : MeasurableSet {z : CodeParameter d K × ℝ |
      z.2 ∈ switchSet (codeScores z.1) 1} := by
    have heq : {z : CodeParameter d K × ℝ | z.2 ∈ switchSet (codeScores z.1) 1} =
        ⋃ q : OrderedCandidatePair K, {z | z.2 ∈ pairSwitchSet (codeScores z.1) 1 q} := by
      ext z
      simp only [mem_setOf_eq,mem_iUnion,switchSet_eq_iUnion_pairSwitchSet]
    rw [heq]
    exact MeasurableSet.iUnion measurableSet_codePairGraph
  have hmap : Measurable (fun z : Ω × ℝ =>
      ((normalizedCurve (γ z.1) L hL.le (hc z.1),θ z.1),z.2/L)) :=
    ((hcode.comp measurable_fst).prodMk (hθ.comp measurable_fst)).prodMk
      (measurable_snd.div_const L)
  convert hgraph.preimage hmap using 1
  ext z
  exact (activeSwitch_normalized (γ z.1) L hL (hc z.1) (θ z.1) z.2).symm

instance sampleStandardBorel (m : DeepModel.Network) (n : ℕ) :
    StandardBorelSpace (m.Sample n) := by
  induction n with
  | zero => exact inferInstanceAs (StandardBorelSpace PUnit)
  | succ n ih => exact inferInstanceAs (StandardBorelSpace (m.Sample n × m.Parameter n))

variable (m : DeepModel.Network)

lemma continuousOn_curve (n : ℕ) (ω : m.Sample n)
    (γ : ℝ → Space (m.width 0)) (L : ℝ) (hc : ContinuousOn γ (Icc 0 L)) :
    ContinuousOn (m.curve n ω γ) (Icc 0 L) := by
  obtain ⟨C,hC⟩ := m.networkMap_lipschitz n ω
  exact hC.continuous.comp_continuousOn hc

lemma layerSwitchTimes_countable (n : ℕ) (θ : m.Parameter n)
    (η : ℝ → Space (m.width n)) (L : ℝ) :
    (m.layerSwitchTimes n θ η L).Countable :=
  countable_iUnion fun r => Paper35.switchSet_countable (m.layerScores n θ η r) L

lemma switchTimes_countable (n : ℕ) (ω : m.Sample n)
    (γ : ℝ → Space (m.width 0)) (L : ℝ) : (m.switchTimes n ω γ L).Countable := by
  induction n with
  | zero => exact countable_empty
  | succ n ih => exact (ih ω.1).union (m.layerSwitchTimes_countable n ω.2 _ L)

lemma measurableSet_switchTimesGraph (n : ℕ) (γ : ℝ → Space (m.width 0))
    (L : ℝ) (hL : 0 < L) (hc : ContinuousOn γ (Icc 0 L)) :
    MeasurableSet {z : m.Sample n × ℝ | z.2 ∈ m.switchTimes n z.1 γ L} := by
  induction n with
  | zero => simpa only [switchTimes,mem_empty_iff_false,setOf_false] using MeasurableSet.empty
  | succ n ih =>
    have hpast : MeasurableSet {z : m.Sample (n+1) × ℝ |
        z.2 ∈ m.switchTimes n z.1.1 γ L} :=
      ih.preimage (measurable_fst.fst.prodMk measurable_snd)
    have hcurrent : MeasurableSet {z : m.Sample (n+1) × ℝ |
        z.2 ∈ m.layerSwitchTimes n z.1.2 (m.curve n z.1.1 γ) L} := by
      have heq : {z : m.Sample (n+1) × ℝ |
          z.2 ∈ m.layerSwitchTimes n z.1.2 (m.curve n z.1.1 γ) L} =
          ⋃ r, {z : m.Sample (n+1) × ℝ | z.2 ∈
            Paper35.switchSet (m.layerScores n z.1.2 (m.curve n z.1.1 γ) r) L} := by
        ext z
        simp only [layerSwitchTimes,mem_setOf_eq,mem_iUnion]
      rw [heq]
      apply MeasurableSet.iUnion
      intro r
      exact measurableSet_affineSwitchGraph
        (fun ω : m.Sample (n+1) => m.curve n ω.1 γ) L hL
        (fun ω => m.continuousOn_curve n ω.1 γ L hc)
        (fun t => (m.continuous_network_parameter n (γ t)).measurable.comp measurable_fst)
        (fun ω => ω.2 r) ((measurable_pi_apply r).comp measurable_snd)
    exact hpast.union hcurrent

theorem measurable_switchCount (hLN : LusinNovikovLaw) (n : ℕ)
    (γ : ℝ → Space (m.width 0)) (L : ℝ) (hL : 0 < L)
    (hc : ContinuousOn γ (Icc 0 L)) :
    Measurable (fun ω : m.Sample n => m.switchCount n ω γ L) := by
  exact measurable_sectionCount_of_LusinNovikov (hLN (m.Sample n) ℝ)
    (m.measurableSet_switchTimesGraph n γ L hL hc)
    (fun ω => m.switchTimes_countable n ω γ L)

/-- Whenever the proved source bound is finite, the displayed extended
expectation is exactly the ordinary Bochner expectation of the actual count. -/
theorem expectedCount_eq_integral (hLN : LusinNovikovLaw) (n : ℕ)
    (γ : ℝ → Space (m.width 0)) (L : ℝ) (hL : 0 < L)
    (hc : ContinuousOn γ (Icc 0 L)) (hfin : m.expectedCount n γ L < ⊤) :
    m.expectedCount n γ L = ENNReal.ofReal
      (∫ ω, (m.switchCount n ω γ L).toReal ∂m.law n) := by
  have hm := m.measurable_switchCount hLN n γ L hL hc
  rw [integral_toReal hm.aemeasurable (ae_lt_top hm hfin.ne)]
  exact (ENNReal.ofReal_toReal hfin.ne).symm

theorem expectedLength_eq_integral (n : ℕ)
    (γ : ℝ → Space (m.width 0)) (L : ℝ) (hfin : m.expectedLength n γ L < ⊤) :
    m.expectedLength n γ L = ENNReal.ofReal
      (∫ ω, (m.curveLength n ω γ L).toReal ∂m.law n) := by
  have hm := m.measurable_curveLength n γ L
  rw [integral_toReal hm.aemeasurable (ae_lt_top hm hfin.ne)]
  exact (ENNReal.ofReal_toReal hfin.ne).symm

/-- Under the original weight L² assumptions both source expectations are
ordinary, integrable real expectations. The formulas identify the extended
bounds (8.6),(8.7) with those usual expectations without assigning `toReal ∞`
to a positive-probability infinite count. -/
theorem ordinary_expectations_of_source
    (hLN : LusinNovikovLaw) (hUP : BorelProjectionLaw)
    (harc : Paper35.CurveCalculus.ArclengthFactorizationInput)
    (hlinear : Paper35.CurveCalculus.LinearACCalculusInput)
    (hmax : Paper35.CurveCalculus.FiniteMaxACCalculusInput)
    (models : ∀ n, m.LayerSource n)
    (hW : ∀ n r, MemLp (fun w => w) 2 ((models n).unit r).weights)
    (γ : ℝ → Space (m.width 0)) (L : ℝ) (hL : 0 < L)
    (hc : ContinuousOn γ (Icc 0 L)) (hf : eVariationOn γ (Icc 0 L) ≠ ∞) (N : ℕ) :
    Integrable (fun ω => (m.switchCount N ω γ L).toReal) (m.law N) ∧
    Integrable (fun ω => (m.curveLength N ω γ L).toReal) (m.law N) ∧
    m.expectedCount N γ L = ENNReal.ofReal
      (∫ ω, (m.switchCount N ω γ L).toReal ∂m.law N) ∧
    m.expectedLength N γ L = ENNReal.ofReal
      (∫ ω, (m.curveLength N ω γ L).toReal ∂m.law N) := by
  have hC := m.expectedCount_lt_top_of_source hLN hUP harc hlinear hmax models hW γ L hL.le hc hf N
  have hA := m.expectedLength_lt_top_of_source harc hlinear hmax models hW γ L hc hf N
  exact ⟨integrable_toReal_of_lintegral_ne_top
      (m.measurable_switchCount hLN N γ L hL hc).aemeasurable hC.ne,
    integrable_toReal_of_lintegral_ne_top (m.measurable_curveLength N γ L).aemeasurable hA.ne,
    m.expectedCount_eq_integral hLN N γ L hL hc hC,
    m.expectedLength_eq_integral N γ L hA⟩

end Paper35.DeepModel.Network
