import MEJF.EfficiencyModel
import MEJF.SetupMeasurable
import MEJF.MainResults

/-! # Proposition 7.2 on the actual statistical sample space

The shared `EfficiencyModel.learner K` is used for both procedures. The
noiseless and atomless laws are genuine exchangeable probability measures.
The interval lengths below evaluate `Setup` predictions, radii and endpoints.
-/
namespace MEJF.EfficiencyCompletion

open MeasureTheory Filter
open MEJF.Efficiency MEJF.EfficiencyLaw MEJF.EfficiencyModel

noncomputable section
attribute [local instance] Classical.propDecidable
local instance : MeasurableSpace (Equiv.Perm Type20) := ⊤
local instance : MeasurableSingletonClass (Equiv.Perm Type20) := ⟨fun _ => trivial⟩

/-- Pathwise endpoint-rule average length on a realized test block. -/
def endpointAverage (K : ℝ) (Z : BlockArray) (i : Type20) : ℝ :=
  average19 (fun j => actualEndpointLength K Z i j)

/-- Pathwise minmax average length on the same realized test block. -/
def minmaxAverage (K : ℝ) (Z : BlockArray) (i : Type20) : ℝ :=
  average19 (fun j => actualMinmaxLength K Z i j)

/-- The actual pathwise average-length advantage (7.1). -/
def advantage (K : ℝ) (Z : BlockArray) (i : Type20) : ℝ :=
  average19 (fun j => actualMinmaxLength K Z i j-actualEndpointLength K Z i j)

lemma advantage_eq (K : ℝ) (Z : BlockArray) (i : Type20) :
    advantage K Z i = minmaxAverage K Z i-endpointAverage K Z i :=
  average19_sub _ _

lemma measurable_actualEndpointLength (K : ℝ) (i : Type20) (j : Coord19) :
    Measurable (fun Z : BlockArray => actualEndpointLength K Z i j) := by
  unfold actualEndpointLength intervalLength
  exact ((Setup.measurable_upperEndpoint (m := 19) (n := 19) (learner K) i j 2 2 (by omega) (by omega)).sub
    (Setup.measurable_lowerEndpoint (m := 19) (n := 19) (learner K) i j 2 2 (by omega) (by omega))).max measurable_const

lemma measurable_actualMinmaxLength (K : ℝ) (i : Type20) (j : Coord19) :
    Measurable (fun Z : BlockArray => actualMinmaxLength K Z i j) := by
  have hp (k : Fin 19) : Measurable (fun Z : BlockArray => predictions (m := 19) (n := 19) (learner K) Z i j k) :=
    (Setup.measurable_pairPrediction (learner K) i (i.succAbove k)).comp
      (measurable_id.prodMk (Setup.measurable_covariate i j))
  have hs (k : Fin 19) : Measurable (fun Z : BlockArray => scores (m := 19) (n := 19) (learner K) Z i 4 (by omega) k) :=
    Setup.measurable_radius (learner K) (i.succAbove k) i 4 (by omega)
  have hq := MEJF.OrderStatistics.measurable_stat_comp _ hs (⟨15, by omega⟩ : Fin 19)
  have hlo := MEJF.OrderStatistics.measurable_stat_comp _ hp (0 : Fin 19)
  have hhi := MEJF.OrderStatistics.measurable_stat_comp _ hp (Fin.last 18)
  change Measurable (fun Z : BlockArray => max
    ((MEJF.OrderStatistics.stat (predictions (m := 19) (n := 19) (learner K) Z i j) (Fin.last 18) +
      MEJF.OrderStatistics.stat (scores (m := 19) (n := 19) (learner K) Z i 4 (by omega)) (⟨15, by omega⟩ : Fin 19)) -
     (MEJF.OrderStatistics.stat (predictions (m := 19) (n := 19) (learner K) Z i j) 0 -
      MEJF.OrderStatistics.stat (scores (m := 19) (n := 19) (learner K) Z i 4 (by omega)) (⟨15, by omega⟩ : Fin 19))) 0)
  exact ((hhi.add hq).sub (hlo.sub hq)).max measurable_const

lemma measurable_average19 {Ω : Type*} [MeasurableSpace Ω] (f : Coord19 → Ω → ℝ)
    (hf : ∀ j, Measurable (f j)) : Measurable (fun z => average19 (fun j => f j z)) := by
  unfold average19
  exact (Finset.measurable_sum _ (fun j _ => hf j)).div_const 19

lemma measurable_endpointAverage (K : ℝ) (i : Type20) : Measurable (fun Z => endpointAverage K Z i) :=
  measurable_average19 _ (measurable_actualEndpointLength K i)

lemma measurable_minmaxAverage (K : ℝ) (i : Type20) : Measurable (fun Z => minmaxAverage K Z i) :=
  measurable_average19 _ (measurable_actualMinmaxLength K i)

lemma measurable_advantage (K : ℝ) (i : Type20) : Measurable (fun Z => advantage K Z i) := by
  simp only [advantage_eq]
  exact (measurable_minmaxAverage K i).sub (measurable_endpointAverage K i)

/-- The four exact noiseless formulas (7.2)--(7.3). -/
def ZeroFormulas (K : ℝ) (Z : BlockArray) (i : Type20) : Prop :=
  endpointAverage K Z i = 2 ∧ minmaxAverage K Z i = (2*K+38)/19 ∧
  advantage K Z i = 2*K/19 ∧ endpointAverage K Z i/minmaxAverage K Z i = 38/(2*K+38)

/-- The four pathwise noisy estimates (7.4)--(7.5). Positivity of the advantage's
lower bound is proved separately from the support event. -/
def NoisyBounds (K ξ : ℝ) (Z : BlockArray) (i : Type20) : Prop :=
  (2*K-76*ξ)/19 ≤ advantage K Z i ∧ endpointAverage K Z i ≤ 2+2*ξ ∧
  (2*K+38-38*ξ)/19 ≤ minmaxAverage K Z i ∧
  endpointAverage K Z i/minmaxAverage K Z i ≤ 38*(1+ξ)/(2*K+38-38*ξ)

lemma measurableSet_zeroFormulas (K : ℝ) : MeasurableSet {Z : BlockArray | ∀ i, ZeroFormulas K Z i} := by
  simp only [Set.setOf_forall]
  apply MeasurableSet.iInter
  intro i
  exact (measurableSet_eq_fun (measurable_endpointAverage K i) measurable_const).inter
    ((measurableSet_eq_fun (measurable_minmaxAverage K i) measurable_const).inter
      ((measurableSet_eq_fun (measurable_advantage K i) measurable_const).inter
        (measurableSet_eq_fun ((measurable_endpointAverage K i).div (measurable_minmaxAverage K i))
          measurable_const)))

lemma measurableSet_noisyBounds (K ξ : ℝ) :
    MeasurableSet {Z : BlockArray | ∀ i, NoisyBounds K ξ Z i} := by
  simp only [Set.setOf_forall]
  apply MeasurableSet.iInter
  intro i
  exact (measurableSet_le measurable_const (measurable_advantage K i)).inter
    ((measurableSet_le (measurable_endpointAverage K i) measurable_const).inter
      ((measurableSet_le measurable_const (measurable_minmaxAverage K i)).inter
        (measurableSet_le ((measurable_endpointAverage K i).div (measurable_minmaxAverage K i))
          measurable_const)))

/-- Exact lengths for every type permutation, evaluated by one actual shared
multiset learner and the actual Setup endpoint procedure. -/
theorem noiseless_every_permutation {K : ℝ} (hK : 0 < K) (p : Equiv.Perm Type20) (i : Type20) :
    ZeroFormulas K (reveal (p,fun _ => 0)) i := by
  have h := cyclic_zero_lengths hK p (p i)
  simpa only [ZeroFormulas, endpointAverage, minmaxAverage, advantage,
    actualEndpointLength_reveal, actualMinmaxLength_reveal] using h

/-- The exact formulas also hold directly almost surely under the actual
noiseless exchangeable law. -/
theorem noiseless_blockLaw {K : ℝ} (hK : 0 < K) :
    ∀ᵐ Z ∂zeroBlockLaw, ∀ i, ZeroFormulas K Z i := by
  rw [zeroBlockLaw, ae_map_iff (measurable_of_finite _).aemeasurable (measurableSet_zeroFormulas K)]
  exact Eventually.of_forall (fun p i => noiseless_every_permutation hK p i)

/-- Every bounded response realization has the original estimates when both
procedures evaluate the same real multiset learner. -/
theorem noisy_every_supported_sample {K ξ : ℝ} (hK : 0 < K) (hξ : 0 ≤ ξ)
    (hsmall : ξ < K/38) (s : Sample) (hs : ∀ a, |s.2 a| ≤ ξ) (i : Type20) :
    NoisyBounds K ξ (reveal s) i := by
  have h := cyclic_pathwise_bounds hK hξ hsmall s hs (s.1 i)
  simpa only [NoisyBounds, endpointAverage, minmaxAverage, advantage,
    actualEndpointLength_reveal, actualMinmaxLength_reveal] using ⟨h.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

/-- The pathwise estimates are statements about the actual atomless law on
complete block arrays, rather than only the construction's source space. -/
theorem noisy_blockLaw {K ξ : ℝ} (hK : 0 < K) (hξ : 0 < ξ) (hsmall : ξ < K/38) :
    ∀ᵐ Z ∂blockLaw ξ, ∀ i, NoisyBounds K ξ Z i := by
  rw [blockLaw, ae_map_iff reveal_measurable.aemeasurable (measurableSet_noisyBounds K ξ)]
  exact (sampleMeasure_bound hξ).mono (fun s hs i =>
    noisy_every_supported_sample hK (le_of_lt hξ) hsmall s hs i)

/-- The lower bound in (7.4) is strictly positive under exactly the stated
noise-radius restriction. -/
theorem noisy_advantage_positive {K ξ : ℝ} (hsmall : ξ < K/38) : 0 < (2*K-76*ξ)/19 := by
  have hnum : 0 < 2*K-76*ξ := by linarith
  exact div_pos hnum (by norm_num)

/-- The chosen levels produce precisely the finite ranks used by the actual
procedures in this module. -/
theorem selected_ranks : Setup.innerRank (1/10) 19 = 2 ∧ Setup.outerRank (1/10) 19 = 2 ∧
    Setup.innerRank (1/5) 19 = 4 ∧ Setup.outerRank (1/5) 19 = 4 := by
  norm_num [Setup.innerRank, Setup.outerRank]

/-- The selected valid pair is on the Pareto antichain, as stated in the proof. -/
theorem nonextreme_pareto : MEJF.RankFrontier.Pareto 4 2 2 2 := by
  apply (MEJF.RankFrontier.pareto_iff_inner (by norm_num : 0 < 2) (by norm_num : 2 ≤ 4)).mpr
  norm_num [MEJF.RankFrontier.innerTop]

/-- The noiseless endpoint-to-minmax average-length ratio in (7.3). -/
theorem noiseless_ratio_tendsto_zero :
    Tendsto (fun K : ℝ => 38/(2*K+38)) atTop (nhds 0) := by
  simpa using length_ratio_tendsto_zero 0

/-- Proposition 7.2, including the actual statistical validity value and the
explicit noiseless and atomless exchangeable models. The all-realization
statements above are stronger than the almost-sure assertions packaged here. -/
theorem proposition_7_2 (K : ℝ) (hK : 0 < K) :
    (Setup.finiteRankGamma 19 19 (1/5) 2 2 (by norm_num) (by norm_num) = 3/20 ∧
      Setup.finiteRankGamma 19 19 (1/5) 2 2 (by norm_num) (by norm_num) < 1/5) ∧
    IsProbabilityMeasure zeroBlockLaw ∧ Exchangeability.Exchangeable zeroBlockLaw ∧
    (∀ᵐ Z ∂zeroBlockLaw, ∀ i, ZeroFormulas K Z i) ∧
    Tendsto (fun κ : ℝ => 38/(2*κ+38)) atTop (nhds 0) ∧
    (∀ ξ : ℝ, 0 < ξ → ξ < K/38 →
      IsProbabilityMeasure (blockLaw ξ) ∧ NoAtoms (blockLaw ξ) ∧
      Exchangeability.Exchangeable (blockLaw ξ) ∧ 0 < (2*K-76*ξ)/19 ∧
      (∀ᵐ Z ∂blockLaw ξ, ∀ i, NoisyBounds K ξ Z i) ∧
      Tendsto (fun κ : ℝ => 38*(1+ξ)/(2*κ+38-38*ξ)) atTop (nhds 0)) := by
  refine ⟨MEJF.MainResults.nonextreme_validity, inferInstance, zeroBlockLaw_exchangeable,
    noiseless_blockLaw hK, noiseless_ratio_tendsto_zero, ?_⟩
  intro ξ hξ hsmall
  exact ⟨blockLaw_probability hξ, inferInstance, blockLaw_exchangeable ξ,
    noisy_advantage_positive hsmall, noisy_blockLaw hK hξ hsmall, length_ratio_tendsto_zero ξ⟩

end
end MEJF.EfficiencyCompletion
