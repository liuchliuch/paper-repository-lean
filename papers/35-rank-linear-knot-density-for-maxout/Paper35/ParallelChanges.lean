import Paper35.MaximizerChanges
import Paper35.RandomProbes
import Paper35.DistributionFree
import Mathlib.Data.Finset.Max

/-! The joint active-index tuple in Corollary 2.7 is identified with the
distinct-time union count, including simultaneous changes and arbitrary
dependence between units. -/
noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace Paper35.ParallelChanges
open Source Source.WeightedModel Source.CrossingRegularity VisibleCrossing
open MaximizerChanges

variable {d K : ℕ}

/-- Local unique maximizers on both sides; they may be the same candidate. -/
def SidedMaximaAt (f : Fin K → ℝ → ℝ) (s : ℝ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∃ i j : Fin K,
    (∀ t ∈ Ioo (s-δ) s, UniqueMaximum f t i) ∧
    (∀ t ∈ Ioo s (s+δ), UniqueMaximum f t j)

theorem sidedMaximaAt_of_uniqueMaximum {f : Fin K → ℝ → ℝ} {s : ℝ}
    (hc : ∀ i, ContinuousAt (f i) s) {i : Fin K} (hi : UniqueMaximum f s i) :
    SidedMaximaAt f s := by
  have hall : ∀ᶠ t in 𝓝 s, UniqueMaximum f t i := by
    apply eventually_all.mpr
    intro j
    by_cases hji : j = i
    · exact Eventually.of_forall (fun _ h => (h hji).elim)
    have hpos : 0 < f i s-f j s := sub_pos.mpr (hi j hji)
    have he := (tendsto_order.mp ((hc i).sub (hc j)).tendsto).1 0 hpos
    filter_upwards [he] with t ht
    exact fun _ => sub_pos.mp ht
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp hall
  refine ⟨δ,hδ,i,i,?_,?_⟩ <;> intro t ht <;> apply hball <;>
    rw [Metric.mem_ball,Real.dist_eq] <;> apply abs_lt.mpr <;>
    constructor <;> linarith [ht.1,ht.2]

/-- If every strict visible equality is a genuine switch, every interior
parameter has unique maximizers on both sufficiently short sides. -/
theorem sidedMaximaAt_of_visible_regular {f : Fin K → ℝ → ℝ} {L s : ℝ}
    (hK : 0 < K) (_hs : s ∈ Ioo 0 L) (hc : ∀ i, ContinuousAt (f i) s)
    (hno : NoTripleMaximumAt f s)
    (hvis : ∀ q : OrderedCandidatePair K, VisiblePair f s q → ActiveSwitch f L s) :
    SidedMaximaAt f s := by
  classical
  have hne : (Finset.univ : Finset (Fin K)).Nonempty := ⟨⟨0,hK⟩,Finset.mem_univ _⟩
  obtain ⟨i,_,hmax⟩ := Finset.exists_max_image Finset.univ (fun i => f i s) hne
  have hmax' (k : Fin K) : f k s ≤ f i s := hmax k (Finset.mem_univ _)
  by_cases hi : UniqueMaximum f s i
  · exact sidedMaximaAt_of_uniqueMaximum hc hi
  have hex : ∃ j, j ≠ i ∧ f i s = f j s := by
    by_contra hn
    apply hi
    intro j hji
    apply lt_of_le_of_ne (hmax' j)
    intro heq
    exact hn ⟨j,hji,heq.symm⟩
  obtain ⟨j,hji,heq⟩ := hex
  have hgap (k : Fin K) (hki : k ≠ i) (hkj : k ≠ j) : f k s < f i s := by
    apply lt_of_le_of_ne (hmax' k)
    intro hki'
    exact hno i j k hji.symm hki.symm hkj.symm heq hki'.symm hmax'
  have ha : ActiveSwitch f L s := by
    rcases lt_or_gt_of_ne hji.symm with hij | hji'
    · exact hvis ⟨(i,j),hij⟩ ⟨heq,hgap⟩
    · apply hvis ⟨(j,i),hji'⟩
      refine ⟨heq.symm,?_⟩
      intro k hkj hki
      rw [← heq]
      exact hgap k hki hkj
  obtain ⟨_,_,δ,hδ,i,j,_,hl,hr⟩ := indexChangeAt_of_activeSwitch hc ha
  exact ⟨δ,hδ,i,j,hl,hr⟩

/-- Actual conditional-density source laws satisfy the deterministic local
side property, without any weight-moment assumption. -/
theorem ae_source_local_sides (p : Probe d) (m : Fin K → WeightedModel d) (hK : 0 < K)
    (hLN : LusinNovikovInput (Fin 2 → Candidate d) (ProbeParameter p))
    (hUP : BorelProjectionNullMeasurableInput (WeightPair d × BiasPair) (ProbeParameter p)) :
    ∀ᵐ θ ∂Measure.pi (fun a => (m a).joint), ∀ s ∈ Ioo 0 p.length,
      NoTripleMaximumAt (scores p θ) s ∧ SidedMaximaAt (scores p θ) s := by
  have hgood : ∀ᵐ θ ∂Measure.pi (fun a => (m a).joint), ∀ q : OrderedCandidatePair K,
      ((θ q.1.1).2,(θ q.1.2).2) ∉
        Source.CrossingArea.exceptionalBiases p (θ q.1.1).1 (θ q.1.2).1 :=
    ae_all_iff.mpr (fun q => ae_selectedPair_not_exceptional p m q hUP)
  filter_upwards [hgood,ae_no_triple_ties p m hLN hUP] with θ hg hn s hs
  have hc (i : Fin K) : ContinuousAt (scores p θ i) s :=
    (continuousAt_const.inner (p.lipschitz.continuousOn.continuousAt
      (Icc_mem_nhds hs.1 hs.2))).add continuousAt_const
  have hno : NoTripleMaximumAt (scores p θ) s := by
    intro i j k hij hik hjk heq hek _
    exact hn i j k hij hik hjk s hs ⟨heq,hek⟩
  refine ⟨hno,sidedMaximaAt_of_visible_regular hK hs hc hno ?_⟩
  intro q hq
  have hmem : s ∈ pairSwitchSet (scores p θ) p.length q := by
    rw [Source.CrossingArea.pairSwitchSet_eq_visibleEqualityTimes p θ q (hg q)]
    exact ⟨hs,hq⟩
  exact ⟨hmem.1,hmem.2.1,q.1.1,q.1.2,ne_of_lt q.2,hmem.2.2.1.1,
    hmem.2.2.1.2,hmem.2.2.2⟩

variable {ι : Type*} [Fintype ι] {k : ι → ℕ}

/-- The complete active-index tuple is constant and unique on either side,
and at least one of its components differs between the two sides. -/
def TupleChangeAt (k : ι → ℕ) (f : (r : ι) → Fin (k r) → ℝ → ℝ) (L s : ℝ) : Prop :=
  0 < s ∧ s < L ∧ ∃ δ : ℝ, 0 < δ ∧ ∃ I J : (r : ι) → Fin (k r), I ≠ J ∧
    (∀ t ∈ Ioo (s-δ) s, ∀ r, UniqueMaximum (f r) t (I r)) ∧
    (∀ t ∈ Ioo s (s+δ), ∀ r, UniqueMaximum (f r) t (J r))

def tupleChangeCount (k : ι → ℕ) (f : (r : ι) → Fin (k r) → ℝ → ℝ) (L : ℝ) : ℝ≥0∞ :=
  ({s | TupleChangeAt k f L s}.encard : ℝ≥0∞)

theorem tupleChangeAt_iff_exists_activeSwitch
    {f : (r : ι) → Fin (k r) → ℝ → ℝ} {L s : ℝ}
    (hc : ∀ r i, ContinuousAt (f r i) s)
    (hno : ∀ r, NoTripleMaximumAt (f r) s)
    (hside : ∀ r, SidedMaximaAt (f r) s) :
    TupleChangeAt k f L s ↔ ∃ r, ActiveSwitch (f r) L s := by
  classical
  constructor
  · rintro ⟨hs0,hsL,δ,hδ,I,J,hne,hl,hr⟩
    have hex : ∃ r, I r ≠ J r := by
      by_contra hn
      push_neg at hn
      exact hne (funext hn)
    obtain ⟨r,hrne⟩ := hex
    exact ⟨r,activeSwitch_of_indexChangeAt (hc r) (hno r)
      ⟨hs0,hsL,δ,hδ,I r,J r,hrne,(fun t ht => hl t ht r),(fun t ht => hr t ht r)⟩⟩
  · rintro ⟨r₀,ha⟩
    obtain ⟨hs0,hsL,δ₀,hδ₀,i₀,j₀,hij₀,hl₀,hr₀⟩ := indexChangeAt_of_activeSwitch (hc r₀) ha
    have hall (r : ι) : ∃ δ : ℝ, 0 < δ ∧ ∃ i j : Fin (k r),
        (r = r₀ → i ≠ j) ∧
        (∀ t ∈ Ioo (s-δ) s, UniqueMaximum (f r) t i) ∧
        (∀ t ∈ Ioo s (s+δ), UniqueMaximum (f r) t j) := by
      by_cases h : r = r₀
      · subst r
        exact ⟨δ₀,hδ₀,i₀,j₀,(fun _ => hij₀),hl₀,hr₀⟩
      · obtain ⟨δ,hδ,i,j,hl,hr⟩ := hside r
        exact ⟨δ,hδ,i,j,(fun he => (h he).elim),hl,hr⟩
    choose δ hδ I J hne hl hr using hall
    have hn : (Finset.univ : Finset ι).Nonempty := ⟨r₀,Finset.mem_univ _⟩
    let ε : ℝ := Finset.univ.inf' hn δ
    have hε : 0 < ε := (Finset.lt_inf'_iff hn).mpr (fun r _ => hδ r)
    have hεle (r : ι) : ε ≤ δ r := Finset.inf'_le δ (Finset.mem_univ r)
    refine ⟨hs0,hsL,ε,hε,I,J,?_,?_,?_⟩
    · intro heq
      exact hne r₀ rfl (congrFun heq r₀)
    · intro t ht r
      apply hl r t
      exact ⟨by linarith [ht.1,hεle r],ht.2⟩
    · intro t ht r
      apply hr r t
      exact ⟨ht.1,by linarith [ht.2,hεle r]⟩

theorem jointSwitchCount_eq_tupleChangeCount
    (f : (r : ι) → Fin (k r) → ℝ → ℝ) (L : ℝ)
    (hc : ∀ s ∈ Ioo 0 L, ∀ r i, ContinuousAt (f r i) s)
    (hreg : ∀ s ∈ Ioo 0 L, ∀ r,
      NoTripleMaximumAt (f r) s ∧ SidedMaximaAt (f r) s) :
    Deep.jointSwitchCount k f L = tupleChangeCount k f L := by
  unfold Deep.jointSwitchCount Deep.allSwitchCount Deep.allSwitchTimes tupleChangeCount
  apply congrArg (fun A : Set ℝ => (A.encard : ℝ≥0∞))
  ext s
  simp only [mem_iUnion,mem_setOf_eq,switchSet]
  by_cases hs : s ∈ Ioo 0 L
  · exact (tupleChangeAt_iff_exists_activeSwitch (hc s hs)
      (fun r => (hreg s hs r).1) (fun r => (hreg s hs r).2)).symm
  · constructor
    · rintro ⟨r,ha⟩
      exact (hs ⟨ha.1,ha.2.1⟩).elim
    · intro ht
      exact (hs ⟨ht.1,ht.2.1⟩).elim

/-- Arbitrarily coupled units inherit local regularity from their individual
source marginal laws. No between-unit independence is imposed. -/
theorem ae_jointSwitchCount_eq_tupleChangeCount
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (p : Probe d)
    (m : (r : ι) → Fin (k r) → WeightedModel d) (hk : ∀ r, 0 < k r)
    (a : (r : ι) → Ω → Fin (k r) → Candidate d) (ha : ∀ r, Measurable (a r))
    (hlaw : ∀ r, μ.map (a r) = Measure.pi (fun j => (m r j).joint))
    (hLN : LusinNovikovInput (Fin 2 → Candidate d) (ProbeParameter p))
    (hUP : BorelProjectionNullMeasurableInput (WeightPair d × BiasPair) (ProbeParameter p)) :
    ∀ᵐ ω ∂μ, Deep.jointSwitchCount k (fun r => scores p (a r ω)) p.length =
      tupleChangeCount k (fun r => scores p (a r ω)) p.length := by
  have hall : ∀ᵐ ω ∂μ, ∀ r, ∀ s ∈ Ioo 0 p.length,
      NoTripleMaximumAt (scores p (a r ω)) s ∧ SidedMaximaAt (scores p (a r ω)) s := by
    apply ae_all_iff.mpr
    intro r
    have H := ae_source_local_sides p (m r) (hk r) hLN hUP
    rw [← hlaw r] at H
    exact ae_of_ae_map (ha r).aemeasurable H
  filter_upwards [hall] with ω hω
  apply jointSwitchCount_eq_tupleChangeCount
  · intro s hs r i
    exact (continuousAt_const.inner (p.lipschitz.continuousOn.continuousAt
      (Icc_mem_nhds hs.1 hs.2))).add continuousAt_const
  · exact fun s hs r => hω r s hs

theorem expected_jointSwitchCount_eq_tupleChangeCount
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (p : Probe d)
    (m : (r : ι) → Fin (k r) → WeightedModel d) (hk : ∀ r, 0 < k r)
    (a : (r : ι) → Ω → Fin (k r) → Candidate d) (ha : ∀ r, Measurable (a r))
    (hlaw : ∀ r, μ.map (a r) = Measure.pi (fun j => (m r j).joint))
    (hLN : LusinNovikovInput (Fin 2 → Candidate d) (ProbeParameter p))
    (hUP : BorelProjectionNullMeasurableInput (WeightPair d × BiasPair) (ProbeParameter p)) :
    (∫⁻ ω, Deep.jointSwitchCount k (fun r => scores p (a r ω)) p.length ∂μ) =
      ∫⁻ ω, tupleChangeCount k (fun r => scores p (a r ω)) p.length ∂μ :=
  lintegral_congr_ae (ae_jointSwitchCount_eq_tupleChangeCount μ p m hk a ha hlaw hLN hUP)

/-- Literal Corollary 2.7 (2.15), with the left side counting changes of the
whole unique active-index tuple and every internal estimate discharged. -/
theorem corollary_2_7_tuple
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (hLN : ClassicalInputs.LusinNovikovLaw) (hUP : ClassicalInputs.BorelProjectionLaw)
    (m : ι → WeightedModel d) (B : ι → ℝ≥0)
    (hb : ∀ r, ∀ᵐ w ∂(m r).weights, (m r).b₀ w = B r)
    (hW : ∀ r, MemLp (fun w => w) 2 (m r).weights) (hk : ∀ r, 2 ≤ k r)
    (p : Probe d) (a : (r : ι) → Ω → Fin (k r) → Candidate d)
    (ha : ∀ r, Measurable (a r)) (hlaw : ∀ r, μ.map (a r) = (m r).iid (k r)) :
    (∫⁻ ω, tupleChangeCount k (fun r => scores p (a r ω)) p.length ∂μ) ≤
      (1/ENNReal.ofReal (Real.sqrt 3)) * ∫⁻ s in Icc 0 p.length,
        ∑ r, (k r : ℝ≥0∞)*B r*RandomProbes.covarianceSpeed (m r) p s := by
  rw [← expected_jointSwitchCount_eq_tupleChangeCount μ p (fun r _ => m r)
    (fun r => lt_of_lt_of_le (by norm_num : 0 < 2) (hk r)) a ha hlaw (hLN _ _) (hUP _ _)]
  exact RandomProbes.parallel_covariance_bound (DistributionFree.weighted_covariance hLN hUP)
    μ k m B hb hW hk p a ha hlaw (fun _ => hLN _ _)

end Paper35.ParallelChanges
