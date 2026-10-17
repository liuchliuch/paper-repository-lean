import Paper35.CrossingRegularity
import Mathlib.Topology.Order.LeftRightNhds
import Mathlib.Topology.Order.DenselyOrdered

/-! The trailing semantic assertion of Definition 2.1. Projection regions are
the input-space strict-affine-dominance interiors: this is the projection-
region object used in Goujon et al., Definition 6. Their changes along a path
are counted at distinct parameters, including self-intersections and retracing.
The equivalence below is proved for continuous paths, hence includes CPWL paths. -/
noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal Topology
namespace Paper35.MaximizerChanges
open Source Source.WeightedModel VisibleCrossing CrossingRegularity
variable {d K : ℕ}

/-- Candidate i is the unique maximizer at this parameter. -/
def UniqueMaximum (f : Fin K → ℝ → ℝ) (t : ℝ) (i : Fin K) : Prop :=
  ∀ j, j ≠ i → f j t < f i t

/-- Distinct locally unique active indices on the two sides of the parameter. -/
def IndexChangeAt (f : Fin K → ℝ → ℝ) (L s : ℝ) : Prop :=
  0 < s ∧ s < L ∧ ∃ δ : ℝ, 0 < δ ∧ ∃ i j : Fin K, i ≠ j ∧
    (∀ t ∈ Ioo (s-δ) s, UniqueMaximum f t i) ∧
    (∀ t ∈ Ioo s (s+δ), UniqueMaximum f t j)

/-- Only triple ties at the maximum are excluded in the deterministic result. -/
def NoTripleMaximumAt (f : Fin K → ℝ → ℝ) (s : ℝ) : Prop :=
  ∀ i j k : Fin K, i ≠ j → i ≠ k → j ≠ k →
    f i s = f j s → f i s = f k s → (∀ a, f a s ≤ f i s) → False

/-- An actual active switch gives locally constant, distinct unique maximizing
indices on its sides. Continuity preserves strict gaps to all other candidates. -/
theorem indexChangeAt_of_activeSwitch {f : Fin K → ℝ → ℝ} {L s : ℝ}
    (hc : ∀ i, ContinuousAt (f i) s) (ha : ActiveSwitch f L s) : IndexChangeAt f L s := by
  classical
  obtain ⟨hs0,hsL,i,j,hij,heq,hgap,δ₀,hδ₀,hsgn⟩ := ha
  have hall : ∀ᶠ t in 𝓝 s, ∀ k, k ≠ i → k ≠ j → f k t < f i t ∧ f k t < f j t := by
    apply eventually_all.mpr
    intro k
    by_cases hki : k = i
    · exact Eventually.of_forall fun _ h => (h hki).elim
    by_cases hkj : k = j
    · exact Eventually.of_forall fun _ _ h => (h hkj).elim
    have hki0 : 0 < f i s - f k s := sub_pos.mpr (hgap k hki hkj)
    have hkj0 : 0 < f j s - f k s := by rw [← heq]; exact hki0
    have hki' : ∀ᶠ t in 𝓝 s, 0 < f i t - f k t :=
      (tendsto_order.mp ((hc i).sub (hc k)).tendsto).1 0 hki0
    have hkj' : ∀ᶠ t in 𝓝 s, 0 < f j t - f k t :=
      (tendsto_order.mp ((hc j).sub (hc k)).tendsto).1 0 hkj0
    filter_upwards [hki',hkj'] with t hi hj
    exact fun _ _ => ⟨sub_pos.mp hi,sub_pos.mp hj⟩
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp hall
  let δ := min δ₀ ε
  have hδ : 0 < δ := lt_min hδ₀ hε
  have hnear {t : ℝ} (ht : t ∈ Ioo (s-δ) (s+δ)) :
      ∀ k, k ≠ i → k ≠ j → f k t < f i t ∧ f k t < f j t := by
    apply hball
    rw [Metric.mem_ball,Real.dist_eq]
    apply abs_lt.mpr
    constructor <;> linarith [ht.1,ht.2,min_le_right δ₀ ε]
  have hleft {t : ℝ} (ht : t ∈ Ioo (s-δ) s) :
      t ∈ Ioo (s-δ₀) s ∧ t ∈ Ioo (s-δ) (s+δ) := by
    constructor
    · constructor <;> linarith [ht.1,ht.2,min_le_left δ₀ ε]
    · exact ⟨ht.1,by linarith [ht.2]⟩
  have hright {t : ℝ} (ht : t ∈ Ioo s (s+δ)) :
      t ∈ Ioo s (s+δ₀) ∧ t ∈ Ioo (s-δ) (s+δ) := by
    constructor
    · constructor <;> linarith [ht.1,ht.2,min_le_left δ₀ ε]
    · exact ⟨by linarith [ht.1],ht.2⟩
  have hmaxi {t : ℝ} (ht : t ∈ Ioo (s-δ) (s+δ)) (hji : f j t < f i t) :
      UniqueMaximum f t i := by
    intro k hki
    by_cases hkj : k = j
    · simpa only [hkj] using hji
    exact (hnear ht k hki hkj).1
  have hmaxj {t : ℝ} (ht : t ∈ Ioo (s-δ) (s+δ)) (hij' : f i t < f j t) :
      UniqueMaximum f t j := by
    intro k hkj
    by_cases hki : k = i
    · simpa only [hki] using hij'
    exact (hnear ht k hki hkj).2
  rcases hsgn with hsgn | hsgn
  · refine ⟨hs0,hsL,δ,hδ,j,i,hij.symm,?_,?_⟩
    · intro t ht
      exact hmaxj (hleft ht).2 (sub_neg.mp (hsgn.1 t (hleft ht).1))
    · intro t ht
      exact hmaxi (hright ht).2 (sub_pos.mp (hsgn.2 t (hright ht).1))
  · refine ⟨hs0,hsL,δ,hδ,i,j,hij,?_,?_⟩
    · intro t ht
      exact hmaxi (hleft ht).2 (sub_pos.mp (hsgn.1 t (hleft ht).1))
    · intro t ht
      exact hmaxj (hright ht).2 (sub_neg.mp (hsgn.2 t (hright ht).1))

/-- Continuity forces the left and right maximizing candidates to tie at the
maximum. Exclusion of a third maximum makes this an actual active switch. -/
theorem activeSwitch_of_indexChangeAt {f : Fin K → ℝ → ℝ} {L s : ℝ}
    (hc : ∀ i, ContinuousAt (f i) s) (hno : NoTripleMaximumAt f s)
    (ha : IndexChangeAt f L s) : ActiveSwitch f L s := by
  obtain ⟨hs0,hsL,δ,hδ,i,j,hij,hl,hr⟩ := ha
  have hmaxi (k : Fin K) : f k s ≤ f i s := by
    apply le_of_tendsto_of_tendsto
      ((hc k).tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[<] s ≤ 𝓝 s))
      ((hc i).tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[<] s ≤ 𝓝 s))
    filter_upwards [Ioo_mem_nhdsLT (by linarith : s-δ < s)] with t ht
    by_cases hki : k = i
    · rw [hki]
    · exact (hl t ht k hki).le
  have hmaxj (k : Fin K) : f k s ≤ f j s := by
    apply le_of_tendsto_of_tendsto
      ((hc k).tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[>] s ≤ 𝓝 s))
      ((hc j).tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[>] s ≤ 𝓝 s))
    filter_upwards [Ioo_mem_nhdsGT (by linarith : s < s+δ)] with t ht
    by_cases hkj : k = j
    · rw [hkj]
    · exact (hr t ht k hkj).le
  have heq : f i s = f j s := le_antisymm (hmaxj i) (hmaxi j)
  refine ⟨hs0,hsL,i,j,hij,heq,?_,δ,hδ,Or.inr ⟨?_,?_⟩⟩
  · intro k hki hkj
    apply lt_of_le_of_ne (hmaxi k)
    intro hk
    exact hno i j k hij hki.symm hkj.symm heq hk.symm hmaxi
  · intro t ht
    exact sub_pos.mpr (hl t ht j hij.symm)
  · intro t ht
    exact sub_neg.mpr (hr t ht i hij)

theorem indexChangeAt_iff_activeSwitch {f : Fin K → ℝ → ℝ} {L s : ℝ}
    (hc : ∀ i, ContinuousAt (f i) s) (hno : NoTripleMaximumAt f s) :
    IndexChangeAt f L s ↔ ActiveSwitch f L s :=
  ⟨activeSwitch_of_indexChangeAt hc hno,indexChangeAt_of_activeSwitch hc⟩

def indexChangeCount (f : Fin K → ℝ → ℝ) (L : ℝ) : ℝ≥0∞ :=
  ({s | IndexChangeAt f L s}.encard : ℝ≥0∞)

/-- Counting distinct local unique-index changes agrees with Definition 2.1. -/
theorem switchCount_eq_indexChangeCount (f : Fin K → ℝ → ℝ) (L : ℝ)
    (hc : ∀ s ∈ Ioo 0 L, ∀ i, ContinuousAt (f i) s)
    (hno : ∀ s ∈ Ioo 0 L, NoTripleMaximumAt f s) :
    switchCount f L = indexChangeCount f L := by
  unfold switchCount switchSet indexChangeCount
  apply congrArg (fun A : Set ℝ => (A.encard : ℝ≥0∞))
  ext s
  by_cases hs : s ∈ Ioo 0 L
  · exact (indexChangeAt_iff_activeSwitch (hc s hs) (hno s hs)).symm
  · exact iff_of_false (fun h => hs ⟨h.1,h.2.1⟩) (fun h => hs ⟨h.1,h.2.1⟩)

/-- Strict projection-region interior in input space, defined from the actual
candidate affine functions, before choosing any path. -/
def projectionRegion (θ : Fin K → Candidate d) (i : Fin K) : Set (Space d) :=
  {x | ∀ j, j ≠ i → scoreValue x (θ j) < scoreValue x (θ i)}

def pathScores (γ : ℝ → Space d) (θ : Fin K → Candidate d) : Fin K → ℝ → ℝ :=
  fun i t => scoreValue (γ t) (θ i)

def RegionChangeAt (θ : Fin K → Candidate d) (γ : ℝ → Space d) (L s : ℝ) : Prop :=
  0 < s ∧ s < L ∧ ∃ δ : ℝ, 0 < δ ∧ ∃ i j : Fin K, i ≠ j ∧
    (∀ t ∈ Ioo (s-δ) s, γ t ∈ projectionRegion θ i) ∧
    (∀ t ∈ Ioo s (s+δ), γ t ∈ projectionRegion θ j)

/-- Input-space region membership is exactly strict unique maximization. -/
theorem regionChangeAt_iff_indexChangeAt (θ : Fin K → Candidate d)
    (γ : ℝ → Space d) (L s : ℝ) :
    RegionChangeAt θ γ L s ↔ IndexChangeAt (pathScores γ θ) L s := Iff.rfl

def regionChangeCount (θ : Fin K → Candidate d) (γ : ℝ → Space d) (L : ℝ) : ℝ≥0∞ :=
  ({s | RegionChangeAt θ γ L s}.encard : ℝ≥0∞)

lemma indexChangeCount_eq_regionChangeCount (θ : Fin K → Candidate d)
    (γ : ℝ → Space d) (L : ℝ) :
    indexChangeCount (pathScores γ θ) L = regionChangeCount θ γ L := rfl

/-- The direct pathwise projection-region identification holds for every
continuous path at the candidate change, without a CPWL assumption. -/
theorem regionChangeAt_iff_activeSwitch (θ : Fin K → Candidate d)
    (γ : ℝ → Space d) (L s : ℝ) (hγ : ContinuousAt γ s)
    (hno : NoTripleMaximumAt (pathScores γ θ) s) :
    RegionChangeAt θ γ L s ↔ ActiveSwitch (pathScores γ θ) L s := by
  rw [regionChangeAt_iff_indexChangeAt]
  apply indexChangeAt_iff_activeSwitch
  · intro i
    exact (continuousAt_const.inner hγ).add continuousAt_const
  · exact hno

theorem switchCount_eq_regionChangeCount (θ : Fin K → Candidate d)
    (γ : ℝ → Space d) (L : ℝ) (hγ : ContinuousOn γ (Icc 0 L))
    (hno : ∀ s ∈ Ioo 0 L, NoTripleMaximumAt (pathScores γ θ) s) :
    switchCount (pathScores γ θ) L = regionChangeCount θ γ L := by
  apply (switchCount_eq_indexChangeCount _ _ _ hno).trans
  · rfl
  · intro s hs i
    exact (continuousAt_const.inner (hγ.continuousAt (Icc_mem_nhds hs.1 hs.2))).add continuousAt_const

/-- Source random-candidate semantic identification. The path can be any
Probe, so this includes every finite-length CPWL Probe. -/
theorem ae_count_eq_index_and_region_changes (p : Probe d) (m : Fin K → WeightedModel d)
    (hLN : LusinNovikovInput (Fin 2 → Candidate d) (ProbeParameter p))
    (hUP : BorelProjectionNullMeasurableInput (WeightPair d × BiasPair) (ProbeParameter p)) :
    ∀ᵐ θ ∂Measure.pi (fun a => (m a).joint),
      switchCount (scores p θ) p.length = indexChangeCount (scores p θ) p.length ∧
      switchCount (scores p θ) p.length = regionChangeCount θ p.curve p.length := by
  filter_upwards [ae_no_triple_ties p m hLN hUP] with θ hθ
  have hc (s : ℝ) (hs : s ∈ Ioo 0 p.length) (i : Fin K) : ContinuousAt (scores p θ i) s :=
    (continuousAt_const.inner (p.lipschitz.continuousOn.continuousAt (Icc_mem_nhds hs.1 hs.2))).add continuousAt_const
  have hno (s : ℝ) (hs : s ∈ Ioo 0 p.length) : NoTripleMaximumAt (scores p θ) s := by
    intro i j k hij hik hjk heq hek _
    exact hθ i j k hij hik hjk s hs ⟨heq,hek⟩
  have heq := switchCount_eq_indexChangeCount (scores p θ) p.length hc hno
  exact ⟨heq,heq⟩

/-- The semantic count identifications pass to the genuine source expectation
in the extended nonnegative sense. No count-measurability assumption is added. -/
theorem expectedCount_eq_index_and_region_changes (p : Probe d) (m : Fin K → WeightedModel d)
    (hLN : LusinNovikovInput (Fin 2 → Candidate d) (ProbeParameter p))
    (hUP : BorelProjectionNullMeasurableInput (WeightPair d × BiasPair) (ProbeParameter p)) :
    expectedSwitchCount (Measure.pi fun a => (m a).joint) (scores p) p.length =
      (∫⁻ θ, indexChangeCount (scores p θ) p.length ∂Measure.pi (fun a => (m a).joint)) ∧
    expectedSwitchCount (Measure.pi fun a => (m a).joint) (scores p) p.length =
      (∫⁻ θ, regionChangeCount θ p.curve p.length ∂Measure.pi (fun a => (m a).joint)) := by
  constructor <;> apply lintegral_congr_ae
  · filter_upwards [ae_count_eq_index_and_region_changes p m hLN hUP] with θ hθ
    exact hθ.1
  · filter_upwards [ae_count_eq_index_and_region_changes p m hLN hUP] with θ hθ
    exact hθ.2

/-- The identified change sets are themselves almost surely finite under the
source hypotheses, not merely count variables with the same expectation. -/
theorem ae_index_and_region_change_sets_finite (p : Probe d) (m : Fin K → WeightedModel d)
    (hLN : LusinNovikovInput (Fin 2 → Candidate d) (ProbeParameter p))
    (hUP : BorelProjectionNullMeasurableInput (WeightPair d × BiasPair) (ProbeParameter p)) :
    ∀ᵐ θ ∂Measure.pi (fun a => (m a).joint),
      {s | IndexChangeAt (scores p θ) p.length s}.Finite ∧
      {s | RegionChangeAt θ p.curve p.length s}.Finite := by
  filter_upwards [ae_no_triple_ties p m hLN hUP,ae_switchSet_finite p m hUP] with θ hθ hfin
  have hsub : {s | IndexChangeAt (scores p θ) p.length s} ⊆ switchSet (scores p θ) p.length := by
    intro s hs
    apply activeSwitch_of_indexChangeAt _ _ hs
    · intro i
      exact (continuousAt_const.inner (p.lipschitz.continuousOn.continuousAt
        (Icc_mem_nhds hs.1 hs.2.1))).add continuousAt_const
    · intro i j k hij hik hjk heq hek _
      exact hθ i j k hij hik hjk s ⟨hs.1,hs.2.1⟩ ⟨heq,hek⟩
  exact ⟨hfin.subset hsub,hfin.subset hsub⟩

end Paper35.MaximizerChanges
