import Paper35.VisibleCrossing
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Topology.Compactness.Compact

/-! Almost-sure source regularity without a weight moment assumption. -/
noncomputable section
open Set MeasureTheory MeasureTheory.Measure Filter
open scoped ENNReal Topology

namespace Paper35.Source.CrossingRegularity
open WeightedModel CrossingArea CrossingJacobian VisibleCrossing
variable {d K : ℕ}

/-- Nonzero derivatives isolate all interior zeros. Compactness and exclusion
of endpoint zeros then make the entire zero set finite. -/
theorem finite_zeros_of_transverse {f : ℝ → ℝ} {L : ℝ}
    (hf : ContinuousOn f (Icc 0 L)) (h0 : f 0 ≠ 0) (hL : f L ≠ 0)
    (htrans : ∀ s ∈ Ioo 0 L, f s = 0 → ∃ a ≠ 0, HasDerivAt f a s) :
    {s | s ∈ Icc 0 L ∧ f s = 0}.Finite := by
  let S : Set ℝ := {s | s ∈ Icc 0 L ∧ f s = 0}
  have hclosed : IsClosed S := isClosed_Icc.isClosed_eq hf continuousOn_const
  have hc : IsCompact S := isCompact_Icc.of_isClosed_subset hclosed (fun _ hs => hs.1)
  by_contra hinf
  obtain ⟨s, hs, hacc⟩ := exists_nhds_ne_inf_principal_neBot hc hinf
  have hs0 : 0 < s := lt_of_le_of_ne hs.1.1 (by intro h; subst s; exact h0 hs.2)
  have hsL : s < L := lt_of_le_of_ne hs.1.2 (by intro h; subst s; exact hL hs.2)
  obtain ⟨a, ha, hd⟩ := htrans s ⟨hs0,hsL⟩ hs.2
  have hne : ∀ᶠ t in 𝓝[≠] s, f t ≠ 0 := hd.eventually_ne ha
  have hcompl : Sᶜ ∈ 𝓝[≠] s := by
    filter_upwards [hne] with t ht
    exact fun hts => ht hts.2
  exact hacc.ne (inf_principal_eq_bot.mpr hcompl)

/-- The genuine equality parameters of a pair are finite outside the null
bias exception and the two endpoint ties. No first weight moment is required. -/
theorem pairEqualityTimes_finite (p : Probe d) (wi wj : Space d) (bi bj : ℝ)
    (hgood : (bi,bj) ∉ exceptionalBiases p wi wj)
    (h0 : inner ℝ wi (p.curve 0) + bi ≠ inner ℝ wj (p.curve 0) + bj)
    (hL : inner ℝ wi (p.curve p.length) + bi ≠ inner ℝ wj (p.curve p.length) + bj) :
    (pairEqualityTimes p wi wj bi bj).Finite := by
  let f : ℝ → ℝ := fun s => (inner ℝ wi (p.curve s) + bi) -
    (inner ℝ wj (p.curve s) + bj)
  have hi : ContinuousOn (fun s => inner ℝ wi (p.curve s) + bi) (Icc 0 p.length) :=
    (continuousOn_const.inner p.lipschitz.continuousOn).add continuousOn_const
  have hj : ContinuousOn (fun s => inner ℝ wj (p.curve s) + bj) (Icc 0 p.length) :=
    (continuousOn_const.inner p.lipschitz.continuousOn).add continuousOn_const
  have hf : {s | s ∈ Icc 0 p.length ∧ f s = 0}.Finite := by
    apply finite_zeros_of_transverse (hi.sub hj) (sub_ne_zero.mpr h0) (sub_ne_zero.mpr hL)
    intro s hs hz
    have heq : s ∈ pairEqualityTimes p wi wj bi bj := ⟨hs, sub_eq_zero.mp hz⟩
    obtain ⟨hdiff, hne⟩ := pairEquality_transverse_of_not_exceptional p wi wj bi bj hgood heq
    refine ⟨inner ℝ (wi-wj) (deriv p.curve s), hne, ?_⟩
    have hdi := ((hasDerivAt_const s wi).inner ℝ hdiff.hasDerivAt).add_const bi
    have hdj := ((hasDerivAt_const s wj).inner ℝ hdiff.hasDerivAt).add_const bj
    simpa only [f, inner_zero_left, zero_add, add_zero, inner_sub_left] using hdi.sub hdj
  apply hf.subset
  intro s hs
  exact ⟨Ioo_subset_Icc_self hs.1, sub_eq_zero.mpr hs.2⟩

/-- Any two different candidate laws have no tie at a fixed location. -/
theorem independent_pair_fixed_tie_null (mi mj : WeightedModel d) (x : Space d) :
    (mi.joint.prod mj.joint) {ab : Candidate d × Candidate d |
      scoreValue x ab.1 = scoreValue x ab.2} = 0 := by
  have H := independent_score_avoids_selected_height mi.joint mj (fun _ : Candidate d => x)
    (scoreValue x) measurable_const (measurable_scoreValue x)
  have hs : {ab : Candidate d × Candidate d | scoreValue x ab.1 = scoreValue x ab.2} =
      {ab : Candidate d × Candidate d | scoreValue x ab.2 = scoreValue x ab.1} := by
    ext ab
    exact eq_comm
  rw [hs]
  exact H

/-- No endpoint tie under the actual heterogeneous full parameter law. -/
theorem ae_selectedPair_no_fixed_tie (m : Fin K → WeightedModel d)
    (q : OrderedCandidatePair K) (x : Space d) :
    ∀ᵐ θ ∂Measure.pi (fun k => (m k).joint),
      scoreValue x (θ q.1.1) ≠ scoreValue x (θ q.1.2) := by
  have hnull := independent_pair_fixed_tie_null (m q.1.1) (m q.1.2) x
  rw [← map_selectedCandidates m q.1.1 q.1.2 (ne_of_lt q.2)] at hnull
  have H := preimage_null_of_map_null
    (((measurable_pi_apply q.1.1).prodMk (measurable_pi_apply q.1.2)).aemeasurable) hnull
  simpa only [ae_iff, Classical.not_not] using H

/-- All equality parameters of a selected pair are almost surely finite for
arbitrary weighted candidate laws, including laws with infinite first moment. -/
theorem ae_pairEqualityTimes_finite (p : Probe d) (m : Fin K → WeightedModel d)
    (q : OrderedCandidatePair K)
    (hUP : BorelProjectionNullMeasurableInput (WeightPair d × BiasPair) (ProbeParameter p)) :
    ∀ᵐ θ ∂Measure.pi (fun k => (m k).joint),
      (pairEqualityTimes p (θ q.1.1).1 (θ q.1.2).1 (θ q.1.1).2 (θ q.1.2).2).Finite := by
  filter_upwards [ae_selectedPair_not_exceptional p m q hUP,
    ae_selectedPair_no_fixed_tie m q (p.curve 0),
    ae_selectedPair_no_fixed_tie m q (p.curve p.length)] with θ hgood h0 hL
  exact pairEqualityTimes_finite p _ _ _ _ hgood h0 hL

/-- Definition 2.1 finiteness for the actual random active-switch set. -/
theorem ae_switchSet_finite (p : Probe d) (m : Fin K → WeightedModel d)
    (hUP : BorelProjectionNullMeasurableInput (WeightPair d × BiasPair) (ProbeParameter p)) :
    ∀ᵐ θ ∂Measure.pi (fun k => (m k).joint), (switchSet (scores p θ) p.length).Finite := by
  have ha : ∀ᵐ θ ∂Measure.pi (fun k => (m k).joint), ∀ q : OrderedCandidatePair K,
      (pairEqualityTimes p (θ q.1.1).1 (θ q.1.2).1 (θ q.1.1).2 (θ q.1.2).2).Finite :=
    ae_all_iff.mpr (fun q => ae_pairEqualityTimes_finite p m q hUP)
  filter_upwards [ha] with θ hθ
  rw [switchSet_eq_iUnion_pairSwitchSet]
  apply Set.finite_iUnion
  intro q
  apply (hθ q).subset
  intro s hs
  exact ⟨⟨hs.1,hs.2.1⟩,hs.2.2.1.1⟩

private def pairTuple (ab : Candidate d × Candidate d) : Fin 2 → Candidate d :=
  fun i => if i = 0 then ab.1 else ab.2

private lemma measurable_pairTuple : Measurable (pairTuple (d := d)) := by
  apply measurable_pi_iff.mpr
  intro i
  by_cases hi : i = 0
  · simpa only [pairTuple, hi, ↓reduceIte] using
      (measurable_fst : Measurable (fun ab : Candidate d × Candidate d => ab.1))
  · simpa only [pairTuple, hi, ↓reduceIte] using
      (measurable_snd : Measurable (fun ab : Candidate d × Candidate d => ab.2))

/-- The actual three independent candidate laws have no interior triple
equality. Lusin--Novikov is used only to measurably enumerate the first pair's
regular zeros; the third candidate's singleton score probability is proved zero. -/
theorem independent_triple_tie_null (p : Probe d) (mi mj mk : WeightedModel d)
    (hLN : LusinNovikovInput (Fin 2 → Candidate d) (ProbeParameter p))
    (hUP : BorelProjectionNullMeasurableInput (WeightPair d × BiasPair) (ProbeParameter p)) :
    ((mi.joint.prod mj.joint).prod mk.joint)
      {t : (Candidate d × Candidate d) × Candidate d | ∃ s ∈ Ioo 0 p.length,
        scoreValue (p.curve s) t.1.1 = scoreValue (p.curve s) t.1.2 ∧
          scoreValue (p.curve s) t.1.1 = scoreValue (p.curve s) t.2} = 0 := by
  classical
  let q : OrderedCandidatePair 2 := ⟨(0,1), by decide⟩
  obtain ⟨e⟩ := hLN (regularVisibleGraph p q) (measurableSet_regularVisibleGraph p q)
    (regularVisibleGraph_sections_countable p q)
  let s₀ : ProbeParameter p := ⟨0, le_rfl, p.length_pos.le⟩
  let en : ℕ → (Fin 2 → Candidate d) → ProbeParameter p := fun n =>
    Function.extend (Subtype.val : e.domain n → (Fin 2 → Candidate d))
      (e.value n) (fun _ => s₀)
  have hen (n : ℕ) : Measurable (en n) :=
    (MeasurableEmbedding.subtype_coe (e.measurable_domain n)).measurable_extend
      (e.measurable_value n) measurable_const
  have heneq (n : ℕ) (θ : Fin 2 → Candidate d) (hn : θ ∈ e.domain n) :
      en n θ = e.value n ⟨θ,hn⟩ :=
    Subtype.val_injective.extend_apply (e.value n) (fun _ => s₀) ⟨θ,hn⟩
  let xn : ℕ → (Candidate d × Candidate d) → Space d :=
    fun n ab => p.curve (en n (pairTuple ab))
  let yn : ℕ → (Candidate d × Candidate d) → ℝ :=
    fun n ab => scoreValue (xn n ab) ab.1
  have hxn (n : ℕ) : Measurable (xn n) :=
    (measurable_probe_curve p).comp ((hen n).comp measurable_pairTuple)
  have hyn (n : ℕ) : Measurable (yn n) := by
    exact ((measurable_fst.comp measurable_fst).inner (hxn n)).add
      (measurable_snd.comp measurable_fst)
  let E : Set (Candidate d × Candidate d) :=
    {ab | (ab.1.2,ab.2.2) ∈ exceptionalBiases p ab.1.1 ab.2.1}
  have hE : ((mi.joint.prod mj.joint).prod mk.joint)
      (E ×ˢ (univ : Set (Candidate d))) = 0 := by
    rw [Measure.prod_prod, independent_pair_exceptional_null p mi mj hUP, zero_mul]
  have havoid := independent_score_avoids_countable_heights
    (mi.joint.prod mj.joint) mk xn yn hxn hyn
  apply measure_mono_null (t := (E ×ˢ (univ : Set (Candidate d))) ∪
    {t | ∃ n, scoreValue (xn n t.1) t.2 = yn n t.1}) _ (measure_union_null hE havoid)
  rintro t ⟨s,hs,heq,hthird⟩
  by_cases ht : t.1 ∈ E
  · exact Or.inl ⟨ht, mem_univ _⟩
  have hgood : (t.1.1.2,t.1.2.2) ∉ exceptionalBiases p t.1.1.1 t.1.2.1 := ht
  have hsPair : s ∈ pairEqualityTimes p t.1.1.1 t.1.2.1 t.1.1.2 t.1.2.2 := ⟨hs,heq⟩
  obtain ⟨hdiff,htrans⟩ := pairEquality_transverse_of_not_exceptional p _ _ _ _ hgood hsPair
  have hvis : VisiblePair (scores p (pairTuple t.1)) s q := by
    refine ⟨?_, ?_⟩
    · simpa [scores, pairTuple, q, scoreValue] using heq
    · intro k hk0 hk1
      have hk0' : k ≠ (0 : Fin 2) := hk0
      have hk1' : k ≠ (1 : Fin 2) := hk1
      fin_cases k <;> contradiction
  have hreg : (pairTuple t.1, (⟨s,Ioo_subset_Icc_self hs⟩ : ProbeParameter p)) ∈
      regularVisibleGraph p q := by
    refine ⟨hs.1,hs.2,hvis,hdiff,?_⟩
    simpa [q,pairTuple] using htrans
  obtain ⟨n,hn,hns⟩ := (e.covers _ _).1 hreg
  have hsreal : (en n (pairTuple t.1) : ℝ) = s :=
    congrArg Subtype.val ((heneq n _ hn).trans hns)
  refine Or.inr ⟨n,?_⟩
  change scoreValue (p.curve (en n (pairTuple t.1))) t.2 =
    scoreValue (p.curve (en n (pairTuple t.1))) t.1.1
  rw [hsreal]
  exact hthird.symm

/-- The three selected coordinates have their actual independent candidate laws. -/
theorem map_selectedTriple (m : Fin K → WeightedModel d) (i j k : Fin K)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    (Measure.pi (fun a => (m a).joint)).map (fun θ => ((θ i,θ j),θ k)) =
      ((m i).joint.prod (m j).joint).prod (m k).joint := by
  have hind := ProbabilityTheory.iIndepFun_pi
    (μ := fun a : Fin K => (m a).joint) (X := fun _ => (id : Candidate d → Candidate d))
    (fun _ => measurable_id.aemeasurable)
  have hp := hind.indepFun_prodMk (fun a => measurable_pi_apply a) i j k hik hjk
  have H := (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
    ((measurable_pi_apply i).prodMk (measurable_pi_apply j)).aemeasurable
    (measurable_pi_apply k).aemeasurable).1 hp
  rw [map_selectedCandidates m i j hij,
    (measurePreserving_eval (fun a : Fin K => (m a).joint) k).map_eq] at H
  exact H

/-- No triple equality for any selected different candidates under the real
heterogeneous product law, with no moment assumptions on the weights. -/
theorem ae_selected_no_triple_tie (p : Probe d) (m : Fin K → WeightedModel d)
    (q : OrderedCandidatePair K) (k : Fin K) (hki : k ≠ q.1.1) (hkj : k ≠ q.1.2)
    (hLN : LusinNovikovInput (Fin 2 → Candidate d) (ProbeParameter p))
    (hUP : BorelProjectionNullMeasurableInput (WeightPair d × BiasPair) (ProbeParameter p)) :
    ∀ᵐ θ ∂Measure.pi (fun a => (m a).joint), ∀ s ∈ Ioo 0 p.length,
      ¬ (scores p θ q.1.1 s = scores p θ q.1.2 s ∧
        scores p θ q.1.1 s = scores p θ k s) := by
  have hnull := independent_triple_tie_null p (m q.1.1) (m q.1.2) (m k) hLN hUP
  rw [← map_selectedTriple m q.1.1 q.1.2 k (ne_of_lt q.2) hki.symm hkj.symm] at hnull
  have H := preimage_null_of_map_null
    ((((measurable_pi_apply q.1.1).prodMk (measurable_pi_apply q.1.2)).prodMk
      (measurable_pi_apply k)).aemeasurable) hnull
  have Hae := measure_eq_zero_iff_ae_notMem.mp H
  filter_upwards [Hae] with θ hθ s hs ht
  exact hθ ⟨s,hs,ht⟩

/-- Simultaneous endpoint exclusion, finite equality sets, and genuine
transversality for every pair of the actual sampled candidates. -/
theorem ae_all_pairs_regular (p : Probe d) (m : Fin K → WeightedModel d)
    (hUP : BorelProjectionNullMeasurableInput (WeightPair d × BiasPair) (ProbeParameter p)) :
    ∀ᵐ θ ∂Measure.pi (fun a => (m a).joint), ∀ q : OrderedCandidatePair K,
      scores p θ q.1.1 0 ≠ scores p θ q.1.2 0 ∧
      scores p θ q.1.1 p.length ≠ scores p θ q.1.2 p.length ∧
      (pairEqualityTimes p (θ q.1.1).1 (θ q.1.2).1 (θ q.1.1).2 (θ q.1.2).2).Finite ∧
      ∀ s ∈ pairEqualityTimes p (θ q.1.1).1 (θ q.1.2).1 (θ q.1.1).2 (θ q.1.2).2,
        DifferentiableAt ℝ p.curve s ∧
          inner ℝ ((θ q.1.1).1 - (θ q.1.2).1) (deriv p.curve s) ≠ 0 := by
  apply ae_all_iff.mpr
  intro q
  filter_upwards [ae_selectedPair_not_exceptional p m q hUP,
    ae_selectedPair_no_fixed_tie m q (p.curve 0),
    ae_selectedPair_no_fixed_tie m q (p.curve p.length)] with θ hgood h0 hL
  refine ⟨h0,hL,pairEqualityTimes_finite p _ _ _ _ hgood h0 hL,?_⟩
  intro s hs
  exact pairEquality_transverse_of_not_exceptional p _ _ _ _ hgood hs

/-- Simultaneous absence of all interior triple ties, not merely the absence
of a third candidate at a preselected deterministic location. -/
theorem ae_no_triple_ties (p : Probe d) (m : Fin K → WeightedModel d)
    (hLN : LusinNovikovInput (Fin 2 → Candidate d) (ProbeParameter p))
    (hUP : BorelProjectionNullMeasurableInput (WeightPair d × BiasPair) (ProbeParameter p)) :
    ∀ᵐ θ ∂Measure.pi (fun a => (m a).joint), ∀ i j k : Fin K,
      i ≠ j → i ≠ k → j ≠ k → ∀ s ∈ Ioo 0 p.length,
        ¬ (scores p θ i s = scores p θ j s ∧ scores p θ i s = scores p θ k s) := by
  have ha : ∀ᵐ θ ∂Measure.pi (fun a => (m a).joint), ∀ q : OrderedCandidatePair K,
      ∀ k : Fin K, k ≠ q.1.1 → k ≠ q.1.2 → ∀ s ∈ Ioo 0 p.length,
        ¬ (scores p θ q.1.1 s = scores p θ q.1.2 s ∧
          scores p θ q.1.1 s = scores p θ k s) := by
    apply ae_all_iff.mpr
    intro q
    apply ae_all_iff.mpr
    intro k
    by_cases hki : k = q.1.1
    · exact Filter.Eventually.of_forall fun _ h => (h hki).elim
    by_cases hkj : k = q.1.2
    · exact Filter.Eventually.of_forall fun _ _ h => (h hkj).elim
    filter_upwards [ae_selected_no_triple_tie p m q k hki hkj hLN hUP] with θ hθ
    exact fun _ _ => hθ
  filter_upwards [ha] with θ hθ i j k hij hik hjk s hs heq
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact hθ ⟨(i,j),hlt⟩ k hik.symm hjk.symm s hs heq
  · exact hθ ⟨(j,i),hgt⟩ k hjk.symm hik.symm s hs
      ⟨heq.1.symm,heq.1.symm.trans heq.2⟩

/-- At any fixed location, all distinct candidates have different scores.
This also treats zero-length paths without constructing a positive Probe. -/
theorem ae_no_fixed_ties (m : Fin K → WeightedModel d) (x : Space d) :
    ∀ᵐ θ ∂Measure.pi (fun a => (m a).joint), ∀ i j : Fin K, i ≠ j →
      scoreValue x (θ i) ≠ scoreValue x (θ j) := by
  have ha : ∀ᵐ θ ∂Measure.pi (fun a => (m a).joint), ∀ q : OrderedCandidatePair K,
      scoreValue x (θ q.1.1) ≠ scoreValue x (θ q.1.2) :=
    ae_all_iff.mpr (fun q => ae_selectedPair_no_fixed_tie m q x)
  filter_upwards [ha] with θ hθ i j hij
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact hθ ⟨(i,j),hlt⟩
  · exact (hθ ⟨(j,i),hgt⟩).symm

/-- Closed-interval version, combining the actual endpoint exclusions with
the interior triple-null theorem. It is suitable for monotone arclength
factorizations whose image includes both endpoints. -/
theorem ae_no_triple_ties_closed (p : Probe d) (m : Fin K → WeightedModel d)
    (hLN : LusinNovikovInput (Fin 2 → Candidate d) (ProbeParameter p))
    (hUP : BorelProjectionNullMeasurableInput (WeightPair d × BiasPair) (ProbeParameter p)) :
    ∀ᵐ θ ∂Measure.pi (fun a => (m a).joint), ∀ i j k : Fin K,
      i ≠ j → i ≠ k → j ≠ k → ∀ s ∈ Icc 0 p.length,
        ¬ (scores p θ i s = scores p θ j s ∧ scores p θ i s = scores p θ k s) := by
  filter_upwards [ae_no_triple_ties p m hLN hUP,
    ae_no_fixed_ties m (p.curve 0), ae_no_fixed_ties m (p.curve p.length)] with θ hθ h0 hL
  intro i j k hij hik hjk s hs heq
  by_cases hs0 : s = 0
  · subst s
    exact h0 i j hij heq.1
  by_cases hsL : s = p.length
  · subst s
    exact hL i j hij heq.1
  exact hθ i j k hij hik hjk s
    ⟨lt_of_le_of_ne hs.1 (Ne.symm hs0), lt_of_le_of_ne hs.2 hsL⟩ heq

end Paper35.Source.CrossingRegularity
