import Paper35.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Topology.Order.LeftRightNhds

/-!
# Deterministic visible-crossing decomposition

This file proves the pathwise counting interface used in the last step of
Lemma 3.1. It does not assert the stochastic area formula (3.5). In particular,
the general multiplicity area formula and the almost-sure exclusion of
nontransverse or triple equalities are not hypotheses disguised as a proof of
that formula.
-/
noncomputable section
open Set MeasureTheory
open scoped ENNReal Topology

namespace Paper35

/-- A differentiable zero with strictly positive derivative has the two strict
signs required by Definition 2.1. -/
lemma signChanges_of_hasDerivAt_pos {g : ℝ → ℝ} {s a : ℝ}
    (hg : HasDerivAt g a s) (hzero : g s = 0) (ha : 0 < a) :
    SignChanges g s := by
  have hpos : {t | 0 < slope g s t} ∈ 𝓝[≠] s :=
    (tendsto_order.mp (hasDerivAt_iff_tendsto_slope.mp hg)).1 0 ha
  rcases Metric.mem_nhdsWithin_iff.mp hpos with ⟨δ, hδ, hball⟩
  refine ⟨δ, hδ, Or.inl ⟨?_, ?_⟩⟩
  · intro t ht
    have htball : t ∈ Metric.ball s δ := by
      rw [Metric.mem_ball, Real.dist_eq]
      apply abs_lt.mpr
      constructor <;> linarith [ht.1, ht.2]
    have hts : t ≠ s := ne_of_lt ht.2
    have hslope : 0 < slope g s t := hball ⟨htball, hts⟩
    have heq : slope g s t * (t - s) = g t := by
      rw [slope_def_field, hzero, sub_zero,
        div_mul_cancel₀ _ (sub_ne_zero.mpr hts)]
    have hneg := mul_neg_of_pos_of_neg hslope (sub_neg.mpr ht.2)
    rwa [heq] at hneg
  · intro t ht
    have htball : t ∈ Metric.ball s δ := by
      rw [Metric.mem_ball, Real.dist_eq]
      apply abs_lt.mpr
      constructor <;> linarith [ht.1, ht.2]
    have hts : t ≠ s := ne_of_gt ht.1
    have hslope : 0 < slope g s t := hball ⟨htball, hts⟩
    have heq : slope g s t * (t - s) = g t := by
      rw [slope_def_field, hzero, sub_zero,
        div_mul_cancel₀ _ (sub_ne_zero.mpr hts)]
    have hpos' := mul_pos hslope (sub_pos.mpr ht.1)
    rwa [heq] at hpos'

/-- The local transversality implication used in the proof of Lemma 3.1.
This does not assume monotonicity in a neighborhood. -/
theorem signChanges_of_hasDerivAt_ne_zero {g : ℝ → ℝ} {s a : ℝ}
    (hg : HasDerivAt g a s) (hzero : g s = 0) (ha : a ≠ 0) :
    SignChanges g s := by
  rcases lt_or_gt_of_ne ha with hneg | hpos
  · have hn : SignChanges (fun t => -g t) s :=
      signChanges_of_hasDerivAt_pos hg.neg (by simp [hzero]) (neg_pos.mpr hneg)
    exact signChanges_neg.mp hn
  · exact signChanges_of_hasDerivAt_pos hg hzero hpos

/-- Each unordered candidate pair is represented once, in increasing order. -/
abbrev OrderedCandidatePair (K : ℕ) := {p : Fin K × Fin K // p.1 < p.2}

/-- Exactly the members of the indicated pair attain the common maximum. -/
def VisiblePair {K : ℕ} (f : Fin K → ℝ → ℝ) (s : ℝ)
    (p : OrderedCandidatePair K) : Prop :=
  f p.1.1 s = f p.1.2 s ∧
    ∀ k, k ≠ p.1.1 → k ≠ p.1.2 → f k s < f p.1.1 s

/-- Visible crossings, with sign change and the original parameter multiplicity. -/
def pairSwitchSet {K : ℕ} (f : Fin K → ℝ → ℝ) (L : ℝ)
    (p : OrderedCandidatePair K) : Set ℝ :=
  {s | 0 < s ∧ s < L ∧ VisiblePair f s p ∧
    SignChanges (fun t => f p.1.1 t - f p.1.2 t) s}

/-- A visible transverse equality is an active switch in Definition 2.1. -/
theorem activeSwitch_of_visiblePair_transverse {K : ℕ}
    {f : Fin K → ℝ → ℝ} {L s ai aj : ℝ} {p : OrderedCandidatePair K}
    (hs0 : 0 < s) (hsL : s < L) (hvis : VisiblePair f s p)
    (hi : HasDerivAt (f p.1.1) ai s) (hj : HasDerivAt (f p.1.2) aj s)
    (htrans : ai ≠ aj) : ActiveSwitch f L s := by
  refine ⟨hs0, hsL, p.1.1, p.1.2, ne_of_lt p.2, hvis.1, hvis.2, ?_⟩
  exact signChanges_of_hasDerivAt_ne_zero (hi.sub hj)
    (sub_eq_zero.mpr hvis.1) (sub_ne_zero.mpr htrans)

/-- The corresponding visible-pair set contains the transverse equality. -/
theorem mem_pairSwitchSet_of_visiblePair_transverse {K : ℕ}
    {f : Fin K → ℝ → ℝ} {L s ai aj : ℝ} {p : OrderedCandidatePair K}
    (hs0 : 0 < s) (hsL : s < L) (hvis : VisiblePair f s p)
    (hi : HasDerivAt (f p.1.1) ai s) (hj : HasDerivAt (f p.1.2) aj s)
    (htrans : ai ≠ aj) : s ∈ pairSwitchSet f L p :=
  ⟨hs0, hsL, hvis, signChanges_of_hasDerivAt_ne_zero (hi.sub hj)
    (sub_eq_zero.mpr hvis.1) (sub_ne_zero.mpr htrans)⟩

/-- The bias-pair map (3.8), expressed in terms of two projected path scores. -/
def crossingBiasMap (Si Sj : ℝ → ℝ) (z : ℝ × ℝ) : ℝ × ℝ :=
  (z.2 - Si z.1, z.2 - Sj z.1)

/-- Its fibers are precisely the common-height equalities for the two biases.
The parameter itself is retained, including on retraced portions of a path. -/
theorem crossingBiasMap_fiber_iff (Si Sj : ℝ → ℝ) (s y bi bj : ℝ) :
    crossingBiasMap Si Sj (s, y) = (bi, bj) ↔
      Si s + bi = y ∧ Sj s + bj = y := by
  simp only [crossingBiasMap, Prod.mk.injEq]
  constructor
  · rintro ⟨hi, hj⟩
    constructor <;> linarith
  · rintro ⟨hi, hj⟩
    constructor <;> linarith

/-- The map can identify parameters exactly when the projected candidate
difference does. This isolates why an injective-only change-of-variables theorem
does not supply the multiplicity formula for general rectifiable probes. -/
theorem crossingBiasMap_injOn_of_difference_injOn (Si Sj : ℝ → ℝ) (D : Set ℝ)
    (h : Set.InjOn (fun s => Si s - Sj s) D) :
    Set.InjOn (crossingBiasMap Si Sj) (D ×ˢ (Set.univ : Set ℝ)) := by
  rintro ⟨s, y⟩ hs ⟨t, z⟩ ht heq
  have hi : y - Si s = z - Si t := congrArg Prod.fst heq
  have hj : y - Sj s = z - Sj t := congrArg Prod.snd heq
  have hst : s = t := h hs.1 ht.1 (by linarith)
  subst t
  have hyz : y = z := by linarith
  subst z
  rfl

theorem crossingBiasMap_injOn_iff (Si Sj : ℝ → ℝ) (D : Set ℝ) :
    Set.InjOn (crossingBiasMap Si Sj) (D ×ˢ (Set.univ : Set ℝ)) ↔
      Set.InjOn (fun s => Si s - Sj s) D := by
  constructor
  · intro h s hs t ht heq
    have hmap : crossingBiasMap Si Sj (s, Si s) =
        crossingBiasMap Si Sj (t, Si t) := by
      simp only [crossingBiasMap, sub_self, Prod.mk.injEq, true_and]
      exact heq
    exact congrArg Prod.fst (h ⟨hs, Set.mem_univ _⟩ ⟨ht, Set.mem_univ _⟩ hmap)
  · exact crossingBiasMap_injOn_of_difference_injOn Si Sj D

lemma visiblePair_maximum {K : ℕ} {f : Fin K → ℝ → ℝ} {s : ℝ}
    {p : OrderedCandidatePair K} (hp : VisiblePair f s p) (k : Fin K) :
    f k s ≤ f p.1.1 s := by
  by_cases hki : k = p.1.1
  · subst k
    exact le_rfl
  by_cases hkj : k = p.1.2
  · subst k
    exact hp.1.ge
  exact (hp.2 k hki hkj).le

/-- Strict visibility forces uniqueness of the ordered pair at a parameter. -/
lemma visiblePair_unique {K : ℕ} {f : Fin K → ℝ → ℝ} {s : ℝ}
    {p q : OrderedCandidatePair K} (hp : VisiblePair f s p)
    (hq : VisiblePair f s q) : p = q := by
  have heq : f q.1.1 s = f p.1.1 s :=
    le_antisymm (visiblePair_maximum hp _) (visiblePair_maximum hq _)
  have hleft : q.1.1 = p.1.1 ∨ q.1.1 = p.1.2 := by
    by_contra! h
    have hlt := hp.2 q.1.1 h.1 h.2
    rw [heq] at hlt
    exact (lt_irrefl _ hlt)
  have hright : q.1.2 = p.1.1 ∨ q.1.2 = p.1.2 := by
    by_contra! h
    have hlt := hp.2 q.1.2 h.1 h.2
    rw [← hq.1, heq] at hlt
    exact (lt_irrefl _ hlt)
  rcases hleft with hl | hl <;> rcases hright with hr | hr
  · have hne := ne_of_lt q.2
    exact False.elim (hne (hl.trans hr.symm))
  · apply Subtype.ext
    exact Prod.ext hl.symm hr.symm
  · have hlt := q.2
    rw [hl, hr] at hlt
    exact False.elim (lt_asymm p.2 hlt)
  · have hne := ne_of_lt q.2
    exact False.elim (hne (hl.trans hr.symm))

lemma pairSwitchSet_subset_switchSet {K : ℕ} (f : Fin K → ℝ → ℝ) (L : ℝ)
    (p : OrderedCandidatePair K) : pairSwitchSet f L p ⊆ switchSet f L := by
  rintro s ⟨hs0, hsL, hvis, hsign⟩
  exact ⟨hs0, hsL, p.1.1, p.1.2, ne_of_lt p.2, hvis.1, hvis.2, hsign⟩

/-- Every active switch belongs to a visible pair, with no regularity assumptions. -/
theorem switchSet_eq_iUnion_pairSwitchSet {K : ℕ} (f : Fin K → ℝ → ℝ)
    (L : ℝ) : switchSet f L = ⋃ p : OrderedCandidatePair K, pairSwitchSet f L p := by
  ext s
  constructor
  · rintro ⟨hs0, hsL, i, j, hij, heq, hvis, hsign⟩
    rcases lt_or_gt_of_ne hij with hlt | hlt
    · exact mem_iUnion.mpr ⟨⟨(i, j), hlt⟩, hs0, hsL, ⟨heq, hvis⟩, hsign⟩
    · refine mem_iUnion.mpr ⟨⟨(j, i), hlt⟩, hs0, hsL, ⟨heq.symm, ?_⟩, ?_⟩
      · intro k hkj hki
        simpa [← heq] using hvis k hki hkj
      · have heqfun : (fun t => f j t - f i t) =
            (fun t => -(f i t - f j t)) := by
          funext t
          ring
        rw [heqfun]
        exact signChanges_neg.mpr hsign
  · intro hs
    rcases mem_iUnion.mp hs with ⟨p, hp⟩
    exact pairSwitchSet_subset_switchSet f L p hp

lemma pairSwitchSet_pairwiseDisjoint {K : ℕ} (f : Fin K → ℝ → ℝ) (L : ℝ) :
    Pairwise (fun p q : OrderedCandidatePair K =>
      Disjoint (pairSwitchSet f L p) (pairSwitchSet f L q)) := by
  intro p q hpq
  apply Set.disjoint_left.mpr
  intro s hp hq
  exact hpq (visiblePair_unique hp.2.2.1 hq.2.2.1)

/-- The strict sign condition makes crossings isolated within each pair's
equality set. Thus the pathwise switch sets are countable without any
differentiability or probabilistic assumptions. -/
theorem pairSwitchSet_countable {K : ℕ} (f : Fin K → ℝ → ℝ) (L : ℝ)
    (p : OrderedCandidatePair K) : (pairSwitchSet f L p).Countable := by
  apply (countable_setOf_isolated_right_within (s := pairSwitchSet f L p)).mono
  intro s hs
  refine ⟨hs, ?_⟩
  apply Filter.empty_mem_iff_bot.mp
  rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
  rcases hs.2.2.2 with ⟨δ, hδ, hsign⟩
  refine ⟨Ioo (s - δ) (s + δ), Ioo_mem_nhds (by linarith) (by linarith), ?_⟩
  rintro t ⟨htN, htS, hts⟩
  have htr : t ∈ Ioo s (s + δ) := ⟨hts, htN.2⟩
  have heq : f p.1.1 t = f p.1.2 t := htS.2.2.1.1
  rcases hsign with ⟨_, hr⟩ | ⟨_, hr⟩
  · have hpos : 0 < f p.1.1 t - f p.1.2 t := hr t htr
    rw [heq, sub_self] at hpos
    exact lt_irrefl _ hpos
  · have hneg : f p.1.1 t - f p.1.2 t < 0 := hr t htr
    rw [heq, sub_self] at hneg
    exact lt_irrefl _ hneg

theorem switchSet_countable {K : ℕ} (f : Fin K → ℝ → ℝ) (L : ℝ) :
    (switchSet f L).Countable := by
  rw [switchSet_eq_iUnion_pairSwitchSet]
  exact Set.countable_iUnion (pairSwitchSet_countable f L)

theorem measurableSet_pairSwitchSet {K : ℕ} (f : Fin K → ℝ → ℝ) (L : ℝ)
    (p : OrderedCandidatePair K) : MeasurableSet (pairSwitchSet f L p) :=
  (pairSwitchSet_countable f L p).measurableSet

theorem measurableSet_switchSet {K : ℕ} (f : Fin K → ℝ → ℝ) (L : ℝ) :
    MeasurableSet (switchSet f L) := (switchSet_countable f L).measurableSet

/-- The full pathwise count is the sum of visible-pair counts, also when infinite.
No assertion about expected counts or density integrals is used in the proof. -/
theorem switchCount_eq_sum_pairSwitchSet {K : ℕ} (f : Fin K → ℝ → ℝ)
    (L : ℝ) : switchCount f L =
      ∑ p : OrderedCandidatePair K, ((pairSwitchSet f L p).encard : ℝ≥0∞) := by
  classical
  unfold switchCount
  rw [switchSet_eq_iUnion_pairSwitchSet]
  rw [Set.encard_iUnion_of_finite (pairSwitchSet_pairwiseDisjoint f L)]
  rw [finsum_eq_sum_of_fintype]
  exact map_sum ENat.toENNRealRingHom _ _

/-- Finiteness can be checked pair by pair, retaining repeated parameter visits. -/
theorem switchSet_finite_iff_pairSwitchSet_finite {K : ℕ}
    (f : Fin K → ℝ → ℝ) (L : ℝ) :
    (switchSet f L).Finite ↔ ∀ p : OrderedCandidatePair K, (pairSwitchSet f L p).Finite := by
  constructor
  · intro h p
    exact h.subset (pairSwitchSet_subset_switchSet f L p)
  · intro h
    rw [switchSet_eq_iUnion_pairSwitchSet]
    exact Set.finite_iUnion h

/-- In the degeneracy argument of Lemma 3.1, finiteness of all pair-equality
sets suffices for finiteness of the actual active-switch set. -/
theorem switchSet_finite_of_pair_equalities_finite {K : ℕ}
    (f : Fin K → ℝ → ℝ) (L : ℝ)
    (hfin : ∀ p : OrderedCandidatePair K,
      {s : ℝ | s ∈ Ioo 0 L ∧ f p.1.1 s = f p.1.2 s}.Finite) :
    (switchSet f L).Finite := by
  apply (switchSet_finite_iff_pairSwitchSet_finite f L).mpr
  intro p
  apply (hfin p).subset
  intro s hs
  exact ⟨⟨hs.1, hs.2.1⟩, hs.2.2.1.1⟩

/-- Tonelli's finite-sum step for the actual visible-pair counting variables.
The displayed measurability premise concerns only these variables; it is not
an assumption of the crossing-density identity. -/
theorem expectedSwitchCount_eq_sum_pairSwitchSet {Ω : Type*} [MeasurableSpace Ω]
    {K : ℕ} (μ : Measure Ω) (f : Ω → Fin K → ℝ → ℝ) (L : ℝ)
    (hmeas : ∀ p : OrderedCandidatePair K,
      AEMeasurable (fun ω => ((pairSwitchSet (f ω) L p).encard : ℝ≥0∞)) μ) :
    expectedSwitchCount μ f L = ∑ p : OrderedCandidatePair K,
      ∫⁻ ω, ((pairSwitchSet (f ω) L p).encard : ℝ≥0∞) ∂μ := by
  classical
  unfold expectedSwitchCount
  simp_rw [switchCount_eq_sum_pairSwitchSet]
  exact lintegral_finset_sum' Finset.univ (fun p _ => hmeas p)

end Paper35
