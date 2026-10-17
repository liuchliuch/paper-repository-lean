import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Combinatorics.Enumerative.Partition
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.List
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-!
# The completed-gap envelope

The elementary multinomial facts are stated for a finite alphabet of gap
lengths. `gapEnvelope` is (B.2), including its empty-sample convention.
-/

noncomputable section
open scoped BigOperators
namespace Paper37.Envelope

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Number of completed gaps. -/
def gapCount (c : α → ℕ) : ℕ := ∑ a, c a

/-- The empirical completed-gap likelihood, with `0^0 = 1`. -/
def gapEnvelope (c : α → ℕ) : ℝ :=
  ∏ a, ((c a : ℝ) / gapCount c) ^ c a

lemma gapCount_zero_iff (c : α → ℕ) : gapCount c = 0 ↔ ∀ a, c a = 0 := by
  simp [gapCount, Finset.sum_eq_zero_iff]

lemma gapEnvelope_pos (c : α → ℕ) : 0 < gapEnvelope c := by
  unfold gapEnvelope
  apply Finset.prod_pos
  intro a ha
  by_cases h : c a = 0
  · simp [h]
  · have hK : 0 < gapCount c := by
      have := Finset.single_le_sum (f := c) (fun i hi => Nat.zero_le (c i)) (Finset.mem_univ a)
      exact lt_of_lt_of_le (Nat.pos_of_ne_zero h) this
    exact pow_pos (div_pos (by exact_mod_cast Nat.pos_of_ne_zero h) (by exact_mod_cast hK)) _

lemma empirical_sum (c : α → ℕ) (hK : gapCount c ≠ 0) :
    ∑ a, ((c a : ℝ) / gapCount c) = 1 := by
  simp_rw [div_eq_mul_inv]
  rw [← Finset.sum_mul]
  have hcast : (∑ a, (c a : ℝ)) = (gapCount c : ℝ) := by simp [gapCount]
  rw [hcast, mul_inv_cancel₀ (by exact_mod_cast hK)]

/-- One multinomial point probability is at most one. This is the precise
inequality used to bound the contribution of one completed-gap count vector. -/
theorem multinomial_gap_mass_le_one (c : α → ℕ) :
    (Nat.multinomial Finset.univ c : ℝ) * gapEnvelope c ≤ 1 := by
  by_cases hK : gapCount c = 0
  · have hc := (gapCount_zero_iff c).mp hK
    simp [gapEnvelope, Nat.multinomial, gapCount, hc]
  · have hmem : c ∈ Finset.piAntidiag Finset.univ (gapCount c) := by
      simp [Finset.mem_piAntidiag, gapCount]
    have hsum := Finset.sum_pow_eq_sum_piAntidiag Finset.univ
      (fun a => (c a : ℝ) / gapCount c) (gapCount c)
    rw [empirical_sum c hK, one_pow] at hsum
    rw [hsum]
    unfold gapEnvelope
    exact Finset.single_le_sum (f := fun d =>
      (Nat.multinomial Finset.univ d : ℝ) * ∏ a, ((c a : ℝ) / gapCount c) ^ d a)
      (fun d hd => by positivity) hmem

/-- Zero counts give the all-zero word's envelope value. -/
@[simp] theorem gapEnvelope_zero : gapEnvelope (fun _ : α => 0) = 1 := by
  simp [gapEnvelope]

/-- The multinomial likelihood is maximized by its empirical distribution.
The candidate `μ` may be a subprobability, as occurs when one truncates a law
on positive integers to the gap lengths visible at a finite horizon. -/
theorem likelihood_le_gapEnvelope (c : α → ℕ) (μ : α → ℝ)
    (hμ : ∀ a, 0 ≤ μ a) (hμsum : ∑ a, μ a ≤ 1) :
    ∏ a, μ a ^ c a ≤ gapEnvelope c := by
  by_cases hK : gapCount c = 0
  · have hc := (gapCount_zero_iff c).mp hK
    simp [hc, gapEnvelope]
  by_cases hz : ∃ a, c a ≠ 0 ∧ μ a = 0
  · obtain ⟨a, hca, hma⟩ := hz
    rw [Finset.prod_eq_zero (Finset.mem_univ a) (by simp [hma, hca])]
    exact (gapEnvelope_pos c).le
  have hKpos : 0 < (gapCount c : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hK
  have hmupos : ∀ a, c a ≠ 0 → 0 < μ a := by
    intro a ha
    exact lt_of_le_of_ne (hμ a) (Ne.symm (fun hm => hz ⟨a, ha, hm⟩))
  let e : α → ℝ := fun a => (c a : ℝ) / gapCount c
  have hepos : ∀ a, c a ≠ 0 → 0 < e a := by
    intro a ha
    exact div_pos (by exact_mod_cast Nat.pos_of_ne_zero ha) hKpos
  have hlog : ∀ a, (c a : ℝ) * (Real.log (μ a) - Real.log (e a)) ≤
      (gapCount c : ℝ) * μ a - c a := by
    intro a
    by_cases ha : c a = 0
    · simpa [ha] using mul_nonneg hKpos.le (hμ a)
    have hcp : 0 < (c a : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero ha
    have he := hepos a ha
    have hm := hmupos a ha
    have hh := mul_le_mul_of_nonneg_left
      (Real.log_le_sub_one_of_pos (div_pos hm he)) hcp.le
    rw [Real.log_div hm.ne' he.ne'] at hh
    have halg : (c a : ℝ) * (μ a / e a - 1) =
        (gapCount c : ℝ) * μ a - c a := by
      dsimp [e]
      field_simp
    rwa [halg] at hh
  have hsum : ∑ a, (c a : ℝ) * (Real.log (μ a) - Real.log (e a)) ≤ 0 := by
    calc
      _ ≤ ∑ a, ((gapCount c : ℝ) * μ a - c a) := Finset.sum_le_sum (fun a ha => hlog a)
      _ = (gapCount c : ℝ) * (∑ a, μ a) - gapCount c := by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
        simp [gapCount]
      _ ≤ 0 := by nlinarith
  have hp : 0 < ∏ a, μ a ^ c a := by
    apply Finset.prod_pos
    intro a ha
    by_cases hc : c a = 0
    · simp [hc]
    · exact pow_pos (hmupos a hc) _
  apply (Real.log_le_log_iff hp (gapEnvelope_pos c)).mp
  rw [Real.log_prod Finset.univ _ (fun a ha => by
    by_cases hc : c a = 0
    · simp [hc]
    · exact (pow_pos (hmupos a hc) _).ne')]
  unfold gapEnvelope
  rw [Real.log_prod Finset.univ _ (fun a ha => by
    by_cases hc : c a = 0
    · simp [hc]
    · exact (pow_pos (hepos a hc) _).ne')]
  simp only [Real.log_pow]
  have hexp : ∑ a, (c a : ℝ) * (Real.log (μ a) - Real.log (e a)) =
      (∑ a, (c a : ℝ) * Real.log (μ a)) - ∑ a, (c a : ℝ) * Real.log (e a) := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib]
  rw [hexp] at hsum
  exact sub_nonpos.mp hsum

/-- Ordered gaps with a specified histogram. Each entry is an actual gap
symbol; the type does not identify distinct orderings. -/
def Ordering (c : α → ℕ) :=
  {f : Fin (gapCount c) → α // ∀ a, (List.ofFn f).count a = c a}

instance (c : α → ℕ) : Fintype (Ordering c) := inferInstanceAs (Fintype {f : Fin (gapCount c) → α // _})

lemma ordered_product_eq (c : α → ℕ) (f : Ordering c) (μ : α → ℝ) :
    (∏ i, μ (f.val i)) = ∏ a, μ a ^ c a := by
  have h := Finset.prod_multiset_map_count (List.ofFn f.val : Multiset α) μ
  have hsup : ∏ a ∈ (List.ofFn f.val : Multiset α).toFinset,
      μ a ^ (List.ofFn f.val : Multiset α).count a =
      ∏ a, μ a ^ (List.ofFn f.val : Multiset α).count a := by
    apply Finset.prod_subset (Finset.subset_univ _)
    intro a ha hnot
    simp only [Multiset.mem_toFinset] at hnot
    rw [Multiset.count_eq_zero_of_notMem hnot, pow_zero]
  rw [hsup] at h
  simpa [List.map_ofFn, List.prod_ofFn, f.prop] using h

/-- All orderings of one histogram have total empirical likelihood at most one.
Unlike a bare multinomial coefficient formula, this theorem sums over actual
ordered tuples. -/
theorem ordering_mass_le_one (c : α → ℕ) :
    ∑ _f : Ordering c, gapEnvelope c ≤ 1 := by
  let e : α → ℝ := fun a => (c a : ℝ) / gapCount c
  have htotal : (∑ f : Fin (gapCount c) → α, ∏ i, e (f i)) = 1 := by
    have h := Finset.sum_pow' (Finset.univ : Finset α) e (gapCount c)
    simp only [Fintype.piFinset_univ] at h
    rw [← h]
    by_cases hK : gapCount c = 0
    · simp [hK]
    · rw [empirical_sum c hK, one_pow]
  calc
    _ = ∑ f : Ordering c, ∏ i, e (f.val i) := by
      apply Finset.sum_congr rfl
      intro f hf
      exact (ordered_product_eq c f e).symm
    _ ≤ ∑ f : Fin (gapCount c) → α, ∏ i, e (f i) := by
      change (∑ f : {f : Fin (gapCount c) → α // ∀ a, (List.ofFn f).count a = c a},
        ∏ i, e (f.val i)) ≤ _
      rw [← Finset.sum_subtype (Finset.univ.filter (fun f : Fin (gapCount c) → α =>
        ∀ a, (List.ofFn f).count a = c a)) (by simp) (fun f => ∏ i, e (f i))]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun f hf hn => Finset.prod_nonneg (fun i hi => by dsimp [e]; positivity))
    _ = 1 := htotal

/-- Histogram of positive integer gaps of size at most `L`. -/
def FeasibleCounts (L : ℕ) :=
  {c : Fin L → Fin (L+1) // ∑ i, (i.val+1) * (c i).val ≤ L}

instance (L : ℕ) : Fintype (FeasibleCounts L) := inferInstanceAs (Fintype {c : Fin L → Fin (L+1) // _})

/-- Ordinary length-`L` blocks described by their completed ordered gaps. The
remaining `L - ∑ d` symbols are the unique terminal zero run. -/
def Block (L : ℕ) := Σ c : FeasibleCounts L, Ordering (fun i => (c.val i).val)

instance (L : ℕ) : Fintype (Block L) := inferInstanceAs (Fintype (Σ c : FeasibleCounts L, _))

/-- B.2 as a function of an actual ordered completed-gap block. -/
def M {L : ℕ} (b : Block L) : ℝ := gapEnvelope (fun i => (b.1.val i).val)

/-- B.4: the finite sum over completed-gap blocks. -/
def Z (L : ℕ) : ℝ := ∑ b : Block L, M b

lemma M_pos {L : ℕ} (b : Block L) : 0 < M b := gapEnvelope_pos _

/-- Before identifying histograms with integer partitions, the normalization
is bounded by the number of feasible completed-gap histograms. -/
theorem Z_le_histogram_card (L : ℕ) : Z L ≤ Fintype.card (FeasibleCounts L) := by
  unfold Z
  change (∑ b : Σ c : FeasibleCounts L, Ordering (fun i => (c.val i).val), M b) ≤ _
  rw [Fintype.sum_sigma]
  calc
    _ ≤ ∑ _c : FeasibleCounts L, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro c hc
      exact ordering_mass_le_one _
    _ = _ := by simp

/-- The multiset partition encoded by a feasible histogram. -/
def histogramParts {L : ℕ} (c : FeasibleCounts L) : Multiset ℕ :=
  ∑ i, Multiset.replicate (c.val i).val (i.val + 1)

lemma histogramParts_sum {L : ℕ} (c : FeasibleCounts L) :
    (histogramParts c).sum = ∑ i, (i.val + 1) * (c.val i).val := by
  change Multiset.sumAddMonoidHom (∑ i, _) = _
  rw [map_sum]
  simp [Multiset.sumAddMonoidHom, mul_comm]

lemma histogramParts_pos {L : ℕ} (c : FeasibleCounts L) {d : ℕ}
    (hd : d ∈ histogramParts c) : 0 < d := by
  obtain ⟨i, hi, hm⟩ := Multiset.mem_sum.mp hd
  have heq := (Multiset.mem_replicate.mp hm).2
  omega

lemma histogramParts_count {L : ℕ} (c : FeasibleCounts L) (i : Fin L) :
    (histogramParts c).count (i.val + 1) = (c.val i).val := by
  unfold histogramParts
  rw [Multiset.count_sum']
  rw [Finset.sum_eq_single i]
  · simp
  · intro j hj hji
    have hne : i.val + 1 ≠ j.val + 1 := by
      intro hh
      exact hji (Fin.ext (Nat.add_right_cancel hh.symm))
    simp [Multiset.count_replicate]
    exact fun hh => False.elim (hji (Fin.ext hh))
  · simp

/-- A feasible histogram yields an ordinary integer partition of its total
completed-gap length. -/
def histogramPartition {L : ℕ} (c : FeasibleCounts L) :
    Σ s : Fin (L+1), Nat.Partition s.val :=
  ⟨⟨∑ i, (i.val + 1) * (c.val i).val, Nat.lt_succ_of_le c.prop⟩,
    ⟨histogramParts c, fun hd => histogramParts_pos c hd, histogramParts_sum c⟩⟩

lemma histogramPartition_injective (L : ℕ) :
    Function.Injective (@histogramPartition L) := by
  intro c d heq
  have hp := congrArg (fun t : Σ s : Fin (L+1), Nat.Partition s.val => t.2.parts) heq
  apply Subtype.ext
  funext i
  apply Fin.ext
  have hc := histogramParts_count c i
  have hd := histogramParts_count d i
  change histogramParts c = histogramParts d at hp
  rw [hp] at hc
  exact hc.symm.trans hd

/-- The cumulative ordinary integer-partition count in B.5. -/
def cumulativePartitions (L : ℕ) : ℕ := ∑ s : Fin (L+1), Fintype.card (Nat.Partition s.val)

lemma histogram_card_le_cumulativePartitions (L : ℕ) :
    Fintype.card (FeasibleCounts L) ≤ cumulativePartitions L := by
  have h := Fintype.card_le_of_injective (@histogramPartition L) (histogramPartition_injective L)
  simpa [Fintype.card_sigma, cumulativePartitions] using h

/-- The combinatorial inequality of Lemma B.1: summing over actual ordered
completed gaps costs at most one unit for each integer partition. -/
theorem Z_le_cumulativePartitions (L : ℕ) : Z L ≤ cumulativePartitions L := by
  exact (Z_le_histogram_card L).trans (by exact_mod_cast histogram_card_le_cumulativePartitions L)

/-- The histogram of the all-zero ordinary block. -/
def zeroCounts (L : ℕ) : FeasibleCounts L := ⟨fun _ => 0, by simp⟩

/-- The all-zero word has no completed gaps. -/
def zeroBlock (L : ℕ) : Block L := by
  refine ⟨zeroCounts L, ?_⟩
  change Ordering (fun _ : Fin L => 0)
  unfold Ordering
  have hK : gapCount (fun _ : Fin L => 0) = 0 := by simp [gapCount]
  rw [hK]
  exact ⟨Fin.elim0, by simp⟩

@[simp] lemma M_zeroBlock (L : ℕ) : M (zeroBlock L) = 1 := by
  exact gapEnvelope_zero

lemma one_le_Z (L : ℕ) : 1 ≤ Z L := by
  have h := Finset.single_le_sum (f := fun b : Block L => M b)
    (fun b hb => (M_pos b).le) (Finset.mem_univ (zeroBlock L))
  simpa [Z] using h

lemma Z_pos (L : ℕ) : 0 < Z L := lt_of_lt_of_le zero_lt_one (one_le_Z L)

/-- The normalized ordinary-renewal assignment B.4. -/
def q {L : ℕ} (b : Block L) : ℝ := M b / Z L

lemma q_pos {L : ℕ} (b : Block L) : 0 < q b := div_pos (M_pos b) (Z_pos L)

lemma q_sum (L : ℕ) : ∑ b : Block L, q b = 1 := by
  simp only [q, div_eq_mul_inv]
  rw [← Finset.sum_mul]
  exact mul_inv_cancel₀ (Z_pos L).ne'

/-- The exact first-renewal mixture sample space: no renewal, or first
renewal at `j+1` followed by an ordinary suffix of length `N-(j+1)`. -/
def StationaryBlock (N : ℕ) := Option (Σ j : Fin N, Block (N - (j.val+1)))

instance (N : ℕ) : Fintype (StationaryBlock N) :=
  inferInstanceAs (Fintype (Option (Σ j : Fin N, Block (N - (j.val+1)))))

/-- The uniform first-renewal assignment B.7. -/
def Q {N : ℕ} (b : StationaryBlock N) : ℝ :=
  match b with
  | none => 1 / (N+1 : ℝ)
  | some ⟨_, y⟩ => q y / (N+1 : ℝ)

lemma Q_pos {N : ℕ} (b : StationaryBlock N) : 0 < Q b := by
  cases b with
  | none => exact div_pos zero_lt_one (by positivity)
  | some b => exact div_pos (q_pos b.2) (by positivity)

/-- The uniform first-renewal mixture is a normalized full-support assignment. -/
theorem Q_sum (N : ℕ) : ∑ b : StationaryBlock N, Q b = 1 := by
  change (∑ b : Option (Σ j : Fin N, Block (N - (j.val+1))), Q b) = 1
  rw [Fintype.sum_option, Fintype.sum_sigma]
  simp only [Q, div_eq_mul_inv]
  simp_rw [← Finset.sum_mul, q_sum]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hN : (N+1 : ℝ) ≠ 0 := by positivity
  field_simp
  ring

/-- A direct multiplicative regret statement. Boundary probabilities can be
applied to this theorem after the ordinary completed-gap likelihood bound. -/
theorem Q_ratio_le_local {N : ℕ} (j : Fin N)
    (b : Block (N - (j.val+1))) (p : ℝ) (hp : p ≤ M b) :
    p / Q (some ⟨j,b⟩) ≤ (N+1 : ℝ) * Z (N - (j.val+1)) := by
  have hN : 0 < (N+1 : ℝ) := by positivity
  have hq : 0 < Q (some ⟨j,b⟩ : StationaryBlock N) := Q_pos _
  apply (div_le_iff₀ hq).mpr
  have hm := (M_pos b).ne'
  have hz := (Z_pos (N-(j.val+1))).ne'
  have hid : ((N+1 : ℝ) * Z (N-(j.val+1))) * Q (some ⟨j,b⟩ : StationaryBlock N) = M b := by
    simp only [Q, q]
    field_simp
  rw [hid]
  exact hp

/-- Reindex a finite sum along a list's actual histogram. -/
lemma list_sum_histogram (l : List α) (w : α → ℕ) :
    (l.map w).sum = ∑ a, w a * l.count a := by
  have h := Finset.sum_multiset_map_count (l : Multiset α) w
  have hs : ∑ a ∈ (l : Multiset α).toFinset,
      (l : Multiset α).count a • w a = ∑ a, (l : Multiset α).count a • w a := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro a ha hn
    simp only [Multiset.mem_toFinset] at hn
    simp [Multiset.count_eq_zero_of_notMem hn]
  rw [hs] at h
  simpa [nsmul_eq_mul, mul_comm] using h

lemma list_count_sum (l : List α) : ∑ a, l.count a = l.length := by
  simpa using (list_sum_histogram l (fun _ => 1)).symm

/-- The ordered gap indices carried by a block; each `i` means length `i+1`. -/
def gapList {L : ℕ} (b : Block L) : List (Fin L) := List.ofFn b.2.val

@[simp] lemma gapList_count {L : ℕ} (b : Block L) (i : Fin L) :
    (gapList b).count i = (b.1.val i).val := b.2.prop i

lemma gapList_sum {L : ℕ} (b : Block L) :
    ((gapList b).map (fun i => i.val+1)).sum = ∑ i, (i.val+1) * (b.1.val i).val := by
  rw [list_sum_histogram]
  simp

lemma gapList_sum_le {L : ℕ} (b : Block L) :
    ((gapList b).map (fun i => i.val+1)).sum ≤ L := by
  rw [gapList_sum]
  exact b.1.prop

lemma length_le_gap_weight {L : ℕ} (l : List (Fin L)) :
    l.length ≤ (l.map (fun i => i.val+1)).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.length_cons, List.map_cons, List.sum_cons]; omega

/-- Construct a completed-gap block from its ordered gap symbols. -/
def ofGapList {L : ℕ} (l : List (Fin L))
    (hl : (l.map (fun i => i.val+1)).sum ≤ L) : Block L := by
  have hlen : l.length ≤ L := (length_le_gap_weight l).trans hl
  let c : FeasibleCounts L := ⟨fun i =>
    ⟨l.count i, Nat.lt_succ_of_le ((List.count_le_length (a := i) (l := l)).trans hlen)⟩, by
      simpa only [← list_sum_histogram l (fun i => i.val+1)] using hl⟩
  have hK : gapCount (fun i => (c.val i).val) = l.length := by
    exact list_count_sum l
  refine ⟨c, ?_⟩
  refine ⟨fun i => l.get (Fin.cast hK i), ?_⟩
  have hof : List.ofFn (fun i => l.get (Fin.cast hK i)) = l := by
    have hh := List.ofFn_congr hK.symm l.get
    simpa using hh.symm
  intro a
  simpa only [hof] using (show l.count a = (c.val a).val from rfl)

@[simp] theorem gapList_ofGapList {L : ℕ} (l : List (Fin L))
    (hl : (l.map (fun i => i.val+1)).sum ≤ L) : gapList (ofGapList l hl) = l := by
  unfold gapList ofGapList
  dsimp only
  have hh := (List.ofFn_congr (list_count_sum l).symm l.get).symm
  simpa only [List.ofFn_get] using hh

/-- Histograms are recoverable from the ordered list, so the representation
contains no duplicate ordinary blocks. -/
theorem gapList_injective (L : ℕ) : Function.Injective (@gapList L) := by
  rintro ⟨c,f⟩ ⟨d,g⟩ heq
  have hc : c = d := by
    apply Subtype.ext
    funext a
    apply Fin.ext
    exact (f.prop a).symm.trans ((congrArg (List.count a) heq).trans (g.prop a))
  cases hc
  congr 1
  apply Subtype.ext
  exact List.ofFn_injective heq

/-- Write the uncensored renewals represented by gap indices. -/
def encodeGaps : List ℕ → List Bool
  | [] => []
  | d::ds => List.replicate d false ++ true :: encodeGaps ds

lemma encodeGaps_length (l : List ℕ) :
    (encodeGaps l).length = (l.map (fun d => d+1)).sum := by
  induction l with
  | nil => simp [encodeGaps]
  | cons d ds ih => simp [encodeGaps, ih, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- Actual binary ordinary word represented by a completed-gap block. -/
def encode {L : ℕ} (b : Block L) : List Bool :=
  let ds := (gapList b).map Fin.val
  encodeGaps ds ++ List.replicate (L - (ds.map (fun d => d+1)).sum) false

lemma encode_length {L : ℕ} (b : Block L) : (encode b).length = L := by
  have hh := gapList_sum_le b
  simpa [encode, encodeGaps_length, List.map_map, Function.comp_def] using Nat.add_sub_of_le hh

/-- Parse completed gap indices with current censored age `a`. -/
def parseGaps (a : ℕ) : List Bool → List ℕ
  | [] => []
  | false::x => parseGaps (a+1) x
  | true::x => a :: parseGaps 0 x

/-- The remaining censored age after a binary word. -/
def parseAge (a : ℕ) : List Bool → ℕ
  | [] => a
  | false::x => parseAge (a+1) x
  | true::x => parseAge 0 x

lemma parseGaps_zeros (a n : ℕ) : parseGaps a (List.replicate n false) = [] := by
  induction n generalizing a with
  | zero => simp [parseGaps]
  | succ n ih => simpa [parseGaps] using ih (a+1)

lemma parseGaps_zeros_prefix (a n : ℕ) (x : List Bool) :
    parseGaps a (List.replicate n false ++ x) = parseGaps (a+n) x := by
  induction n generalizing a with
  | zero => simp
  | succ n ih => simpa [parseGaps, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (a+1)

lemma parseGaps_encodeGaps (ds : List ℕ) (A : ℕ) :
    parseGaps 0 (encodeGaps ds ++ List.replicate A false) = ds := by
  induction ds with
  | nil => simp [encodeGaps, parseGaps_zeros]
  | cons d ds ih => simp [encodeGaps, List.append_assoc, parseGaps_zeros_prefix, parseGaps, ih]

@[simp] lemma parseGaps_encode {L : ℕ} (b : Block L) :
    parseGaps 0 (encode b) = (gapList b).map Fin.val := by
  exact parseGaps_encodeGaps _ _

/-- The binary encoding is injective; completed gap histograms and orderings
therefore do not overcount words in B.4. -/
theorem encode_injective (L : ℕ) : Function.Injective (@encode L) := by
  intro b c heq
  apply gapList_injective L
  apply List.map_injective_iff.mpr Fin.val_injective
  simpa only [parseGaps_encode] using congrArg (parseGaps 0) heq

/-- Parsing followed by encoding recovers the initial age as a zero prefix.
This also establishes the precise terminal-censoring convention. -/
theorem reconstruct (a : ℕ) (x : List Bool) :
    encodeGaps (parseGaps a x) ++ List.replicate (parseAge a x) false =
      List.replicate a false ++ x := by
  induction x generalizing a with
  | nil => simp [parseGaps, parseAge, encodeGaps]
  | cons b x ih =>
    cases b with
    | false =>
      simpa [parseGaps, parseAge, List.replicate_succ', List.append_assoc] using ih (a+1)
    | true =>
      simp only [parseGaps, parseAge, encodeGaps, List.append_assoc, List.cons_append]
      rw [ih 0]
      simp

lemma parse_weight_age (a : ℕ) (x : List Bool) :
    ((parseGaps a x).map (fun d => d+1)).sum + parseAge a x = a + x.length := by
  have hh := congrArg List.length (reconstruct a x)
  simpa [encodeGaps_length] using hh

lemma parse_weight_le (x : List Bool) :
    ((parseGaps 0 x).map (fun d => d+1)).sum ≤ x.length := by
  have hh := parse_weight_age 0 x
  omega

lemma parsed_gap_lt (x : List Bool) {d : ℕ} (hd : d ∈ parseGaps 0 x) : d < x.length := by
  have hm : d+1 ∈ (parseGaps 0 x).map (fun d => d+1) := List.mem_map.mpr ⟨d,hd,rfl⟩
  have hh := (List.le_sum_of_mem hm).trans (parse_weight_le x)
  omega

/-- Parse a binary length-`L` word into its bounded alphabet of gap indices. -/
def parsedGapList (L : ℕ) (x : List Bool) (hx : x.length = L) : List (Fin L) :=
  (parseGaps 0 x).attach.map (fun d => ⟨d.val, by rw [← hx]; exact parsed_gap_lt x d.prop⟩)

@[simp] lemma parsedGapList_vals (L : ℕ) (x : List Bool) (hx : x.length = L) :
    (parsedGapList L x hx).map Fin.val = parseGaps 0 x := by
  simp [parsedGapList, List.map_map]

lemma parsedGapList_weight (L : ℕ) (x : List Bool) (hx : x.length = L) :
    ((parsedGapList L x hx).map (fun i => i.val+1)).sum ≤ L := by
  have hh := parse_weight_le x
  rw [hx] at hh
  simpa [parsedGapList, List.map_map] using hh

/-- Every binary word has an ordinary completed-gap block representation. -/
def ofWord (L : ℕ) (x : List Bool) (hx : x.length = L) : Block L :=
  ofGapList (parsedGapList L x hx) (parsedGapList_weight L x hx)

theorem encode_ofWord (L : ℕ) (x : List Bool) (hx : x.length = L) :
    encode (ofWord L x hx) = x := by
  have hh := parse_weight_age 0 x
  rw [hx] at hh
  have ha : L - ((parseGaps 0 x).map (fun d => d+1)).sum = parseAge 0 x := by omega
  simp only [encode, ofWord, gapList_ofGapList, parsedGapList_vals]
  rw [ha]
  simpa using reconstruct 0 x

/-- Source-object equivalence between the interval-gap representation and all
binary words at a fixed horizon. -/
def blockEquivWord (L : ℕ) : Block L ≃ {x : List Bool // x.length = L} where
  toFun b := ⟨encode b, encode_length b⟩
  invFun x := ofWord L x.val x.prop
  left_inv b := encode_injective L (encode_ofWord L (encode b) (encode_length b))
  right_inv x := Subtype.ext (encode_ofWord L x.val x.prop)

/-- The same empirical likelihood written directly on a finite ordered sample.
This presentation makes independence of the ambient gap alphabet explicit. -/
def listEnvelope {β : Type*} [DecidableEq β] (l : List β) : ℝ :=
  (l.map (fun d => (l.count d : ℝ) / l.length)).prod

lemma listEnvelope_map_injective {β γ : Type*} [DecidableEq β] [DecidableEq γ]
    (l : List β) (f : β → γ) (hf : Function.Injective f) :
    listEnvelope (l.map f) = listEnvelope l := by
  simp [listEnvelope, List.map_map, List.count_map_of_injective l f hf, Function.comp_def]

lemma M_eq_listEnvelope {L : ℕ} (b : Block L) : M b = listEnvelope (gapList b) := by
  have hh := ordered_product_eq (fun i => (b.1.val i).val) b.2
    (fun a => ((b.1.val a).val : ℝ) / gapCount (fun i => (b.1.val i).val))
  simpa [M, gapEnvelope, listEnvelope, gapList, List.map_ofFn, List.prod_ofFn, b.2.prop] using hh.symm

lemma M_eq_nat_listEnvelope {L : ℕ} (b : Block L) :
    M b = listEnvelope ((gapList b).map Fin.val) := by
  rw [listEnvelope_map_injective _ _ Fin.val_injective, M_eq_listEnvelope]

lemma gapList_ofWord_vals (L : ℕ) (x : List Bool) (hx : x.length = L) :
    (gapList (ofWord L x hx)).map Fin.val = parseGaps 0 x := by
  rw [ofWord, gapList_ofGapList, parsedGapList_vals]

lemma parseGaps_append_false (a : ℕ) (x : List Bool) :
    parseGaps a (x ++ [false]) = parseGaps a x := by
  induction x generalizing a with
  | nil => simp [parseGaps]
  | cons b x ih => cases b <;> simp [parseGaps, ih]

/-- The injection `y ↦ y0` from the proof of Lemma B.1. -/
def appendZero {L : ℕ} (b : Block L) : Block (L+1) :=
  ofWord (L+1) (encode b ++ [false]) (by simp [encode_length])

@[simp] lemma encode_appendZero {L : ℕ} (b : Block L) :
    encode (appendZero b) = encode b ++ [false] := encode_ofWord _ _ _

@[simp] lemma M_appendZero {L : ℕ} (b : Block L) : M (appendZero b) = M b := by
  rw [M_eq_nat_listEnvelope, M_eq_nat_listEnvelope]
  congr 1
  unfold appendZero
  rw [gapList_ofWord_vals, parseGaps_append_false, parseGaps_encode]

lemma appendZero_injective (L : ℕ) : Function.Injective (@appendZero L) := by
  intro b c heq
  apply encode_injective L
  have hh := congrArg encode heq
  simpa using hh

/-- Appending one censored zero preserves every completed gap, proving the
monotonicity clause of Lemma B.1 on the actual binary-word sample space. -/
theorem Z_succ_mono (L : ℕ) : Z L ≤ Z (L+1) := by
  classical
  calc
    Z L = ∑ b : Block L, M (appendZero b) := by simp only [Z, M_appendZero]
    _ = ∑ b ∈ Finset.univ.image (@appendZero L), M b := by
      rw [Finset.sum_image]
      exact fun b hb c hc heq => appendZero_injective L heq
    _ ≤ Z (L+1) := Finset.sum_le_univ_sum_of_nonneg (fun b => (M_pos b).le)

theorem Z_monotone : Monotone Z := monotone_nat_of_le_succ Z_succ_mono

/-- B.3 for a completed ordered-gap block and an arbitrary subprobability on
its finite alphabet. -/
theorem completed_likelihood_le_M {L : ℕ} (b : Block L) (μ : Fin L → ℝ)
    (hμ : ∀ i, 0 ≤ μ i) (hsum : ∑ i, μ i ≤ 1) :
    ((gapList b).map μ).prod ≤ M b := by
  have hh := ordered_product_eq (fun i => (b.1.val i).val) b.2 μ
  have hmax := likelihood_le_gapEnvelope (fun i => (b.1.val i).val) μ hμ hsum
  simpa [gapList, List.map_ofFn, List.prod_ofFn, hh, M] using hmax

/-- Dropping a terminal survival factor in `[0,1]` gives B.3. -/
theorem censored_likelihood_le_M {L : ℕ} (b : Block L) (μ : Fin L → ℝ)
    (hμ : ∀ i, 0 ≤ μ i) (hsum : ∑ i, μ i ≤ 1)
    (survival : ℝ) (hs0 : 0 ≤ survival) (hs1 : survival ≤ 1) :
    ((gapList b).map μ).prod * survival ≤ M b := by
  have hp : 0 ≤ ((gapList b).map μ).prod := List.prod_nonneg (fun x hx => by
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    exact hμ i)
  exact (mul_le_of_le_one_right hp hs1).trans (completed_likelihood_le_M b μ hμ hsum)

/-- A no-renewal word has regret at most the mixture's uniform component cost. -/
theorem Q_ratio_none {N : ℕ} {p : ℝ} (hp : p ≤ 1) :
    p / Q (none : StationaryBlock N) ≤ (N+1 : ℝ) := by
  have hN : 0 < (N+1 : ℝ) := by positivity
  simp only [Q, div_eq_mul_inv, inv_inv, one_mul]
  exact mul_le_of_le_one_left hN.le hp

/-- The monotonicity of the ordinary normalizer gives the common block-regret
factor `(N+1) Z_N` for each nonzero first-renewal component. -/
theorem Q_ratio_le_global {N : ℕ} (j : Fin N)
    (b : Block (N - (j.val+1))) (p : ℝ) (hp : p ≤ M b) :
    p / Q (some ⟨j,b⟩) ≤ (N+1 : ℝ) * Z N := by
  exact (Q_ratio_le_local j b p hp).trans
    (mul_le_mul_of_nonneg_left (Z_monotone (Nat.sub_le _ _)) (by positivity))

/-- Taking logs in B.8 is valid on every positive-probability block. -/
theorem Q_log_regret_le {N : ℕ} (j : Fin N)
    (b : Block (N - (j.val+1))) (p : ℝ) (hp0 : 0 < p) (hp : p ≤ M b) :
    Real.log (p / Q (some ⟨j,b⟩)) ≤ Real.log ((N+1 : ℝ) * Z N) := by
  exact Real.log_le_log (div_pos hp0 (Q_pos _)) (Q_ratio_le_global j b p hp)

end Paper37.Envelope
