import Paper37.MultisetDP
import Paper37.EnvelopeBridge

namespace Paper37.DP
open Finset

/-- Actual first-admissible ordering count for a natural-number histogram. -/
noncomputable def actualFirst (s : Finset ℕ) (A : ℕ) (b : ℕ → ℕ)
    (hk : 0 < s.sum b) : ℕ :=
  ∑ f : TupleOrdering (fun j : s => b j),
    if A < (f.val ⟨0, by simpa only [sum_coe_sort] using hk⟩).val then 1 else 0

/-- The integer used by the DP counts the actual ordered tuples whose first
future gap is greater than the currently censored age. -/
theorem admissibleOrders_eq_actualFirst (s : Finset ℕ) (A : ℕ) (b : ℕ → ℕ)
    (hk : 0 < s.sum b) : admissibleOrders s A b = actualFirst s A b hk := by
  classical
  have hs : (∑ j : s, b j) = s.sum b := sum_coe_sort _ _
  have hm : Nat.multinomial univ (fun j : s => b j) = Nat.multinomial s b := by
    have hprod : (∏ j : s, (b j).factorial) = ∏ j ∈ s, (b j).factorial :=
      prod_coe_sort s (fun j => (b j).factorial)
    simp only [Nat.multinomial, hs, hprod]
  have hp : (∑ j : s, if A < j.val then b j else 0) = marked s A b := by
    exact sum_coe_sort s (fun j => if A < j then b j else 0)
  have ha := actual_ordering_mark_identity (fun j : s => b j)
    (show 0 < ∑ j : s, b j from hs.symm ▸ hk) (fun j => A < j.val)
  apply Nat.eq_of_mul_eq_mul_left hk
  calc
    _ = Nat.multinomial s b * marked s A b := (marked_ordering_identity s A b).symm
    _ = Nat.multinomial univ (fun j : s => b j) *
        (∑ j : s, if A < j.val then b j else 0) := by rw [hm, hp]
    _ = (∑ j : s, b j) * actualFirst s A b hk := ha
    _ = _ := congrArg (fun n => n * actualFirst s A b hk) hs

end Paper37.DP

namespace Paper37.ContinuationDP

open Finset Paper37.Envelope Paper37.Prediction Paper37.Renewal

/-- A future gap block is precisely a block with the already elapsed age as a
zero prefix. This definition includes the single no-future-renewal block. -/
def FutureBlock (A R : ℕ) :=
  {b : Block (A + R) // List.replicate A false <+: encode b}

instance (A R : ℕ) : Fintype (FutureBlock A R) :=
  inferInstanceAs (Fintype {b : Block (A + R) // _})

lemma zeros_append_drop {A R : ℕ} (b : FutureBlock A R) :
    List.replicate A false ++ (encode b.val).drop A = encode b.val := by
  simpa only [List.length_replicate] using List.prefix_iff_eq_append.mp b.prop

/-- An exact finite bijection from admissible ordered future gap blocks to
all binary extensions. There is no counting assumption in this equivalence. -/
def futureEquivSuffix (A R : ℕ) :
    FutureBlock A R ≃ {v : List Bool // v.length = R} where
  toFun b := ⟨(encode b.val).drop A, by simp [encode_length]⟩
  invFun v := ⟨ofWord (A + R) (List.replicate A false ++ v.val) (by simp [v.prop]), by
    rw [encode_ofWord]
    exact ⟨v.val, rfl⟩⟩
  left_inv b := by
    apply Subtype.ext
    apply encode_injective (A + R)
    rw [encode_ofWord]
    exact zeros_append_drop b
  right_inv v := by
    apply Subtype.ext
    simp [encode_ofWord]

/-- The source continuation sum reindexed by actual admissible completed-gap
blocks, with both censored boundaries retained. -/
theorem continuationMass_futureBlocks (z : List Bool) (R : ℕ) :
    continuationMass (z.length + R) z =
      ∑ b : FutureBlock (parseAge 0 z) R,
        wordEnvelope (z ++ (encode b.val).drop (parseAge 0 z)) := by
  classical
  unfold continuationMass
  have heq : z.length + R - z.length = R := by omega
  rw [heq]
  symm
  apply sum_bij (fun b _ => (encode b.val).drop (parseAge 0 z))
  · intro b hb
    exact List.mem_toFinset.mpr ((mem_words R _).mpr ((futureEquivSuffix _ _ b).prop))
  · intro b hb c hc heq
    exact (futureEquivSuffix _ _).injective (Subtype.ext heq)
  · intro v hv
    have hvl : v.length = R := (mem_words R v).mp (List.mem_toFinset.mp hv)
    exact ⟨(futureEquivSuffix _ _).symm ⟨v, hvl⟩, mem_univ _,
      congrArg Subtype.val ((futureEquivSuffix _ _).apply_symm_apply ⟨v,hvl⟩)⟩
  · intro b hb
    rfl

/-- Parsing a continuation preserves the completed observed gaps and begins
the future gap sequence at the actual current censored age. -/
theorem parseGaps_append (a : ℕ) (z v : List Bool) :
    parseGaps a (z ++ v) = parseGaps a z ++ parseGaps (parseAge a z) v := by
  induction z generalizing a with
  | nil => simp [parseGaps, parseAge]
  | cons b z ih => cases b <;> simp [parseGaps, parseAge, ih]

/-- Exact gap sequence of every extension in the preceding source bijection. -/
theorem extension_gaps (z : List Bool) (R : ℕ)
    (b : FutureBlock (parseAge 0 z) R) :
    parseGaps 0 (z ++ (encode b.val).drop (parseAge 0 z)) =
      parseGaps 0 z ++ (gapList b.val).map Fin.val := by
  rw [parseGaps_append]
  congr 1
  have hh := congrArg (parseGaps 0) (zeros_append_drop b)
  rw [parseGaps_zeros_prefix, zero_add, parseGaps_encode] at hh
  exact hh

end Paper37.ContinuationDP

namespace Paper37.ContinuationDP
open Finset Paper37.Envelope Paper37.Prediction Paper37.Renewal

/-- First future gap lengths are indexed by their length minus one. -/
def firstAdmissible {L : ℕ} (A : ℕ) (b : Block L) : Prop :=
  match gapList b with
  | [] => True
  | d :: _ => A ≤ d.val

instance {L : ℕ} (A : ℕ) (b : Block L) : Decidable (firstAdmissible A b) := by
  unfold firstAdmissible
  split <;> infer_instance

lemma zeros_prefix_zeros_one_iff (A d : ℕ) (x : List Bool) :
    List.replicate A false <+: List.replicate d false ++ true :: x ↔ A ≤ d := by
  induction A generalizing d with
  | zero => simp
  | succ A ih =>
    cases d with
    | zero => simp [List.replicate_succ]
    | succ d => simpa [List.replicate_succ] using ih d

/-- A completed gap block admits the elapsed age exactly when its first
future gap is longer than that age. Empty gap lists give the unique zero run. -/
theorem zeros_prefix_iff_firstAdmissible (A R : ℕ) (b : Block (A + R)) :
    List.replicate A false <+: encode b ↔ firstAdmissible A b := by
  cases hg : gapList b with
  | nil =>
    simp only [firstAdmissible, hg]
    constructor
    · intro h; trivial
    · intro h
      have he : encode b = List.replicate (A + R) false := by simp [encode, hg, encodeGaps]
      rw [he, List.replicate_add]
      exact ⟨List.replicate R false, rfl⟩
  | cons d ds =>
    simp only [firstAdmissible, hg]
    simpa [encode, hg, encodeGaps, List.append_assoc] using
      zeros_prefix_zeros_one_iff A d.val
        (encodeGaps (ds.map Fin.val) ++
          List.replicate (A + R - (((d :: ds).map Fin.val).map (fun n => n + 1)).sum) false)

/-- The source continuation as a sum over all future gap histograms and
actual orderings, retaining the first-gap feasibility restriction. -/
theorem continuationMass_orderings (z : List Bool) (R : ℕ) :
    continuationMass (z.length + R) z =
      ∑ b : Block (parseAge 0 z + R),
        if firstAdmissible (parseAge 0 z) b then
          wordEnvelope (z ++ (encode b).drop (parseAge 0 z)) else 0 := by
  classical
  rw [continuationMass_futureBlocks]
  change (∑ b : {b : Block (parseAge 0 z + R) // _},
    wordEnvelope (z ++ (encode b.val).drop (parseAge 0 z))) = _
  rw [← Finset.sum_subtype (univ.filter (fun b : Block (parseAge 0 z + R) =>
    List.replicate (parseAge 0 z) false <+: encode b)) (by simp)
    (fun b => wordEnvelope (z ++ (encode b).drop (parseAge 0 z))), sum_filter]
  apply sum_congr rfl
  intro b hb
  simp only [zeros_prefix_iff_firstAdmissible]

@[simp] theorem gapList_zeroBlock (L : ℕ) : gapList (zeroBlock L) = [] := by
  simp [gapList, zeroBlock, zeroCounts, gapCount]

/-- Exactly one future block contains no renewal. -/
theorem gapList_eq_nil_iff {L : ℕ} (b : Block L) :
    gapList b = [] ↔ b = zeroBlock L := by
  constructor
  · intro h
    apply gapList_injective L
    simpa using h
  · rintro rfl
    exact gapList_zeroBlock L

/-- A zero-only extension has precisely the prefix's completed-gap envelope,
which is `M_nf` in equation C.3. -/
theorem noFutureRenewal_envelope (z : List Bool) (R : ℕ) :
    wordEnvelope (z ++ List.replicate R false) = wordEnvelope z := by
  unfold wordEnvelope
  rw [← Paper37.EnvelopeBridge.parseGaps_eq_gapsFrom,
    ← Paper37.EnvelopeBridge.parseGaps_eq_gapsFrom, parseGaps_append, parseGaps_zeros,
    List.append_nil]

end Paper37.ContinuationDP

namespace Paper37.ContinuationDP
open Finset Paper37.Envelope Paper37.Prediction Paper37.Renewal

lemma sum_count_of_support (g : List ℕ) (s : Finset ℕ)
    (hg : g.toFinset ⊆ s) : ∑ d ∈ s, g.count d = g.length := by
  rw [← List.sum_toFinset_count_eq_length g]
  symm
  apply sum_subset hg
  intro d hd hnot
  exact List.count_eq_zero.mpr (fun h => hnot (List.mem_toFinset.mpr h))

/-- The empirical envelope expressed over any finite alphabet containing its
completed gaps; unused types contribute `0^0=1`. -/
theorem gapEnvelope_on_alphabet (g : List ℕ) (s : Finset ℕ)
    (hg : g.toFinset ⊆ s) :
    Prediction.gapEnvelope g = ∏ d ∈ s,
      ((g.count d : ℚ) / (g.length : ℚ)) ^ g.count d := by
  unfold Prediction.gapEnvelope
  apply prod_subset hg
  intro d hd hnot
  have hc : g.count d = 0 :=
    List.count_eq_zero.mpr (fun h => hnot (List.mem_toFinset.mpr h))
  simp [hc]

/-- Exact rational numerator and denominator of a completed-gap envelope.
This includes the empty gap sequence by the source's `0^0=1` convention. -/
theorem gapEnvelope_numerator (g : List ℕ) (s : Finset ℕ)
    (hg : g.toFinset ⊆ s) :
    Prediction.gapEnvelope g =
      (∏ d ∈ s, (g.count d : ℚ) ^ g.count d) / (g.length : ℚ) ^ g.length := by
  rw [gapEnvelope_on_alphabet g s hg]
  simp_rw [div_pow]
  rw [prod_div_distrib, prod_pow_eq_pow_sum, sum_count_of_support g s hg]

/-- The extended word has the numerator obtained by adding observed and
future counts. All hypotheses are support facts about the actual gap lists. -/
theorem extension_envelope_histogram (z : List Bool) (R : ℕ)
    (b : FutureBlock (parseAge 0 z) R) (s : Finset ℕ)
    (hs : (parseGaps 0 z ++ (gapList b.val).map Fin.val).toFinset ⊆ s) :
    wordEnvelope (z ++ (encode b.val).drop (parseAge 0 z)) =
      (∏ d ∈ s, ((parseGaps 0 z).count d + ((gapList b.val).map Fin.val).count d : ℚ) ^
        ((parseGaps 0 z).count d + ((gapList b.val).map Fin.val).count d)) /
        ((parseGaps 0 z).length + (gapList b.val).length : ℚ) ^
          ((parseGaps 0 z).length + (gapList b.val).length) := by
  unfold wordEnvelope
  rw [← Paper37.EnvelopeBridge.parseGaps_eq_gapsFrom, extension_gaps,
    gapEnvelope_numerator _ s hs]
  simp [List.count_append, List.length_append, List.length_map]

end Paper37.ContinuationDP

namespace Paper37.ContinuationDP
open Finset Paper37.Envelope Paper37.DP

/-- Positive gap lengths and the source's length-minus-one alphabet are
canonically equivalent. -/
def gapEquiv (L : ℕ) : Fin L ≃ (gapSet L) where
  toFun i := ⟨i.val + 1, by simp only [gapSet, mem_Icc]; omega⟩
  invFun d := ⟨d.val - 1, by have h := mem_Icc.mp d.prop; omega⟩
  left_inv i := by apply Fin.ext; simp
  right_inv d := by apply Subtype.ext; have h := mem_Icc.mp d.prop; simp; omega

lemma sum_gapSet {M : Type*} [AddCommMonoid M] (L : ℕ) (f : ℕ → M) :
    ∑ d ∈ gapSet L, f d = ∑ i : Fin L, f (i.val + 1) := by
  rw [← sum_coe_sort]
  exact (Fintype.sum_equiv (gapEquiv L) _ _ (fun i => rfl)).symm

lemma prod_gapSet {M : Type*} [CommMonoid M] (L : ℕ) (f : ℕ → M) :
    ∏ d ∈ gapSet L, f d = ∏ i : Fin L, f (i.val + 1) := by
  rw [← prod_coe_sort]
  exact (Fintype.prod_equiv (gapEquiv L) _ _ (fun i => rfl)).symm

/-- A finite histogram on positive natural gap lengths, extended by zero. -/
def extendCounts (L : ℕ) (c : Fin L → ℕ) (d : ℕ) : ℕ :=
  if h : d ∈ gapSet L then c ⟨d - 1, by have h' := mem_Icc.mp h; omega⟩ else 0

@[simp] lemma extendCounts_succ (L : ℕ) (c : Fin L → ℕ) (i : Fin L) :
    extendCounts L c (i.val + 1) = c i := by
  have hi : i.val + 1 ∈ gapSet L := by simp only [gapSet, mem_Icc]; omega
  simp [extendCounts, hi]

lemma extendCounts_support (L : ℕ) (c : Fin L → ℕ) :
    ∀ d, extendCounts L c d ≠ 0 → d ∈ gapSet L := by
  intro d hd
  by_contra hn
  simp [extendCounts, hn] at hd

/-- The same exact count-vector domain as the feasible bounded histograms,
without imposing an artificial bound on an ambient function type. -/
def CountFamily (L : ℕ) :=
  {b : ℕ → ℕ // (∀ d, b d ≠ 0 → d ∈ gapSet L) ∧ lengthSum (gapSet L) b ≤ L}

lemma count_le_weight (L : ℕ) (b : ℕ → ℕ) :
    (gapSet L).sum b ≤ lengthSum (gapSet L) b := by
  apply sum_le_sum
  intro d hd
  have hd' : 1 ≤ d := (mem_Icc.mp hd).1
  simpa only [one_mul] using Nat.mul_le_mul_right (b d) hd'

lemma family_count_le (L : ℕ) (b : CountFamily L) : (gapSet L).sum b.val ≤ L :=
  (count_le_weight L b.val).trans b.prop.2

/-- Convert the natural histogram to the source's bounded finite alphabet. -/
def familyToCounts (L : ℕ) (b : CountFamily L) : FeasibleCounts L := by
  refine ⟨fun i => ⟨b.val (i.val + 1), ?_⟩, ?_⟩
  · have hi : i.val + 1 ∈ gapSet L := by simp only [gapSet, mem_Icc]; omega
    have h := (single_le_sum (fun d hd => Nat.zero_le (b.val d)) hi).trans (family_count_le L b)
    omega
  · simpa only [lengthSum, sum_gapSet] using b.prop.2

lemma familyToCounts_injective (L : ℕ) : Function.Injective (familyToCounts L) := by
  intro b c heq
  apply Subtype.ext
  funext d
  by_cases hd : d ∈ gapSet L
  · let i : Fin L := ⟨d - 1, by have h := mem_Icc.mp hd; omega⟩
    have hi : i.val + 1 = d := by have h := mem_Icc.mp hd; dsimp [i]; omega
    have h := congrArg (fun a : FeasibleCounts L => (a.val i).val) heq
    simpa only [familyToCounts, hi] using h
  · have hb : b.val d = 0 := by by_contra hn; exact hd (b.prop.1 d hn)
    have hc : c.val d = 0 := by by_contra hn; exact hd (c.prop.1 d hn)
    rw [hb, hc]

noncomputable instance (L : ℕ) : Fintype (CountFamily L) :=
  Fintype.ofInjective (familyToCounts L) (familyToCounts_injective L)

/-- Exact regrouping of feasible count vectors by future count `k` and future
length sum `u`. Each original count vector occurs once in this finite sum. -/
theorem countFamily_sum (L : ℕ) (h : (ℕ → ℕ) → ℚ) :
    (∑ c : CountFamily L, h c.val) =
      ∑ k ∈ range (L + 1), ∑ u ∈ range (L + 1),
        ∑ b ∈ (gapSet L).piAntidiag k, if lengthSum (gapSet L) b = u then h b else 0 := by
  classical
  let triples : Finset (Σ _k : ℕ, Σ _u : ℕ, ℕ → ℕ) :=
    (range (L + 1)).sigma fun k => (range (L + 1)).sigma fun u =>
      ((gapSet L).piAntidiag k).filter fun b => lengthSum (gapSet L) b = u
  have htr : (∑ t ∈ triples, h t.2.2) =
      ∑ k ∈ range (L + 1), ∑ u ∈ range (L + 1),
        ∑ b ∈ (gapSet L).piAntidiag k, if lengthSum (gapSet L) b = u then h b else 0 := by
    simp only [triples, sum_sigma, sum_filter]
  rw [← htr]
  apply sum_bij (fun c _ => ⟨(gapSet L).sum c.val, ⟨lengthSum (gapSet L) c.val, c.val⟩⟩)
  · intro c hc
    simp only [triples, mem_sigma, mem_range, mem_filter, mem_piAntidiag]
    exact ⟨by have hh := family_count_le L c; omega,
      by have hh := c.prop.2; omega, ⟨trivial, c.prop.1⟩, trivial⟩
  · intro c hc d hd heq
    apply Subtype.ext
    exact congrArg (fun t => t.2.2) heq
  · rintro ⟨k,u,b⟩ hmem
    simp only [triples, mem_sigma, mem_range, mem_filter, mem_piAntidiag] at hmem
    rcases hmem with ⟨hk, hu, ⟨hsum, hsup⟩, hlen⟩
    refine ⟨⟨b, hsup, by omega⟩, mem_univ _, ?_⟩
    simp only
    rw [hsum, hlen]
  · intro c hc
    rfl

end Paper37.ContinuationDP

namespace Paper37.ContinuationDP
open Finset Paper37.Envelope Paper37.DP Paper37.Prediction

/-- Extend the source's bounded histogram by zero to positive gap lengths. -/
def countsToFamily (L : ℕ) (c : FeasibleCounts L) : CountFamily L :=
  ⟨extendCounts L (fun i => (c.val i).val), extendCounts_support _ _, by
    simpa only [lengthSum, sum_gapSet, extendCounts_succ] using c.prop⟩

@[simp] theorem familyToCounts_countsToFamily (L : ℕ) (c : FeasibleCounts L) :
    familyToCounts L (countsToFamily L c) = c := by
  apply Subtype.ext
  funext i
  apply Fin.ext
  simp [familyToCounts, countsToFamily]

/-- Feasible source histograms and finitely supported natural histograms
are equivalent as finite indexing sets. -/
def countsEquivFamily (L : ℕ) : FeasibleCounts L ≃ CountFamily L where
  toFun := countsToFamily L
  invFun := familyToCounts L
  left_inv := familyToCounts_countsToFamily L
  right_inv b := familyToCounts_injective L (familyToCounts_countsToFamily L _)

lemma gapEnvelope_list_product (g : List ℕ) :
    Prediction.gapEnvelope g =
      (g.map (fun d => (g.count d : ℚ) / (g.length : ℚ))).prod := by
  have h := Finset.prod_multiset_map_count (g : Multiset ℕ)
    (fun d => (g.count d : ℚ) / (g.length : ℚ))
  simpa [Prediction.gapEnvelope] using h.symm

/-- Shifting gap indices to positive gap lengths does not change the envelope. -/
theorem gapEnvelope_map_succ (g : List ℕ) :
    Prediction.gapEnvelope (g.map Nat.succ) = Prediction.gapEnvelope g := by
  rw [gapEnvelope_list_product, gapEnvelope_list_product]
  simp only [List.map_map, List.length_map]
  congr 1
  apply List.map_congr_left
  intro d hd
  simp only [Function.comp_apply, List.count_map_of_injective g Nat.succ Nat.succ_injective]

/-- Observed completed-gap counts indexed by their actual positive lengths. -/
def observedCounts (z : List Bool) (d : ℕ) : ℕ :=
  ((parseGaps 0 z).map Nat.succ).count d

/-- All observed completed gaps lie in the source horizon's positive alphabet. -/
lemma observed_support (z : List Bool) (H : ℕ) (hz : z.length ≤ H) :
    ((parseGaps 0 z).map Nat.succ).toFinset ⊆ gapSet H := by
  intro d hd
  rcases List.mem_map.mp (List.mem_toFinset.mp hd) with ⟨i, hi, rfl⟩
  have h := parsed_gap_lt z hi
  simp only [gapSet, mem_Icc]
  omega

/-- Feasible future histograms use no positive gap longer than their budget. -/
lemma family_gap_le (T : ℕ) (b : CountFamily T) {d : ℕ} (hd : b.val d ≠ 0) : d ≤ T :=
  (mem_Icc.mp (b.prop.1 d hd)).2

lemma lengthSum_mono_alphabet (s t : Finset ℕ) (b : ℕ → ℕ)
    (hst : s ⊆ t) (hb : ∀ d ∈ t, d ∉ s → b d = 0) : lengthSum s b = lengthSum t b := by
  apply sum_subset hst
  intro d hd hnot
  rw [hb d hd hnot, mul_zero]

/-- Low total gap length forces zero counts outside the smaller alphabet. -/
lemma support_of_length_le (H T : ℕ) (b : ℕ → ℕ)
    (hsup : ∀ d, b d ≠ 0 → d ∈ gapSet H) (hlen : lengthSum (gapSet H) b ≤ T) :
    ∀ d, b d ≠ 0 → d ∈ gapSet T := by
  intro d hd
  have hin := hsup d hd
  have hlow : d ≤ d * b d := by
    simpa only [mul_one] using Nat.mul_le_mul_left d (Nat.one_le_iff_ne_zero.mpr hd)
  have hsum : d * b d ≤ lengthSum (gapSet H) b :=
    single_le_sum (fun j hj => Nat.zero_le (j * b j)) hin
  have hdpos : 1 ≤ d := (mem_Icc.mp hin).1
  exact mem_Icc.mpr ⟨hdpos, hlow.trans (hsum.trans hlen)⟩

end Paper37.ContinuationDP

namespace Paper37.ContinuationDP
open Finset Paper37.DP Paper37.Envelope

lemma sum_alphabet_eq (s t : Finset ℕ) (b : ℕ → ℕ) (hst : s ⊆ t)
    (hb : ∀ d, b d ≠ 0 → d ∈ s) : s.sum b = t.sum b := by
  apply sum_subset hst
  intro d hd hnot
  by_contra hn
  exact hnot (hb d hn)

lemma multinomial_alphabet_eq (s t : Finset ℕ) (b : ℕ → ℕ) (hst : s ⊆ t)
    (hb : ∀ d, b d ≠ 0 → d ∈ s) : Nat.multinomial s b = Nat.multinomial t b := by
  have hp : (∏ d ∈ s, (b d).factorial) = ∏ d ∈ t, (b d).factorial := by
    apply prod_subset hst
    intro d hd hnot
    have hz : b d = 0 := by by_contra hn; exact hnot (hb d hn)
    simp [hz]
  unfold Nat.multinomial
  rw [sum_alphabet_eq s t b hst hb, hp]

lemma marked_alphabet_eq (s t : Finset ℕ) (A : ℕ) (b : ℕ → ℕ) (hst : s ⊆ t)
    (hb : ∀ d, b d ≠ 0 → d ∈ s) : marked s A b = marked t A b := by
  apply sum_subset hst
  intro d hd hnot
  have hz : b d = 0 := by by_contra hn; exact hnot (hb d hn)
  simp [hz]

lemma admissibleOrders_zero_count (s : Finset ℕ) (A : ℕ) (b : ℕ → ℕ)
    (hk : s.sum b = 0) : admissibleOrders s A b = 0 := by
  unfold admissibleOrders
  apply sum_eq_zero
  intro d hd
  have hz : b d = 0 := by
    have hh : b d ≤ s.sum b := single_le_sum (fun i hi => Nat.zero_le _) hd
    omega
  simp [firstOrders, hz]

/-- Adding unavailable gap lengths does not change the actual ordering count. -/
lemma admissibleOrders_alphabet_eq (s t : Finset ℕ) (A : ℕ) (b : ℕ → ℕ) (hst : s ⊆ t)
    (hb : ∀ d, b d ≠ 0 → d ∈ s) : admissibleOrders s A b = admissibleOrders t A b := by
  have hs := sum_alphabet_eq s t b hst hb
  by_cases hk : s.sum b = 0
  · rw [admissibleOrders_zero_count s A b hk,
      admissibleOrders_zero_count t A b (hs.symm.trans hk)]
  · apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hk)
    have ht := marked_ordering_identity t A b
    rw [← hs, ← multinomial_alphabet_eq s t b hst hb,
      ← marked_alphabet_eq s t A b hst hb] at ht
    exact (marked_ordering_identity s A b).symm.trans ht

lemma gapSet_mono {T H : ℕ} (hTH : T ≤ H) : gapSet T ⊆ gapSet H := by
  intro d hd
  simp only [gapSet, mem_Icc] at hd ⊢
  omega

/-- Regroup a future-length budget using the paper's full ambient gap alphabet.
Longer unavailable types occur with count zero, while their observed counts
are retained later in the likelihood weight. -/
theorem countFamily_sum_ambient (H T : ℕ) (hTH : T ≤ H) (h : (ℕ → ℕ) → ℚ) :
    (∑ c : CountFamily T, h c.val) =
      ∑ k ∈ range (T + 1), ∑ u ∈ range (T + 1),
        ∑ b ∈ (gapSet H).piAntidiag k, if lengthSum (gapSet H) b = u then h b else 0 := by
  classical
  let triples : Finset (Σ _k : ℕ, Σ _u : ℕ, ℕ → ℕ) :=
    (range (T + 1)).sigma fun k => (range (T + 1)).sigma fun u =>
      ((gapSet H).piAntidiag k).filter fun b => lengthSum (gapSet H) b = u
  have htr : (∑ t ∈ triples, h t.2.2) =
      ∑ k ∈ range (T + 1), ∑ u ∈ range (T + 1),
        ∑ b ∈ (gapSet H).piAntidiag k, if lengthSum (gapSet H) b = u then h b else 0 := by
    simp only [triples, sum_sigma, sum_filter]
  rw [← htr]
  apply sum_bij (fun c _ => ⟨(gapSet H).sum c.val, ⟨lengthSum (gapSet H) c.val, c.val⟩⟩)
  · intro c hc
    have hs := sum_alphabet_eq (gapSet T) (gapSet H) c.val (gapSet_mono hTH) c.prop.1
    have hl : lengthSum (gapSet T) c.val = lengthSum (gapSet H) c.val := by
      apply lengthSum_mono_alphabet _ _ _ (gapSet_mono hTH)
      intro d hd hn
      by_contra hz
      exact hn (c.prop.1 d hz)
    simp only [triples, mem_sigma, mem_range, mem_filter, mem_piAntidiag]
    exact ⟨by rw [← hs]; have hh := family_count_le T c; omega,
      by rw [← hl]; have hh := c.prop.2; omega,
      ⟨trivial, fun d hd => gapSet_mono hTH (c.prop.1 d hd)⟩, trivial⟩
  · intro c hc d hd heq
    apply Subtype.ext
    exact congrArg (fun t => t.2.2) heq
  · rintro ⟨k,u,b⟩ hmem
    simp only [triples, mem_sigma, mem_range, mem_filter, mem_piAntidiag] at hmem
    rcases hmem with ⟨hk, hu, ⟨hsum, hsup⟩, hlen⟩
    have hsT := support_of_length_le H T b hsup (by omega)
    have hl : lengthSum (gapSet T) b = lengthSum (gapSet H) b := by
      apply lengthSum_mono_alphabet _ _ _ (gapSet_mono hTH)
      intro d hd hn
      by_contra hz
      exact hn (hsT d hz)
    refine ⟨⟨b, hsT, by omega⟩, mem_univ _, ?_⟩
    simp only
    rw [hsum, hlen]
  · intro c hc
    rfl

end Paper37.ContinuationDP

namespace Paper37.ContinuationDP
open Finset Paper37.DP Paper37.Envelope

lemma family_count_eq_gapCount {T : ℕ} (c : FeasibleCounts T) :
    (gapSet T).sum (countsToFamily T c).val = gapCount (fun i => (c.val i).val) := by
  simp [countsToFamily, sum_gapSet, gapCount]

lemma family_multinomial_eq {T : ℕ} (c : FeasibleCounts T) :
    Nat.multinomial (gapSet T) (countsToFamily T c).val =
      Nat.multinomial univ (fun i => (c.val i).val) := by
  simp [Nat.multinomial, countsToFamily, sum_gapSet, prod_gapSet]

lemma family_marked_eq {T : ℕ} (c : FeasibleCounts T) (A : ℕ) :
    marked (gapSet T) A (countsToFamily T c).val =
      ∑ i : Fin T, if A ≤ i.val then (c.val i).val else 0 := by
  simp [marked, countsToFamily, sum_gapSet, Nat.lt_succ_iff]

noncomputable def sourceFirstCount {T : ℕ} (c : FeasibleCounts T) (A : ℕ)
    (hk : 0 < gapCount (fun i => (c.val i).val)) : ℕ :=
  ∑ f : Ordering (fun i => (c.val i).val),
    if A ≤ (f.val ⟨0,hk⟩).val then 1 else 0

/-- C.9 on the exact finite source alphabet used by `Block`. -/
theorem admissibleOrders_eq_sourceFirstCount {T : ℕ} (c : FeasibleCounts T) (A : ℕ)
    (hk : 0 < gapCount (fun i => (c.val i).val)) :
    admissibleOrders (gapSet T) A (countsToFamily T c).val = sourceFirstCount c A hk := by
  apply Nat.eq_of_mul_eq_mul_left hk
  have hn := marked_ordering_identity (gapSet T) A (countsToFamily T c).val
  rw [family_count_eq_gapCount, family_multinomial_eq, family_marked_eq] at hn
  exact hn.symm.trans (actual_ordering_mark_identity (fun i => (c.val i).val) hk
    (fun i => A ≤ i.val))

lemma firstAdmissible_ordering {T : ℕ} (c : FeasibleCounts T) (A : ℕ)
    (f : Ordering (fun i => (c.val i).val))
    (hk : 0 < gapCount (fun i => (c.val i).val)) :
    firstAdmissible A (⟨c,f⟩ : Block T) ↔ A ≤ (f.val ⟨0,hk⟩).val := by
  have hlen : (List.ofFn f.val).length ≠ 0 := by simpa using Nat.ne_of_gt hk
  cases hl : List.ofFn f.val with
  | nil => exact False.elim (hlen (by rw [hl]; rfl))
  | cons d ds =>
    have hh := List.getElem_ofFn (f := f.val) (i := 0) (by simpa using hk)
    have hhead : d = f.val ⟨0,hk⟩ := by simpa only [hl, List.getElem_cons_zero] using hh
    simp only [firstAdmissible, gapList, hl, hhead]

/-- Summing an ordering-independent mass over the actual admissible orderings
produces exactly the integer used in the multiset DP. The zero histogram
has its one empty ordering and contributes the no-renewal mass once. -/
theorem ordering_sum_mass {T : ℕ} (c : FeasibleCounts T) (A : ℕ) (q : ℚ) :
    (∑ f : Ordering (fun i => (c.val i).val),
      if firstAdmissible A (⟨c,f⟩ : Block T) then q else 0) =
      if hk : 0 < gapCount (fun i => (c.val i).val) then
        (admissibleOrders (gapSet T) A (countsToFamily T c).val : ℚ) * q else q := by
  classical
  by_cases hk : 0 < gapCount (fun i => (c.val i).val)
  · rw [dif_pos hk, admissibleOrders_eq_sourceFirstCount c A hk]
    unfold sourceFirstCount
    rw [Nat.cast_sum, sum_mul]
    apply sum_congr rfl
    intro f hf
    simp only [firstAdmissible_ordering c A f hk]
    split_ifs <;> simp
  · rw [dif_neg hk]
    have hz : gapCount (fun i => (c.val i).val) = 0 := by omega
    have hc0 := (gapCount_zero_iff _).mp hz
    have hf (f : Ordering (fun i => (c.val i).val)) :
        firstAdmissible A (⟨c,f⟩ : Block T) := by
      have hl : List.ofFn f.val = [] := List.length_eq_zero.mp (by simp [hz])
      simp [firstAdmissible, gapList, hl]
    simp only [hf, if_true, sum_const, card_univ, nsmul_eq_mul]
    have hcard : Fintype.card (Ordering (fun i => (c.val i).val)) = 1 := by
      have hh := DP.card_count_tuples (fun i => (c.val i).val)
      simpa [Envelope.Ordering, gapCount, hc0, Nat.multinomial] using hh
    simp [hcard]

end Paper37.ContinuationDP

namespace Paper37.ContinuationDP
open Finset Paper37.DP Paper37.Envelope Paper37.Prediction

lemma future_positive_support {T : ℕ} (b : Block T) :
    ((gapList b).map (fun i => i.val + 1)).toFinset ⊆ gapSet T := by
  intro d hd
  rcases List.mem_map.mp (List.mem_toFinset.mp hd) with ⟨i, hi, rfl⟩
  simp only [gapSet, mem_Icc]
  omega

lemma future_positive_count {T : ℕ} (c : FeasibleCounts T)
    (f : Envelope.Ordering (fun i => (c.val i).val)) (d : ℕ) :
    (((gapList (⟨c,f⟩ : Block T)).map (fun i => i.val + 1)).count d) =
      (countsToFamily T c).val d := by
  classical
  have hinj : Function.Injective (fun i : Fin T => i.val + 1) := by
    intro i j h
    change i.val + 1 = j.val + 1 at h
    apply Fin.ext
    omega
  by_cases hd : d ∈ gapSet T
  · let i : Fin T := ⟨d - 1, by have h := mem_Icc.mp hd; omega⟩
    have hid : i.val + 1 = d := by have h := mem_Icc.mp hd; dsimp [i]; omega
    rw [← hid]
    rw [List.count_map_of_injective _ _ hinj]
    simp [countsToFamily]
  · have hc : (((gapList (⟨c,f⟩ : Block T)).map (fun i => i.val + 1)).count d) = 0 := by
      apply List.count_eq_zero.mpr
      intro hm
      exact hd (future_positive_support (⟨c,f⟩ : Block T) (List.mem_toFinset.mpr hm))
    rw [hc]
    simp [countsToFamily, extendCounts, hd]

/-- The likelihood mass of one future histogram after the observed prefix.
The numerator retains all observed gap types in the original horizon. -/
def histogramMass (H : ℕ) (z : List Bool) (b : ℕ → ℕ) : ℚ :=
  (weight (observedCounts z) (gapSet H) b : ℚ) /
    (((parseGaps 0 z).length + (gapSet H).sum b : ℕ) : ℚ) ^
      ((parseGaps 0 z).length + (gapSet H).sum b)

lemma age_le_length (z : List Bool) : parseAge 0 z ≤ z.length := by
  have hh := parse_weight_age 0 z
  omega

/-- The source word mass is constant on future histograms, with the exact
numerator and denominator used in C.8. -/
theorem extension_eq_histogramMass (H : ℕ) (z : List Bool) (R : ℕ)
    (hH : z.length + R ≤ H) (b : FutureBlock (parseAge 0 z) R) :
    wordEnvelope (z ++ (encode b.val).drop (parseAge 0 z)) =
      histogramMass H z (countsToFamily (parseAge 0 z + R) b.val.1).val := by
  classical
  let obs := (parseGaps 0 z).map Nat.succ
  let fut := (gapList b.val).map (fun i => i.val + 1)
  have hTH : parseAge 0 z + R ≤ H := by have hh := age_le_length z; omega
  have ho : obs.toFinset ⊆ gapSet H := observed_support z H (by omega)
  have hf : fut.toFinset ⊆ gapSet H :=
    (future_positive_support b.val).trans (gapSet_mono hTH)
  have hsupport : (obs ++ fut).toFinset ⊆ gapSet H := by
    intro d hd
    simp only [List.toFinset_append, mem_union] at hd
    exact hd.elim (fun h => ho h) (fun h => hf h)
  have hc (d : ℕ) : fut.count d = (countsToFamily (parseAge 0 z + R) b.val.1).val d :=
    future_positive_count b.val.1 b.val.2 d
  have hcount : (gapSet H).sum (countsToFamily (parseAge 0 z + R) b.val.1).val =
      (gapList b.val).length := by
    have hfl : fut.length = (gapList b.val).length := by simp [fut]
    rw [← hfl, ← sum_count_of_support fut (gapSet H) hf]
    exact sum_congr rfl fun d hd => (hc d).symm
  unfold wordEnvelope
  rw [← Paper37.EnvelopeBridge.parseGaps_eq_gapsFrom, extension_gaps,
    ← gapEnvelope_map_succ]
  have hmap : (parseGaps 0 z ++ (gapList b.val).map Fin.val).map Nat.succ = obs ++ fut := by
    simp [obs, fut, List.map_map]
  rw [hmap, gapEnvelope_numerator _ _ hsupport]
  simp only [List.count_append, hc, List.length_append, List.length_map]
  unfold histogramMass weight observedCounts
  rw [hcount]
  push_cast
  simp only [obs, fut, List.length_map]

end Paper37.ContinuationDP

namespace Paper37.ContinuationDP
open Finset Paper37.DP Paper37.Envelope Paper37.Prediction

/-- Full source continuation after grouping only by feasible future histograms. -/
theorem continuationMass_histograms (H : ℕ) (z : List Bool) (R : ℕ)
    (hH : z.length + R ≤ H) :
    continuationMass (z.length + R) z =
      ∑ c : FeasibleCounts (parseAge 0 z + R),
        if hk : 0 < gapCount (fun i => (c.val i).val) then
          (admissibleOrders (gapSet (parseAge 0 z + R)) (parseAge 0 z)
            (countsToFamily (parseAge 0 z + R) c).val : ℚ) *
              histogramMass H z (countsToFamily (parseAge 0 z + R) c).val
        else histogramMass H z (countsToFamily (parseAge 0 z + R) c).val := by
  classical
  rw [continuationMass_orderings]
  change (∑ b : (Σ c : FeasibleCounts (parseAge 0 z + R),
    Envelope.Ordering (fun i => (c.val i).val)), _) = _
  rw [Fintype.sum_sigma]
  apply sum_congr rfl
  intro c hc
  rw [← ordering_sum_mass c (parseAge 0 z)]
  apply sum_congr rfl
  intro f hf
  by_cases hfirst : firstAdmissible (parseAge 0 z) (⟨c,f⟩ : Block (parseAge 0 z + R))
  · simp only [if_pos hfirst]
    exact extension_eq_histogramMass H z R hH
      ⟨⟨c,f⟩, (zeros_prefix_iff_firstAdmissible _ _ _).mpr hfirst⟩
  · simp [hfirst]

/-- A future histogram's contribution, with the empty future kept separate. -/
def contribution (H : ℕ) (z : List Bool) (A : ℕ) (b : ℕ → ℕ) : ℚ :=
  if (gapSet H).sum b = 0 then histogramMass H z b
  else (admissibleOrders (gapSet H) A b : ℚ) * histogramMass H z b

/-- The source continuation reindexed by the exact count-vector domain. -/
theorem continuationMass_countFamily (H : ℕ) (z : List Bool) (R : ℕ)
    (hH : z.length + R ≤ H) :
    continuationMass (z.length + R) z =
      ∑ b : CountFamily (parseAge 0 z + R), contribution H z (parseAge 0 z) b.val := by
  classical
  rw [continuationMass_histograms H z R hH]
  apply Fintype.sum_equiv (countsEquivFamily (parseAge 0 z + R))
  intro c
  have hTH : parseAge 0 z + R ≤ H := by have hh := age_le_length z; omega
  let b := countsToFamily (parseAge 0 z + R) c
  have hs : (gapSet H).sum b.val = gapCount (fun i => (c.val i).val) := by
    rw [← sum_alphabet_eq _ _ b.val (gapSet_mono hTH) b.prop.1]
    exact family_count_eq_gapCount c
  have ho := admissibleOrders_alphabet_eq (gapSet (parseAge 0 z + R)) (gapSet H)
    (parseAge 0 z) b.val (gapSet_mono hTH) b.prop.1
  change _ = contribution H z (parseAge 0 z) b.val
  unfold contribution
  rw [hs, ← ho]
  by_cases hk : 0 < gapCount (fun i => (c.val i).val)
  · simp [hk, Nat.ne_of_gt hk, b]
  · have hz : gapCount (fun i => (c.val i).val) = 0 := by omega
    simp [hz, b]

/-- The no-future-renewal mass agrees exactly with C.3, including `r=0`. -/
theorem histogramMass_zero (H : ℕ) (z : List Bool) (hz : z.length ≤ H) :
    histogramMass H z 0 = wordEnvelope z := by
  unfold wordEnvelope
  rw [← Paper37.EnvelopeBridge.parseGaps_eq_gapsFrom, ← gapEnvelope_map_succ,
    gapEnvelope_numerator _ _ (observed_support z H hz)]
  simp [histogramMass, weight, observedCounts]

/-- Summing one nonempty count/length state produces `F` divided by the
combined empirical denominator. -/
lemma state_mass_eq_F (H : ℕ) (z : List Bool) (A k u : ℕ) (hk : k ≠ 0) :
    (∑ b ∈ (gapSet H).piAntidiag k,
      if lengthSum (gapSet H) b = u then contribution H z A b else 0) =
      (F (observedCounts z) (gapSet H) A k u : ℚ) /
        (((parseGaps 0 z).length + k : ℕ) : ℚ) ^ ((parseGaps 0 z).length + k) := by
  unfold F
  rw [Nat.cast_sum, sum_div]
  apply sum_congr rfl
  intro b hb
  have hs := (mem_piAntidiag.mp hb).1
  by_cases hl : lengthSum (gapSet H) b = u
  · simp only [if_pos hl, contribution, hs, if_neg hk, histogramMass, Nat.cast_mul]
    ring
  · simp [hl]

/-- The zero-count slice is the unique no-future-renewal extension. -/
lemma zero_state_mass (H T : ℕ) (z : List Bool) (A : ℕ) :
    (∑ u ∈ range (T + 1), ∑ b ∈ (gapSet H).piAntidiag 0,
      if lengthSum (gapSet H) b = u then contribution H z A b else 0) =
      histogramMass H z 0 := by
  simp [lengthSum, contribution]

end Paper37.ContinuationDP

namespace Paper37.ContinuationDP
open Finset Paper37.DP Paper37.Envelope Paper37.Prediction

lemma F_eq_zero_of_lt (H A k u : ℕ) (a : ℕ → ℕ) (hku : u < k) :
    F a (gapSet H) A k u = 0 := by
  unfold F
  apply sum_eq_zero
  intro b hb
  have hsum := (mem_piAntidiag.mp hb).1
  have hbound := count_le_weight H b
  have hne : lengthSum (gapSet H) b ≠ u := by omega
  simp [hne]

/-- C.8 expressed using the independent weighted counts of actual admissible
first orderings. This theorem starts at the exhaustive binary source sum. -/
theorem continuationMass_eq_F (H : ℕ) (z : List Bool) (R : ℕ)
    (hH : z.length + R ≤ H) :
    continuationMass (z.length + R) z = wordEnvelope z +
      ∑ k ∈ Icc 1 (parseAge 0 z + R), ∑ u ∈ Icc k (parseAge 0 z + R),
        (F (observedCounts z) (gapSet H) (parseAge 0 z) k u : ℚ) /
          (((parseGaps 0 z).length + k : ℕ) : ℚ) ^ ((parseGaps 0 z).length + k) := by
  classical
  let T := parseAge 0 z + R
  have hTH : T ≤ H := by have hh := age_le_length z; dsimp [T]; omega
  rw [continuationMass_countFamily H z R hH, countFamily_sum_ambient H T hTH]
  have hrange : range (T + 1) = insert 0 (Icc 1 T) := by
    ext k
    simp only [mem_range, mem_insert, mem_Icc]
    omega
  rw [hrange, sum_insert (by simp)]
  have hzstate : (∑ u ∈ insert 0 (Icc 1 T),
      ∑ b ∈ (gapSet H).piAntidiag 0,
        if lengthSum (gapSet H) b = u then contribution H z (parseAge 0 z) b else 0) =
      histogramMass H z 0 := by
    rw [← hrange]
    exact zero_state_mass H T z (parseAge 0 z)
  rw [hzstate, histogramMass_zero H z (by omega)]
  congr 1
  apply sum_congr rfl
  intro k hk
  have hkpos : 0 < k := (mem_Icc.mp hk).1
  have hkn : k ≠ 0 := Nat.ne_of_gt hkpos
  calc
    _ = ∑ u ∈ insert 0 (Icc 1 T),
        (F (observedCounts z) (gapSet H) (parseAge 0 z) k u : ℚ) /
          (((parseGaps 0 z).length + k : ℕ) : ℚ) ^ ((parseGaps 0 z).length + k) := by
      apply sum_congr rfl
      intro u hu
      exact state_mass_eq_F H z (parseAge 0 z) k u hkn
    _ = ∑ u ∈ Icc k T,
        (F (observedCounts z) (gapSet H) (parseAge 0 z) k u : ℚ) /
          (((parseGaps 0 z).length + k : ℕ) : ℚ) ^ ((parseGaps 0 z).length + k) := by
      rw [← hrange]
      symm
      apply sum_subset
      · intro u hu
        simp only [mem_Icc, mem_range] at hu ⊢
        omega
      · intro u hu hnot
        have hlt : u < k := by
          simp only [mem_Icc, mem_range] at hu hnot
          omega
        rw [F_eq_zero_of_lt H (parseAge 0 z) k u (observedCounts z) hlt]
        simp

/-- Equation C.8 with the exact integer division certified by Lemma C.1. -/
theorem continuationMass_eq_integerDP (H : ℕ) (z : List Bool) (R : ℕ)
    (hH : z.length + R ≤ H) :
    continuationMass (z.length + R) z = wordEnvelope z +
      ∑ k ∈ Icc 1 (parseAge 0 z + R), ∑ u ∈ Icc k (parseAge 0 z + R),
        ((Sd (observedCounts z) (parseAge 0 z) H k u / k : ℕ) : ℚ) /
          (((parseGaps 0 z).length + k : ℕ) : ℚ) ^ ((parseGaps 0 z).length + k) := by
  rw [continuationMass_eq_F H z R hH]
  congr 1
  apply sum_congr rfl
  intro k hk
  apply sum_congr rfl
  intro u hu
  rw [show Sd (observedCounts z) (parseAge 0 z) H k u / k =
      F (observedCounts z) (gapSet H) (parseAge 0 z) k u from
    S_div_eq_F _ _ _ _ _ ((mem_Icc.mp hk).1)]

/-- Safe executable access to the materialized table. Out-of-range states
are zero, as in the paper's domain convention. -/
def layerAt {H : ℕ} (table : Layer H) (k u : ℕ) : ℕ × ℕ :=
  if hk : k < H + 1 then
    if hu : u < H + 1 then table[k][u] else (0,0)
  else (0,0)

lemma layerAt_run (H : ℕ) (a : ℕ → ℕ) (A d k u : ℕ) (hk : k ≤ H) (hu : u ≤ H) :
    layerAt (run H a A d) k u = (Gd a d k u, Sd a A d k u) := by
  have hk' : k < H + 1 := by omega
  have hu' : u < H + 1 := by omega
  simp only [layerAt, dif_pos hk', dif_pos hu']
  exact run_correct H a A d ⟨k,hk'⟩ ⟨u,hu'⟩

/-- Executable C.6--C.8 query. The rolling integer table is computed once;
all final summands use its entries and the certified exact integer division. -/
def evaluateContinuation (H : ℕ) (z : List Bool) (R : ℕ) : ℚ :=
  let A := parseAge 0 z
  let r := (parseGaps 0 z).length
  let T := A + R
  let table := run H (observedCounts z) A H
  histogramMass H z 0 +
    ∑ k ∈ Icc 1 T, ∑ u ∈ Icc k T,
      (((layerAt table k u).2 / k : ℕ) : ℚ) / ((r + k : ℕ) : ℚ) ^ (r + k)

/-- The actual executable rolling-table query returns the exhaustive source
continuation mass, for every source prefix and remaining horizon. -/
theorem evaluateContinuation_correct (H : ℕ) (z : List Bool) (R : ℕ)
    (hH : z.length + R ≤ H) :
    evaluateContinuation H z R = continuationMass (z.length + R) z := by
  rw [continuationMass_eq_integerDP H z R hH]
  unfold evaluateContinuation
  dsimp only
  rw [histogramMass_zero H z (by omega)]
  congr 1
  apply sum_congr rfl
  intro k hk
  apply sum_congr rfl
  intro u hu
  have hTH : parseAge 0 z + R ≤ H := by have hh := age_le_length z; omega
  rw [layerAt_run H (observedCounts z) (parseAge 0 z) H k u
    ((mem_Icc.mp hk).2.trans hTH) ((mem_Icc.mp hu).2.trans hTH)]

/-- A user query stated at the original horizon, with no free remainder. -/
theorem evaluateContinuation_horizon (H : ℕ) (z : List Bool) (hz : z.length ≤ H) :
    evaluateContinuation H z (H - z.length) = continuationMass H z := by
  have heq : z.length + (H - z.length) = H := Nat.add_sub_of_le hz
  simpa only [heq] using evaluateContinuation_correct H z (H - z.length) (by omega)

end Paper37.ContinuationDP

namespace Paper37.ContinuationDP
open Finset Paper37.DP Paper37.Envelope Paper37.Prediction

/-- C.8 in its original rational form; the integer-division implementation
above computes exactly these terms. -/
theorem continuationMass_eq_multisetDP (H : ℕ) (z : List Bool) (R : ℕ)
    (hH : z.length + R ≤ H) :
    continuationMass (z.length + R) z = wordEnvelope z +
      ∑ k ∈ Icc 1 (parseAge 0 z + R), ∑ u ∈ Icc k (parseAge 0 z + R),
        (Sd (observedCounts z) (parseAge 0 z) H k u : ℚ) /
          ((k : ℚ) * (((parseGaps 0 z).length + k : ℕ) : ℚ) ^
            ((parseGaps 0 z).length + k)) := by
  rw [continuationMass_eq_F H z R hH]
  congr 1
  apply sum_congr rfl
  intro k hk
  apply sum_congr rfl
  intro u hu
  have hk' : (k : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt ((mem_Icc.mp hk).1)
  change _ = (S (observedCounts z) (gapSet H) (parseAge 0 z) k u : ℚ) / _
  rw [S_eq_mul_F, Nat.cast_mul]
  exact (mul_div_mul_left _ _ hk').symm

/-- Execute the two child masses in Proposition C.2 after the first renewal. -/
def evaluateVisibleConditional (L : ℕ) (z : List Bool) : ℚ :=
  let w₁ := evaluateContinuation L (z ++ [true]) (L - (z.length + 1))
  let w₀ := evaluateContinuation L (z ++ [false]) (L - (z.length + 1))
  w₁ / (w₀ + w₁)

/-- An exact conditional query for an arbitrary supplied prefix. -/
def evaluateConditional (N : ℕ) (y : List Bool) : ℚ :=
  match firstSuffix y with
  | none => 1 / ((N - y.length + 1 : ℕ) : ℚ)
  | some z => evaluateVisibleConditional (N - y.length + z.length) z

/-- The executable conditional answers every valid queried prefix exactly. -/
theorem evaluateConditional_correct (N : ℕ) (y : List Bool) (hy : y.length < N) :
    evaluateConditional N y = blockConditional N y := by
  classical
  unfold evaluateConditional
  cases hs : firstSuffix y with
  | none =>
    dsimp only
    have hz := Paper37.EnvelopeBridge.firstSuffix_none_iff y |>.mp hs
    rw [hz, Paper37.EnvelopeBridge.blockConditional_zeros N y.length hy]
    simp only [List.length_replicate]
  | some z =>
    dsimp only
    obtain ⟨j,hj⟩ := Paper37.EnvelopeBridge.firstSuffix_some_decomposition y z hs
    have hlen : y.length = j + 1 + z.length := by simp [hj]; omega
    have hz : z.length < N - (j + 1) := by omega
    have hL : N - y.length + z.length = N - (j + 1) := by omega
    rw [hL, hj, Paper37.EnvelopeBridge.blockConditional_firstRenewal N j z (by omega)]
    unfold evaluateVisibleConditional
    have hchild (b : Bool) : (z ++ [b]).length ≤ N - (j + 1) := by simp; omega
    have heval (b : Bool) : evaluateContinuation (N - (j + 1)) (z ++ [b])
        (N - (j + 1) - (z.length + 1)) = continuationMass (N - (j + 1)) (z ++ [b]) := by
      simpa only [List.length_append, List.length_singleton] using
        evaluateContinuation_horizon _ _ (hchild b)
    simp only [heval true, heval false]

/-- Executable compression-averaged predictor D.1. Each summand invokes only
the corresponding supplied suffix query. -/
def evaluatePredictor (n : ℕ) (x : List Bool) : ℚ :=
  (∑ t ∈ Icc 1 n, evaluateConditional (n + 1) (x.drop (n - t))) / n

/-- The executable suffix batch implements the exact source predictor. -/
theorem evaluatePredictor_correct (n : ℕ) (x : List Bool) (hx : x.length = n) :
    evaluatePredictor n x = predict n x := by
  unfold evaluatePredictor predict
  congr 1
  apply sum_congr rfl
  intro t ht
  apply evaluateConditional_correct
  have htn : t ≤ n := (mem_Icc.mp ht).2
  simp only [List.length_drop, hx]
  omega

end Paper37.ContinuationDP

namespace Paper37.ContinuationDP
open Finset Paper37.DP Paper37.Envelope Paper37.Prediction Paper37.Renewal

/-- Reindex any source extension sum by actual future gap blocks. This is the
same finite bijection as C.8 and also supports the occupied-type refinement. -/
theorem sum_extensions_futureBlocks (z : List Bool) (R : ℕ) (g : List Bool → ℚ) :
    (∑ v ∈ (words R).toFinset, g (z ++ v)) =
      ∑ b : FutureBlock (parseAge 0 z) R,
        g (z ++ (encode b.val).drop (parseAge 0 z)) := by
  classical
  symm
  apply sum_bij (fun b _ => (encode b.val).drop (parseAge 0 z))
  · intro b hb
    exact List.mem_toFinset.mpr ((mem_words R _).mpr ((futureEquivSuffix _ _ b).prop))
  · intro b hb c hc heq
    exact (futureEquivSuffix _ _).injective (Subtype.ext heq)
  · intro v hv
    have hvl : v.length = R := (mem_words R v).mp (List.mem_toFinset.mp hv)
    exact ⟨(futureEquivSuffix _ _).symm ⟨v, hvl⟩, mem_univ _,
      congrArg Subtype.val ((futureEquivSuffix _ _).apply_symm_apply ⟨v,hvl⟩)⟩
  · intro b hb
    rfl

/-- Generic exact histogram regrouping for a source extension statistic whose
value depends only on the future histogram. This supports E.7 by using the
occupied-type restriction in `q`, with the same genuine source bijection. -/
theorem sum_extensions_histograms (z : List Bool) (R : ℕ) (g : List Bool → ℚ)
    (q : FeasibleCounts (parseAge 0 z + R) → ℚ)
    (hg : ∀ b : FutureBlock (parseAge 0 z) R,
      g (z ++ (encode b.val).drop (parseAge 0 z)) = q b.val.1) :
    (∑ v ∈ (words R).toFinset, g (z ++ v)) =
      ∑ c : FeasibleCounts (parseAge 0 z + R),
        if hk : 0 < gapCount (fun i => (c.val i).val) then
          (admissibleOrders (gapSet (parseAge 0 z + R)) (parseAge 0 z)
            (countsToFamily (parseAge 0 z + R) c).val : ℚ) * q c else q c := by
  classical
  rw [sum_extensions_futureBlocks]
  change (∑ b : {b : Block (parseAge 0 z + R) // _}, _) = _
  rw [← Finset.sum_subtype (univ.filter (fun b : Block (parseAge 0 z + R) =>
    List.replicate (parseAge 0 z) false <+: encode b)) (by simp)
    (fun b => g (z ++ (encode b).drop (parseAge 0 z))), sum_filter]
  change (∑ b : (Σ c : FeasibleCounts (parseAge 0 z + R),
    Envelope.Ordering (fun i => (c.val i).val)), _) = _
  rw [Fintype.sum_sigma]
  apply sum_congr rfl
  intro c hc
  rw [← ordering_sum_mass c (parseAge 0 z)]
  apply sum_congr rfl
  intro f hf
  by_cases hfirst : firstAdmissible (parseAge 0 z) (⟨c,f⟩ : Block (parseAge 0 z + R))
  · have hprefix := (zeros_prefix_iff_firstAdmissible _ _ _).mpr hfirst
    simp only [if_pos hprefix, if_pos hfirst]
    exact hg ⟨⟨c,f⟩, hprefix⟩
  · have hn : ¬List.replicate (parseAge 0 z) false <+: encode (⟨c,f⟩ : Block (parseAge 0 z + R)) := by
      simpa only [zeros_prefix_iff_firstAdmissible] using hfirst
    simp [hfirst, hn]

end Paper37.ContinuationDP
