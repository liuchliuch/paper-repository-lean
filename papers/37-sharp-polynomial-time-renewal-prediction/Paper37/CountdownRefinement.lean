import Paper37.SuffixRegeneration
import Mathlib.Analysis.Normed.Group.Tannery

/-! Original unbounded countdown event semantics for Lemma D.1. Index `c`
means the next renewal is exactly `c+1` steps from the start of the suffix.
For a renewal beyond the observed `t+1` symbols, the event is the actual longer
cylinder of `c` zeros followed by one. No conditional-independence field is used. -/
namespace Paper37.CountdownRefinement

open Finset Compression Compression.Distribution Renewal RenewalCompression RenewalCountdown
open SuffixRegeneration
open Filter
open scoped Topology

noncomputable def countableJointMass (μ : Law) {k t : ℕ} (o : Word k) (s : Word t)
    (y : Bool) (c : ℕ) : ℝ :=
  if c ≤ t then
    if firstOneIndex (s.val ++ [y]) = c then blockMass μ ((o.val ++ s.val) ++ [y]) else 0
  else if s = zeros t ∧ y = false then
    blockMass μ ((o.val ++ List.replicate c false) ++ [true]) else 0

lemma countableJointMass_nonneg (μ : Law) {k t : ℕ} (o : Word k) (s : Word t)
    (y : Bool) (c : ℕ) : 0 ≤ countableJointMass μ o s y c := by
  unfold countableJointMass
  split_ifs <;> first | exact blockMass_nonneg μ _ | exact le_rfl

lemma countableJointMass_finite (μ : Law) {k t : ℕ} (o : Word k) (s : Word t)
    (y : Bool) (c : ℕ) (hc : c ≤ t) :
    countableJointMass μ o s y c = jointMass μ o s y ⟨c, by omega⟩ := by
  unfold countableJointMass jointMass
  rw [if_pos hc]
  simp only [Fin.ext_iff, countdownValue]

/-- Rank-one factorization at every original, unbounded countdown value. -/
theorem countableJointMass_rank_one (μ : Law) {k t : ℕ} (o o' : Word k) (s : Word t)
    (y y' : Bool) (c : ℕ) :
    countableJointMass μ o s y c * countableJointMass μ o' s y' c =
      countableJointMass μ o s y' c * countableJointMass μ o' s y c := by
  by_cases hc : c ≤ t
  · simp_rw [countableJointMass_finite μ _ s _ c hc]
    exact jointMass_rank_one μ o o' s y y' ⟨c, by omega⟩
  · cases y <;> cases y' <;> simp [countableJointMass, hc]

/-- Original D.1, for every countable countdown event C=c+1, expressed as the
exact finite older-history/outcome marginal identity defining conditional independence. -/
theorem suffix_regeneration_unbounded (μ : Law) {k t : ℕ} (o : Word k) (s : Word t)
    (y : Bool) (c : ℕ) :
    countableJointMass μ o s y c *
        (∑ o' : Word k, ∑ y' : Bool, countableJointMass μ o' s y' c) =
      (∑ y' : Bool, countableJointMass μ o s y' c) *
        (∑ o' : Word k, countableJointMass μ o' s y c) := by
  simp_rw [mul_sum, sum_mul]
  apply sum_congr rfl
  intro o' _
  apply sum_congr rfl
  intro y' _
  exact countableJointMass_rank_one μ o o' s y y' c

/-- Finite mean makes the stationary no-renewal numerator tend to zero. -/
theorem residual_tendsto_zero (μ : Law) : Tendsto (residual μ) atTop (𝓝 0) := by
  have h := tendsto_tsum_of_dominated_convergence (𝓕 := (atTop : Filter ℕ)) μ.finiteMean
    (f := fun n d : ℕ => ((d+1-n : ℕ) : ℝ) * μ.mass d)
    (g := fun _ : ℕ => (0 : ℝ)) ?_ ?_
  · simpa only [Renewal.residual, tsum_zero] using h
  · intro d
    apply tendsto_const_nhds.congr'
    exact eventually_atTop.mpr ⟨d+1, fun n hn => by simp [Nat.sub_eq_zero_of_le hn]⟩
  · apply Eventually.of_forall
    intro n d
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) (μ.nonneg d))]
    apply mul_le_mul_of_nonneg_right _ (μ.nonneg d)
    exact_mod_cast Nat.sub_le (d+1) n

/-- Conditional on any finite older history, infinite postponement of the next
renewal has probability zero, proved by stationary cylinder domination. -/
theorem zeros_append_tendsto_zero (μ : Law) (o : List Bool) :
    Tendsto (fun n => blockMass μ (o ++ List.replicate n false)) atTop (𝓝 0) := by
  have hres : Tendsto (fun n => residual μ n / mean μ) atTop (𝓝 0) := by
    simpa using (residual_tendsto_zero μ).div_const (mean μ)
  apply squeeze_zero (fun n => blockMass_nonneg μ _) _ hres
  intro n
  have h := older_component_le μ o.length (List.replicate n false) ⟨o, rfl⟩
  rwa [blockMass_zeros] at h

lemma zeros_extension_step (μ : Law) (o : List Bool) (n : ℕ) :
    blockMass μ (o ++ List.replicate n false) =
      blockMass μ (o ++ List.replicate (n+1) false) +
        blockMass μ ((o ++ List.replicate n false) ++ [true]) := by
  have h := blockMass_right_consistency μ (o ++ List.replicate n false)
  have hz : (o ++ List.replicate n false) ++ [false] = o ++ List.replicate (n+1) false := by
    rw [List.append_assoc]
    congr 1
    simpa using (List.replicate_add n 1 false).symm
  rwa [hz] at h

/-- First-renewal events after any fixed initial zero run exhaust that no-renewal event. -/
theorem hasSum_firstRenewal_after_zeros (μ : Law) (o : List Bool) (n : ℕ) :
    HasSum (fun r => blockMass μ ((o ++ List.replicate (n+r) false) ++ [true]))
      (blockMass μ (o ++ List.replicate n false)) := by
  apply (hasSum_iff_tendsto_nat_of_nonneg (fun r => blockMass_nonneg μ _) _).mpr
  have hsum : ∀ K, (∑ r ∈ range K, blockMass μ ((o ++ List.replicate (n+r) false) ++ [true])) =
      blockMass μ (o ++ List.replicate n false) - blockMass μ (o ++ List.replicate (n+K) false) := by
    intro K
    induction K with
    | zero => simp
    | succ K ih =>
      rw [sum_range_succ, ih]
      have h := zeros_extension_step μ o (n+K)
      rw [Nat.add_succ]
      linarith
  simp_rw [hsum]
  have hadd : Tendsto (fun K : ℕ => n+K) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    exact eventually_atTop.mpr ⟨b, fun K hK => by omega⟩
  simpa using tendsto_const_nhds.sub ((zeros_append_tendsto_zero μ o).comp hadd)


lemma firstOneIndex_lt_length (s : List Bool) (hs : true ∈ s) :
    firstOneIndex s < s.length := by
  induction s with
  | nil => simp at hs
  | cons b s ih =>
    cases b with
    | false =>
      have h := ih (by simpa using hs)
      simpa only [firstOneIndex, List.length_cons, Nat.add_lt_add_iff_right] using h
    | true => simp [firstOneIndex]

/-- The exact unbounded countdown events exhaust each observed cylinder. This
establishes the normalization/marginal condition for the countable joint law,
including all-zero histories and arbitrary finite-mean gap tails. -/
theorem hasSum_countableJointMass (μ : Law) {k t : ℕ} (o : Word k) (s : Word t) (y : Bool) :
    HasSum (fun c : ℕ => countableJointMass μ o s y c)
      (blockMass μ ((o.val ++ s.val) ++ [y])) := by
  by_cases hs : true ∈ s.val
  · let i := firstOneIndex (s.val ++ [y])
    have hi : i ≤ t := by
      have h := firstOneIndex_lt_length s.val hs
      dsimp [i]
      rw [firstOneIndex_visible s.val hs [y] []]
      simpa only [List.append_nil, s.property] using h.le
    have hz : s ≠ zeros t := by
      intro h
      rw [h] at hs
      simp [zeros] at hs
    have heq : (fun c => countableJointMass μ o s y c) =
        (fun c => if c = i then blockMass μ ((o.val ++ s.val) ++ [y]) else 0) := by
      funext c
      by_cases hc : c ≤ t
      · simp [countableJointMass, hc, i, eq_comm]
      · have hci : c ≠ i := by omega
        simp [countableJointMass, hc, hz, hci]
    rw [heq]
    exact hasSum_ite_eq i _
  · have hz : s = zeros t := by
      apply Subtype.ext
      simpa only [zeros, s.property] using no_true_eq_zeros s.val hs
    subst s
    cases y with
    | true =>
      have hi : firstOneIndex ((zeros t).val ++ [true]) = t := by
        simp [zeros, firstOneIndex_zeros_append, firstOneIndex]
      have heq : (fun c => countableJointMass μ o (zeros t) true c) =
          (fun c => if c = t then blockMass μ ((o.val ++ (zeros t).val) ++ [true]) else 0) := by
        funext c
        by_cases hc : c ≤ t
        · simp [countableJointMass, hc, hi, eq_comm]
        · have hct : c ≠ t := by omega
          simp [countableJointMass, hc, hct]
      rw [heq]
      exact hasSum_ite_eq t _
    | false =>
      have hbase := hasSum_firstRenewal_after_zeros μ o.val (t+1)
      have hshift : HasSum (fun r => countableJointMass μ o (zeros t) false (r+(t+1)))
          (blockMass μ (o.val ++ List.replicate (t+1) false)) := by
        convert hbase using 1
        funext r
        have hr : ¬r+(t+1) ≤ t := by omega
        simp [countableJointMass, hr, Nat.add_comm]
      have hfull := hshift.sum_range_add
      have hprefix : (∑ c ∈ range (t+1), countableJointMass μ o (zeros t) false c) = 0 := by
        apply sum_eq_zero
        intro c hc
        have hct : c ≤ t := by have := mem_range.mp hc; omega
        have hne : t+1 ≠ c := by omega
        simp [countableJointMass, hct, zeros, firstOneIndex_zeros_append, firstOneIndex, hne]
      rw [hprefix, zero_add] at hfull
      have hz : ((o.val ++ (zeros t).val) ++ [false]) =
          o.val ++ List.replicate (t+1) false := by
        simp only [zeros, List.append_assoc]
        congr 1
        simpa using (List.replicate_add t 1 false).symm
      rw [hz]
      exact hfull

/-- The countable countdown marginal is the original stationary observed-block law. -/
theorem tsum_countableJointMass (μ : Law) {k t : ℕ} (o : Word k) (s : Word t) (y : Bool) :
    (∑' c : ℕ, countableJointMass μ o s y c) = blockMass μ ((o.val ++ s.val) ++ [y]) :=
  (hasSum_countableJointMass μ o s y).tsum_eq

end Paper37.CountdownRefinement
