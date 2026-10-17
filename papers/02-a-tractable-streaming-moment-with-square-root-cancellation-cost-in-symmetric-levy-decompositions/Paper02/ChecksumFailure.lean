import Paper02.Sampling
import Paper02.SparseRecovery
import Mathlib.Logic.Equiv.Prod

/-!
# Conditioning and union bounds for independently seeded checksums

The hash seed is fixed before the checksum seeds are averaged.  This proves
Appendix A's union bound for the actual Cartesian product seed, without an
assumed conditional-independence or conditional-probability certificate.
-/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Paper02.ChecksumFailure
open Sampling

variable {H Z I A B : Type*}

lemma uniform_expect_equiv [Fintype A] [Nonempty A] [Fintype B] [Nonempty B]
    (e : A ≃ B) (X : B → ℝ) :
    (FiniteLaw.uniform A).expect (fun a => X (e a)) =
      (FiniteLaw.uniform B).expect X := by
  rw [FiniteLaw.uniform_expect, FiniteLaw.uniform_expect,
    e.sum_comp X, Fintype.card_congr e]

lemma uniform_expect_product [Fintype A] [Nonempty A] [Fintype B] [Nonempty B]
    (X : A × B → ℝ) :
    (FiniteLaw.uniform (A × B)).expect X =
      (FiniteLaw.uniform A).expect (fun a =>
        (FiniteLaw.uniform B).expect (fun b => X (a, b))) := by
  simp only [FiniteLaw.uniform_expect, Fintype.sum_prod_type,
    Fintype.card_prod, Nat.cast_mul, ← Finset.sum_div]
  ring

/-- A single coordinate of a uniform vector is uniform.  This is a
consequence of the explicit split-at-coordinate equivalence. -/
lemma uniform_expect_coordinate [Fintype I] [DecidableEq I]
    [Fintype Z] [Nonempty Z] (i : I) (X : Z → ℝ) :
    (FiniteLaw.uniform (I → Z)).expect (fun z => X (z i)) =
      (FiniteLaw.uniform Z).expect X := by
  let e := Equiv.funSplitAt i Z
  calc
    _ = (FiniteLaw.uniform (I → Z)).expect (fun z => X (e z).1) := rfl
    _ = (FiniteLaw.uniform (Z × ({j : I // j ≠ i} → Z))).expect
        (fun z => X z.1) := uniform_expect_equiv e (fun z => X z.1)
    _ = _ := by rw [uniform_expect_product]; simp

/-- The probability of an event at level `i`, averaged over the entire copy
seed, is the average of its fixed-hash checksum probability. -/
lemma conditional_event_probability [Fintype H] [Nonempty H]
    [Fintype I] [DecidableEq I] [Fintype Z] [Nonempty Z]
    (E : H → I → Set Z) (i : I) :
    (FiniteLaw.uniform (H × (I → Z))).prob
      {seed | seed.2 i ∈ E seed.1 i} =
      (FiniteLaw.uniform H).expect (fun h => (FiniteLaw.uniform Z).prob (E h i)) := by
  unfold FiniteLaw.prob
  rw [uniform_expect_product]
  apply (FiniteLaw.uniform H).expect_congr
  intro h
  exact uniform_expect_coordinate i (fun z => if z ∈ E h i then 1 else 0)

/-- Conditioning on an arbitrary hash seed and unioning over all levels.
No independence between the level failure events is required. -/
lemma conditional_event_union_bound [Fintype H] [Nonempty H]
    [Fintype I] [DecidableEq I] [Fintype Z] [Nonempty Z]
    (E : H → I → Set Z) {err : ℝ}
    (hE : ∀ h i, (FiniteLaw.uniform Z).prob (E h i) ≤ err) :
    (FiniteLaw.uniform (H × (I → Z))).prob
      {seed | ∃ i, seed.2 i ∈ E seed.1 i} ≤ Fintype.card I * err := by
  let μ := FiniteLaw.uniform (H × (I → Z))
  have hu := μ.prob_exists_le_sum (Finset.univ : Finset I)
    (fun i => {seed | seed.2 i ∈ E seed.1 i})
  simp only [Finset.mem_univ, true_and] at hu
  apply le_trans hu
  calc
    _ ≤ ∑ _i : I, err := by
      apply Finset.sum_le_sum
      intro i _
      rw [conditional_event_probability]
      calc
        _ ≤ (FiniteLaw.uniform H).expect (fun _ => err) :=
          (FiniteLaw.uniform H).expect_mono (fun h => hE h i)
        _ = err := (FiniteLaw.uniform H).expect_const err
    _ = _ := by simp

/-- Checksum rejection at all dense sampled vectors, in the full copy seed.
The sampled vector may be any function of the hash seed and the level. -/
lemma dense_decoder_union_bound [Fintype H] [Nonempty H]
    [Fintype I] [DecidableEq I] {d q U K : ℕ} [Fact q.Prime]
    (hUq : 2 * U < q) (sample : H → I → Fin d → ℤ)
    (hbound : ∀ h j i, -(U : ℤ) ≤ sample h j i ∧ sample h j i ≤ U) :
    (FiniteLaw.uniform (H × (I → ZMod q))).prob
      {seed | ∃ j, K < (SparseRecovery.integerSupport (sample seed.1 j)).card ∧
        SparseRecovery.decodeSummary (d := d) U K (seed.2 j)
          (SparseRecovery.integerSummary K (seed.2 j) (sample seed.1 j)) ≠ none} ≤
      Fintype.card I * ((d : ℝ) / q) := by
  let E : H → I → Set (ZMod q) := fun h j =>
    {z | K < (SparseRecovery.integerSupport (sample h j)).card ∧
      SparseRecovery.decodeSummary (d := d) U K z
        (SparseRecovery.integerSummary K z (sample h j)) ≠ none}
  apply conditional_event_union_bound E
  intro h j
  by_cases hdense : K < (SparseRecovery.integerSupport (sample h j)).card
  · have hc := SparseRecovery.decodeSummary_dense_probability_le
      hUq (sample h j) (hbound h j) hdense
    rw [FiniteLaw.uniform_prob]
    simpa only [E, Set.mem_setOf_eq, hdense, true_and, ZMod.card] using hc
  · have he : E h j = ∅ := by ext z; simp [E, hdense]
    rw [he, FiniteLaw.uniform_prob]
    simp
    positivity

end Paper02.ChecksumFailure
