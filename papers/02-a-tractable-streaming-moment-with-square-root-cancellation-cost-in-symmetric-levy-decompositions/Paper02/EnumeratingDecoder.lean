import Paper02.MomentMachine
import Paper02.CompactCandidates
import Paper02.Streaming

/-! # Bounded-register candidate checks for the exhaustive decoder

The compact code is retained while two explicit loops check distinct indices
and stored moments.  Neither loop constructs a dimension-sized integer vector.
-/
noncomputable section
open scoped BigOperators

namespace Paper02.EnumeratingDecoder

open CompactCandidates SparseRecovery

structure BooleanState (N : ℕ) where
  index : Fin (N + 1)
  good : Bool
  deriving Fintype, DecidableEq

def booleanStep {N : ℕ} (test : Fin N → Bool) (s : BooleanState N) : BooleanState N :=
  if h : s.index.val < N then
    ⟨⟨s.index.val + 1, by omega⟩, s.good && test ⟨s.index.val, h⟩⟩ else s

def booleanPrefix {N : ℕ} (test : Fin N → Bool) (n : ℕ) : Bool :=
  decide (∀ i : Fin N, i.val < n → test i = true)

lemma booleanPrefix_succ {N : ℕ} (test : Fin N → Bool) (n : ℕ) (hn : n < N) :
    booleanPrefix test (n + 1) = (booleanPrefix test n && test ⟨n, hn⟩) := by
  apply Bool.eq_iff_iff.mpr
  simp only [booleanPrefix, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · intro h
    exact ⟨fun i hi => h i (by omega), h ⟨n, hn⟩ (by simp)⟩
  · rintro ⟨h, he⟩ i hi
    by_cases hin : i.val < n
    · exact h i hin
    · have heq : i = ⟨n, hn⟩ := Fin.ext (by dsimp only; omega)
      simpa [heq] using he

theorem boolean_reaches {N : ℕ} (test : Fin N → Bool) (n : ℕ) (hn : n ≤ N) :
    Relation.ReflTransGen (fun x y => booleanStep test x = y)
      ⟨0, true⟩ ⟨⟨n, by omega⟩, booleanPrefix test n⟩ := by
  induction n with
  | zero => simpa [booleanPrefix] using
      (Relation.ReflTransGen.refl : Relation.ReflTransGen (fun x y => booleanStep test x = y)
        (⟨0, true⟩ : BooleanState N) _)
  | succ n ih =>
    have hnt : n < N := by omega
    apply (ih hnt.le).trans
    apply Relation.ReflTransGen.single
    simp only [booleanStep, dif_pos hnt]
    congr 1
    exact (booleanPrefix_succ test n hnt).symm

theorem boolean_checker_correct {N : ℕ} (test : Fin N → Bool) :
    let finish : BooleanState N := ⟨⟨N, by omega⟩, booleanPrefix test N⟩
    Relation.ReflTransGen (fun x y => booleanStep test x = y) ⟨0, true⟩ finish ∧
      booleanStep test finish = finish ∧
      (finish.good = true ↔ ∀ i, test i = true) := by
  dsimp only
  refine ⟨boolean_reaches test N (le_refl _), ?_, ?_⟩
  · simp [booleanStep]
  · simp [booleanPrefix]

/-- A pair of slots is compatible if either is unused or their coordinates
are distinct, with the diagonal pair allowed. -/
def compatible {d U K : ℕ} (code : CompactCode d U K) (j k : Fin K) : Bool :=
  if j = k then true else
    match code j, code k with
    | some a, some b => decide (a.1 ≠ b.1)
    | _, _ => true

/-- The actual double loop uses quotient and remainder of a `K²` counter. -/
def compatibilityTest {d U K : ℕ} (code : CompactCode d U K) (n : Fin (K * K)) : Bool :=
  compatible code n.divNat n.modNat

lemma compatibility_test_iff {d U K : ℕ} (code : CompactCode d U K) :
    (∀ n, compatibilityTest code n = true) ↔ ∀ j k, compatible code j k = true := by
  constructor
  · intro h j k
    have hh := h (finProdFinEquiv (j, k))
    change compatible code (finProdFinEquiv.symm (finProdFinEquiv (j, k))).1
      (finProdFinEquiv.symm (finProdFinEquiv (j, k))).2 = true at hh
    simpa only [Equiv.symm_apply_apply] using hh
  · intro h n
    exact h n.divNat n.modNat

def slotNode {d U : ℕ} (entry : Option (Fin d × Fin (2 * U + 1))) (q : ℕ) : ZMod q :=
  match entry with
  | none => 0
  | some a => (a.1.val + 1 : ℕ)

def slotWeight {d U : ℕ} (entry : Option (Fin d × Fin (2 * U + 1))) (q : ℕ) : ZMod q :=
  match entry with
  | none => 0
  | some a => (integerValue a.2 : ℤ)

/-- Summing compact slot contributions is exactly the stored integer power
moment, even for codes that will later be rejected for duplicate indices. -/
theorem slots_moment {d U K q : ℕ} [Fact q.Prime] (code : CompactCode d U K) (t : ℕ) :
    (∑ j, slotWeight (code j) q * slotNode (code j) q ^ t) =
      powerMoment (fun i : Fin d => ((i.val + 1 : ℕ) : ZMod q))
        (fun i => ((candidateValue code i : ℤ) : ZMod q)) t := by
  unfold powerMoment candidateValue
  simp only [Int.cast_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  cases he : code j with
  | none => simp [slotValue, slotWeight, slotNode]
  | some a =>
    rw [Finset.sum_eq_single a.1]
    · simp [slotValue, slotWeight, slotNode]
    · intro i _ hi
      simp [slotValue, Ne.symm hi]
    · simp

/-- This links the operational checker to the canonical candidate condition's
actual stored power moments. -/
theorem compact_moment_checker_correct {d U K q : ℕ} [Fact q.Prime]
    (code : CompactCode d U K) (M : Fin (2 * K) → ZMod q) :
    let nodes := fun j => slotNode (code j) q
    let weights := fun j => slotWeight (code j) q
    let finish := MomentMachine.registers (2 * K) 0 0 (le_refl _) (by omega) (by omega) 1 0
      (MomentMachine.goodPrefix nodes weights M (2 * K))
    MomentMachine.Reaches nodes weights M
      (MomentMachine.registers 0 0 0 (by omega) (by omega) (by omega) 1 0 true) finish ∧
      (finish.good = true ↔ integerMoments (q := q) K (candidateValue code) = M) := by
  dsimp only
  have hm := MomentMachine.checker_correct
    (fun j => slotNode (code j) q) (fun j => slotWeight (code j) q) M
  refine ⟨hm.1, hm.2.2.trans ?_⟩
  simp only [slots_moment]
  change (∀ t : Fin (2 * K), integerMoments K (candidateValue code) t = M t) ↔ _
  exact ⟨fun h => funext h, fun h => congrFun h⟩

/-- The scan's actual state needs only its counter and one flag. -/
theorem boolean_space_bound (N : ℕ) :
    Fintype.card (BooleanState N) ≤ 2 ^ (WeightEval.registerBits (N + 1) + 1) := by
  let e : BooleanState N ≃ Fin (N + 1) × Bool :=
    { toFun := fun s => (s.index, s.good)
      invFun := fun s => ⟨s.1, s.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Fintype.card_congr e]
  simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool, pow_succ]
  exact Nat.mul_le_mul_right 2 (WeightEval.lt_two_pow_registerBits (N + 1)).le


lemma compatible_all_iff {d U K : ℕ} (code : CompactCode d U K) :
    (∀ j k, compatible code j k = true) ↔
      ∀ (j k : Fin K) (a b : Fin d × Fin (2 * U + 1)),
        code j = some a → code k = some b → a.1 = b.1 → j = k := by
  constructor
  · intro h j k a b hja hkb hab
    by_contra hjk
    have ht := h j k
    simp [compatible, hjk, hja, hkb, hab] at ht
  · intro h j k
    by_cases hjk : j = k
    · simp [compatible, hjk]
    · cases hja : code j with
      | none => simp [compatible, hjk, hja]
      | some a =>
        cases hkb : code k with
        | none => simp [compatible, hjk, hja, hkb]
        | some b =>
          have hab : a.1 ≠ b.1 := fun he => hjk (h j k a b hja hkb he)
          simp [compatible, hjk, hja, hkb, hab]

/-- A compact code is a candidate exactly when its coordinate check and actual
moment check both accept. -/
def Pass {d U K q : ℕ} [Fact q.Prime] (M : Fin (2 * K) → ZMod q)
    (code : CompactCode d U K) : Prop :=
  (∀ j k, compatible code j k = true) ∧ integerMoments K (candidateValue code) = M

lemma pass_is_candidate {d U K q : ℕ} [Fact q.Prime]
    (M : Fin (2 * K) → ZMod q) (code : CompactCode d U K) (h : Pass M code) :
    IntegerCandidate U K M (candidateValue code) := by
  refine ⟨candidateValue_bounded code ((compatible_all_iff code).mp h.1),
    candidateValue_sparse code, ?_⟩
  intro t
  exact congrFun h.2 t

lemma candidate_has_passing_code {d U K q : ℕ} [Fact q.Prime]
    (M : Fin (2 * K) → ZMod q) (v : Fin d → ℤ) (hv : IntegerCandidate U K M v) :
    ∃ code : CompactCode d U K, Pass M code ∧ candidateValue code = v := by
  refine ⟨encode v hv.1, ?_, candidateValue_encode v hv.1 hv.2.1⟩
  constructor
  · apply (compatible_all_iff _).mpr
    intro j k a b hj hk hi
    exact encode_coordinate_injective v hv.1 hj hk hi
  · rw [candidateValue_encode v hv.1 hv.2.1]
    exact funext hv.2.2

end Paper02.EnumeratingDecoder
