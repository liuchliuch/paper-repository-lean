import Paper02.EnumeratingDecoder

/-! # Operational checksum of a compact candidate
Every transition performs one field multiplication or one field accumulation.
The exponent counter is bounded by the dimension, so its bit length is logarithmic.
-/
noncomputable section
open scoped BigOperators

namespace Paper02.ChecksumMachine
open CompactCandidates EnumeratingDecoder SparseRecovery

structure State (d K q : ℕ) [NeZero q] where
  slot : Fin (K + 1)
  exponent : Fin (d + 1)
  power : ZMod q
  accumulator : ZMod q
  deriving Fintype

variable {d U K q : ℕ} [Fact q.Prime]

def slotExponent (entry : Option (Fin d × Fin (2 * U + 1))) : ℕ :=
  match entry with
  | none => 0
  | some a => a.1.val + 1

lemma slotExponent_le (entry : Option (Fin d × Fin (2 * U + 1))) : slotExponent entry ≤ d := by
  cases entry with
  | none => simp [slotExponent]
  | some a => have hi := a.1.isLt; simp only [slotExponent]; omega

def step (code : CompactCode d U K) (z : ZMod q) (s : State d K q) : State d K q :=
  if hj : s.slot.val < K then
    if he : s.exponent.val < slotExponent (code ⟨s.slot.val, hj⟩) then
      { s with exponent := ⟨s.exponent.val + 1, by
          have h := slotExponent_le (code ⟨s.slot.val, hj⟩); omega⟩
               power := s.power * z }
    else
      { slot := ⟨s.slot.val + 1, by omega⟩
        exponent := 0
        power := 1
        accumulator := s.accumulator + slotWeight (code ⟨s.slot.val, hj⟩) q * s.power }
  else s

def registers (j e : ℕ) (hj : j ≤ K) (he : e ≤ d) (p a : ZMod q) : State d K q :=
  ⟨⟨j, by omega⟩, ⟨e, by omega⟩, p, a⟩

def Reaches (code : CompactCode d U K) (z : ZMod q) (s t : State d K q) : Prop :=
  Relation.ReflTransGen (fun x y => step code z x = y) s t

lemma powers_reach (code : CompactCode d U K) (z : ZMod q) (j : Fin K) (a : ZMod q)
    (e : ℕ) (he : e ≤ slotExponent (code j)) :
    Reaches code z (registers j.val 0 j.isLt.le (by omega) 1 a)
      (registers j.val e j.isLt.le (he.trans (slotExponent_le (code j))) (z ^ e) a) := by
  induction e with
  | zero => simpa only [pow_zero] using
      (Relation.ReflTransGen.refl : Reaches code z (registers j.val 0 j.isLt.le (by omega) 1 a) _)
  | succ e ih =>
    have he' : e < slotExponent (code j) := by omega
    apply (ih he'.le).tail
    simp [step, registers, j.isLt, he', pow_succ]

lemma slot_reach (code : CompactCode d U K) (z : ZMod q) (j : Fin K) (a : ZMod q) :
    Reaches code z (registers j.val 0 j.isLt.le (by omega) 1 a)
      (registers (j.val + 1) 0 (by omega) (by omega) 1
        (a + slotWeight (code j) q * z ^ slotExponent (code j))) := by
  apply (powers_reach code z j a (slotExponent (code j)) (le_refl _)).tail
  simp [step, registers, j.isLt]

def contribution (code : CompactCode d U K) (z : ZMod q) (j : ℕ) : ZMod q :=
  if hj : j < K then slotWeight (code ⟨j, hj⟩) q * z ^ slotExponent (code ⟨j, hj⟩) else 0

def partialSum (code : CompactCode d U K) (z : ZMod q) (n : ℕ) : ZMod q :=
  ∑ j ∈ Finset.range n, contribution code z j

theorem slots_reach (code : CompactCode d U K) (z : ZMod q) (n : ℕ) (hn : n ≤ K) :
    Reaches code z (registers 0 0 (by omega) (by omega) 1 0)
      (registers n 0 hn (by omega) 1 (partialSum code z n)) := by
  induction n with
  | zero => exact Relation.ReflTransGen.refl
  | succ n ih =>
    have hn' : n < K := by omega
    have hp : partialSum code z (n + 1) = partialSum code z n +
        slotWeight (code ⟨n, hn'⟩) q * z ^ slotExponent (code ⟨n, hn'⟩) := by
      simp [partialSum, Finset.sum_range_succ, contribution, hn']
    rw [hp]
    exact (ih hn'.le).trans (slot_reach code z ⟨n, hn'⟩ (partialSum code z n))

lemma partialSum_all (code : CompactCode d U K) (z : ZMod q) :
    partialSum code z K = ∑ j, slotWeight (code j) q * z ^ slotExponent (code j) := by
  rw [partialSum, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j _
  simp [contribution, j.isLt]

lemma compact_checksum (code : CompactCode d U K) (z : ZMod q) :
    (∑ j, slotWeight (code j) q * z ^ slotExponent (code j)) =
      checksum (fun i => ((candidateValue code i : ℤ) : ZMod q)) z := by
  unfold checksum candidateValue
  simp only [Int.cast_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  cases he : code j with
  | none => simp [slotValue, slotWeight, slotExponent]
  | some a =>
    rw [Finset.sum_eq_single a.1]
    · simp [slotValue, slotWeight, slotExponent]
    · intro i _ hi; simp [slotValue, Ne.symm hi]
    · simp

/-- The stored checksum is obtained by actual bounded-register execution. -/
theorem checker_correct (code : CompactCode d U K) (z : ZMod q) :
    let finish := registers K 0 (le_refl _) (by omega) 1
      (checksum (fun i => ((candidateValue code i : ℤ) : ZMod q)) z)
    Reaches code z (registers 0 0 (by omega) (by omega) 1 0) finish ∧ step code z finish = finish := by
  dsimp only
  constructor
  · simpa only [partialSum_all, compact_checksum] using slots_reach code z K (le_refl _)
  · simp [step, registers]

theorem checker_fits : StreamingSpace.FitsBits (State d K q)
    (WeightEval.registerBits (K + 1) + WeightEval.registerBits (d + 1) +
      2 * WeightEval.registerBits q) := by
  let e : State d K q ≃ Fin (K + 1) × Fin (d + 1) × ZMod q × ZMod q :=
    { toFun := fun s => (s.slot, s.exponent, s.power, s.accumulator)
      invFun := fun s => ⟨s.1, s.2.1, s.2.2.1, s.2.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hh := StreamingSpace.prod_fits (StreamingSpace.fin_fits (K + 1))
    (StreamingSpace.prod_fits (StreamingSpace.fin_fits (d + 1))
      (StreamingSpace.prod_fits (StreamingSpace.field_fits q) (StreamingSpace.field_fits q)))
  unfold StreamingSpace.FitsBits at *
  rw [Fintype.card_congr e]
  convert hh using 1 <;> congr 1 <;> omega

end Paper02.ChecksumMachine
