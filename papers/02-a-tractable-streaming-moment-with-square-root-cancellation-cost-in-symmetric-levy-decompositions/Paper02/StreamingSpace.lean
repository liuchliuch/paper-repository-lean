import Paper02.Hashing
import Paper02.SparseRecovery
import Paper02.WeightEval
import Mathlib.NumberTheory.Bertrand
import Mathlib.Data.Nat.Log

/-!
# Concrete memory bounds for the bounded-weight turnstile sketch

Every space bound below counts the states of explicit finite registers.  The
read-only incoming update is consumed one binary digit at a time, so its length
never enters a state-cardinality bound.
-/

noncomputable section
set_option maxRecDepth 4000
set_option synthInstance.maxSize 512
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

namespace Paper02.StreamingSpace

open Paper02 SparseRecovery WeightEval

/-- The number of distinct contents fits in a binary memory of this size. -/
def FitsBits (A : Type*) [Fintype A] (b : ℕ) : Prop := Fintype.card A ≤ 2 ^ b

lemma prod_fits {A B : Type*} [Fintype A] [Fintype B] {a b : ℕ}
    (hA : FitsBits A a) (hB : FitsBits B b) : FitsBits (A × B) (a + b) := by
  simpa only [FitsBits, Fintype.card_prod, pow_add] using Nat.mul_le_mul hA hB

lemma array_fits {A : Type*} [Fintype A] {a : ℕ}
    (n : ℕ) (hA : FitsBits A a) : FitsBits (Fin n → A) (n * a) := by
  unfold FitsBits at *
  rw [Fintype.card_fun, Fintype.card_fin, Nat.mul_comm n a, pow_mul]
  exact Nat.pow_le_pow_left hA n

lemma fin_fits (n : ℕ) : FitsBits (Fin n) (registerBits n) := by
  simpa only [FitsBits, Fintype.card_fin] using (lt_two_pow_registerBits n).le

lemma field_fits (q : ℕ) [NeZero q] : FitsBits (ZMod q) (registerBits q) := by
  simpa only [FitsBits, ZMod.card] using (lt_two_pow_registerBits q).le

/-- A single summary stores exactly its `2K` moments and one checksum. -/
lemma summary_card (K q : ℕ) [NeZero q] :
    Fintype.card (Summary K (ZMod q)) = q ^ (2 * K + 1) := by
  simp [Summary, Fintype.card_fun, Fintype.card_prod, ZMod.card, pow_succ]

lemma summary_fits (K q : ℕ) [NeZero q] :
    FitsBits (Summary K (ZMod q)) ((2 * K + 1) * registerBits q) := by
  have h := prod_fits (array_fits (2 * K) (field_fits q)) (field_fits q)
  convert h using 1 <;> ring

/-- All randomness and all maintained summaries of one streaming copy. -/
abbrev OnlineState (J ℓ K q : ℕ) :=
  Hashing.Seed J ℓ × (Fin (J + 1) → ZMod q) ×
    (Fin (J + 1) → Summary K (ZMod q))

def onlineBits (J ℓ K q : ℕ) : ℕ :=
  J * (ℓ + 1) + (J + 1) * (2 * K + 2) * registerBits q

lemma online_card (J ℓ K q : ℕ) [NeZero q] :
    Fintype.card (OnlineState J ℓ K q) =
      2 ^ (J * (ℓ + 1)) * q ^ ((J + 1) * (2 * K + 2)) := by
  unfold OnlineState
  rw [Fintype.card_prod, Fintype.card_prod]
  rw [Hashing.card_seed]
  have hsum : Fintype.card (Fin (J + 1) → Summary K (ZMod q)) =
      (q ^ (2 * K + 1)) ^ (J + 1) := by
    rw [Fintype.card_fun, Fintype.card_fin, summary_card]
  rw [hsum, Fintype.card_fun, Fintype.card_fin, ZMod.card, ← pow_mul, ← pow_add]
  congr 2
  ring

lemma online_fits (J ℓ K q : ℕ) [NeZero q] :
    FitsBits (OnlineState J ℓ K q) (onlineBits J ℓ K q) := by
  have hhash : FitsBits (Hashing.Seed J ℓ) (J * (ℓ + 1)) := by
    rw [FitsBits, Hashing.card_seed]
  have h := prod_fits hhash (prod_fits
    (array_fits (J + 1) (field_fits q))
    (array_fits (J + 1) (summary_fits K q)))
  convert h using 1 <;> simp only [onlineBits] <;> ring

/-- Live decoding registers: an augmented linear system, recurrence coefficients,
`K` candidate index/value slots, scan counters, the witness evaluator, and the
scaled estimate accumulator. Index zero marks an unused candidate slot. -/
abbrev DecoderWorkspace (d U J K q : ℕ) :=
  (Fin K → Fin (K + 1) → ZMod q) ×
  (Fin (K + 1) → ZMod q) ×
  (Fin K → Fin (d + 1) × ZMod q) ×
  (Fin 8 → Fin (d + 2 * K + J + 3)) ×
  WeightEval.ScanState U × Fin (3 * d * 2 ^ J + 1)

def decoderBits (d U J K q : ℕ) : ℕ :=
  K * ((K + 1) * registerBits q) +
  ((K + 1) * registerBits q +
  (K * (registerBits (d + 1) + registerBits q) +
  (8 * registerBits (d + 2 * K + J + 3) +
  (evaluatorBits U + registerBits (3 * d * 2 ^ J + 1)))))

lemma decoder_fits (d U J K q : ℕ) [NeZero q] :
    FitsBits (DecoderWorkspace d U J K q) (decoderBits d U J K q) := by
  exact prod_fits (array_fits K (array_fits (K + 1) (field_fits q)))
    (prod_fits (array_fits (K + 1) (field_fits q))
      (prod_fits (array_fits K (prod_fits (fin_fits (d + 1)) (field_fits q)))
        (prod_fits (array_fits 8 (fin_fits (d + 2 * K + J + 3)))
          (prod_fits (evaluator_space_bound U) (fin_fits (3 * d * 2 ^ J + 1))))))

/-- Sequential decoding shares one workspace across the `J+1` levels. -/
lemma one_copy_fits (d U J ℓ K q : ℕ) [NeZero q] :
    FitsBits (OnlineState J ℓ K q × DecoderWorkspace d U J K q)
      (onlineBits J ℓ K q + decoderBits d U J K q) :=
  prod_fits (online_fits J ℓ K q) (decoder_fits d U J K q)

/-- One-bit Horner transition for an arbitrarily long incoming magnitude. -/
def binaryStep (q : ℕ) (r : ZMod q) (b : Bool) : ZMod q :=
  2 * r + if b then 1 else 0

def natBinaryStep (r : ℕ) (b : Bool) : ℕ := 2 * r + if b then 1 else 0

def binaryValue (bits : List Bool) : ℕ := bits.foldl natBinaryStep 0

def reduceBits (q : ℕ) (bits : List Bool) : ZMod q :=
  bits.foldl (binaryStep q) 0

lemma reduceBits_fold (q : ℕ) (bits : List Bool) (r : ℕ) :
    bits.foldl (binaryStep q) (r : ZMod q) = (bits.foldl natBinaryStep r : ℕ) := by
  induction bits generalizing r with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.foldl_cons]
    have hs : binaryStep q (r : ZMod q) b = (natBinaryStep r b : ℕ) := by
      cases b <;> simp [binaryStep, natBinaryStep]
    rw [hs, ih]

/-- Correct reduction uses one field register independently of input length. -/
lemma reduceBits_correct (q : ℕ) (bits : List Bool) :
    reduceBits q bits = (binaryValue bits : ZMod q) := by
  simpa only [reduceBits, binaryValue, Nat.cast_zero] using reduceBits_fold q bits 0

lemma binaryValue_append (bits : List Bool) (b : Bool) :
    binaryValue (bits ++ [b]) = natBinaryStep (binaryValue bits) b := by
  simp [binaryValue, List.foldl_append]

lemma exists_binary_encoding (n : ℕ) : ∃ bits : List Bool, binaryValue bits = n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n = 0
    · exact ⟨[], hn.symm⟩
    · obtain ⟨bits, hbits⟩ := ih (n / 2) (by omega)
      refine ⟨bits ++ [decide (n % 2 = 1)], ?_⟩
      rw [binaryValue_append, hbits]
      unfold natBinaryStep
      split_ifs with h <;> simp_all <;> omega

/-- The update's sign occupies one bit; its magnitude is read-only input. -/
abbrev UpdateReader (q : ℕ) := Bool × ZMod q

def signedBinaryValue (negative : Bool) (bits : List Bool) : ℤ :=
  if negative then -(binaryValue bits : ℤ) else binaryValue bits

def reduceSignedBits (q : ℕ) (negative : Bool) (bits : List Bool) : ZMod q :=
  if negative then -reduceBits q bits else reduceBits q bits

lemma reduceSignedBits_correct (q : ℕ) (negative : Bool) (bits : List Bool) :
    reduceSignedBits q negative bits = (signedBinaryValue negative bits : ZMod q) := by
  cases negative <;> simp [reduceSignedBits, signedBinaryValue, reduceBits_correct]

/-- Every integer update, without any magnitude promise, has such a read-only
encoding and is reduced correctly by the fixed finite register machine. -/
theorem arbitrary_update_reduction (q : ℕ) (Δ : ℤ) :
    ∃ negative bits, signedBinaryValue negative bits = Δ ∧
      reduceSignedBits q negative bits = (Δ : ZMod q) := by
  cases Δ with
  | ofNat n =>
    obtain ⟨bits, hb⟩ := exists_binary_encoding n
    refine ⟨false, bits, ?_, ?_⟩
    · simp [signedBinaryValue, hb]
    · simp [reduceSignedBits, reduceBits_correct, hb]
  | negSucc n =>
    obtain ⟨bits, hb⟩ := exists_binary_encoding (n + 1)
    refine ⟨true, bits, ?_, ?_⟩
    · simp [signedBinaryValue, hb, Int.negSucc_eq]
    · simp [reduceSignedBits, reduceBits_correct, hb, Int.cast_negSucc]

lemma update_reader_fits (q : ℕ) [NeZero q] :
    FitsBits (UpdateReader q) (1 + registerBits q) := by
  apply prod_fits (a := 1) (b := registerBits q)
  · norm_num [FitsBits]
  · exact field_fits q

/-- Exact choices from Appendix A.2. -/
def levelCount (d : ℕ) : ℕ := Nat.clog 2 d

def binaryColumns (d : ℕ) : ℕ := Nat.clog 2 (d + 1)

def primeThreshold (d U : ℕ) : ℕ := max (2 * U) (64 * d * (levelCount d + 1))

/-- Bertrand supplies the paper's prime, including both necessary injections. -/
theorem exists_streaming_prime (d U : ℕ) (hd : 1 ≤ d) :
    ∃ q : ℕ, q.Prime ∧ primeThreshold d U < q ∧ q ≤ 2 * primeThreshold d U ∧
      d < q ∧ 2 * U < q := by
  have hB : primeThreshold d U ≠ 0 := by
    have hpos : 0 < 64 * d * (levelCount d + 1) := by positivity
    exact ne_of_gt (lt_of_lt_of_le hpos (Nat.le_max_right _ _))
  obtain ⟨q, hq, hlo, hup⟩ := Nat.exists_prime_lt_and_le_two_mul (primeThreshold d U) hB
  refine ⟨q, hq, hlo, hup, ?_, ?_⟩
  · have h := (Nat.le_max_right (2 * U) (64 * d * (levelCount d + 1))).trans_lt hlo
    have hp : 1 ≤ levelCount d + 1 := by omega
    nlinarith
  · exact (Nat.le_max_left (2 * U) (64 * d * (levelCount d + 1))).trans_lt hlo

lemma coordinate_fits_columns (d : ℕ) : d ≤ 2 ^ binaryColumns d := by
  exact (Nat.le_succ d).trans (Nat.le_pow_clog (by norm_num) (d + 1))

lemma levelCount_le_dim (d : ℕ) : levelCount d ≤ d := by
  apply (Nat.clog_le_iff_le_pow (by norm_num)).2
  exact (Nat.lt_two_pow_self (n := d)).le

lemma registerBits_pos (n : ℕ) : 0 < registerBits n := by
  unfold registerBits
  omega

lemma registerBits_le_of_lt_pow {n b : ℕ} (hb : 0 < b) (hn : n < 2 ^ b) :
    registerBits n ≤ b := by
  by_cases h0 : n = 0
  · simp [registerBits, h0]
    omega
  · have h := (Nat.log_lt_iff_lt_pow (by norm_num : 1 < 2) h0).2 hn
    unfold registerBits
    omega

lemma registerBits_mul_le (a b : ℕ) :
    registerBits (a * b) ≤ registerBits a + registerBits b := by
  apply registerBits_le_of_lt_pow (by have := registerBits_pos a; omega)
  rw [pow_add]
  exact (Nat.mul_le_mul_left a (lt_two_pow_registerBits b).le).trans_lt
    (Nat.mul_lt_mul_of_pos_right (lt_two_pow_registerBits a) (by positivity))

lemma registerBits_mono {a b : ℕ} (h : a ≤ b) : registerBits a ≤ registerBits b := by
  exact Nat.add_le_add_right (Nat.log_mono_right h) 1

lemma logarithmic_dimensions (d : ℕ) :
    levelCount d ≤ registerBits (d + 1) ∧ binaryColumns d ≤ registerBits (d + 1) := by
  constructor <;> apply (Nat.clog_le_iff_le_pow (by norm_num : 1 < 2)).2
  · exact (Nat.le_succ d).trans (lt_two_pow_registerBits (d + 1)).le
  · exact (lt_two_pow_registerBits (d + 1)).le

/-- A concrete logarithmic bound on the prime-field register size; no search
history or prime table is retained. -/
theorem prime_registerBits_bound (d U q : ℕ) (hq0 : q ≠ 0)
    (hq : q ≤ 2 * primeThreshold d U) :
    registerBits q ≤ 8 + 2 * registerBits (d + 1) + registerBits (U + 1) := by
  have hJ := levelCount_le_dim d
  have hB : primeThreshold d U ≤ 2 * U + 64 * d * (levelCount d + 1) :=
    max_le (by omega) (by omega)
  have hs : 1 ≤ (d + 1) ^ 2 := by nlinarith
  have hu := Nat.mul_le_mul_right U hs
  have hpoly : q ≤ 256 * (d + 1) ^ 2 * (U + 1) := by
    have hq' : q ≤ 4 * U + 128 * d * (levelCount d + 1) := by nlinarith
    have hscale : d * (levelCount d + 1) ≤ (d + 1) ^ 2 := by nlinarith
    nlinarith
  apply registerBits_le_of_lt_pow (by omega)
  have hd := lt_two_pow_registerBits (d + 1)
  have hU := lt_two_pow_registerBits (U + 1)
  have hsquare : (d + 1) ^ 2 ≤ (2 ^ registerBits (d + 1)) ^ 2 :=
    Nat.pow_le_pow_left hd.le 2
  have hprod : (d + 1) ^ 2 * (U + 1) <
      (2 ^ registerBits (d + 1)) ^ 2 * 2 ^ registerBits (U + 1) :=
    (Nat.mul_lt_mul_of_pos_left hU (by positivity)).trans_le
      (Nat.mul_le_mul_right _ hsquare)
  have hf := Nat.mul_lt_mul_of_pos_left hprod (by norm_num : 0 < 256)
  rw [← Nat.mul_assoc] at hf
  have hg := hpoly.trans_lt hf
  have hp : 256 * ((2 ^ registerBits (d + 1)) ^ 2 * 2 ^ registerBits (U + 1)) =
      2 ^ (8 + 2 * registerBits (d + 1) + registerBits (U + 1)) := by
    rw [← pow_mul]
    rw [show registerBits (d + 1) * 2 = 2 * registerBits (d + 1) by omega]
    rw [pow_add, pow_add]
    norm_num
    ring
  exact hg.trans_eq hp

/-- The online memory is explicitly polynomial in `K`, `log(2d)`, and
`log(2U)` for the prime chosen in Appendix A. -/
theorem onlineBits_polylog (d U K q : ℕ) (hq0 : q ≠ 0)
    (hq : q ≤ 2 * primeThreshold d U) :
    onlineBits (levelCount d) (binaryColumns d) K q ≤
      registerBits (d + 1) * (registerBits (d + 1) + 1) +
      (registerBits (d + 1) + 1) * (2 * K + 2) *
        (8 + 2 * registerBits (d + 1) + registerBits (U + 1)) := by
  unfold onlineBits
  gcongr
  · exact (logarithmic_dimensions d).1
  · exact (logarithmic_dimensions d).2
  · exact (logarithmic_dimensions d).1
  · exact prime_registerBits_bound d U q hq0 hq

lemma scan_counter_bits (d J K : ℕ) :
    registerBits (d + 2 * K + J + 3) ≤ registerBits (d + 1) + 2 * K + J + 4 := by
  calc
    _ ≤ registerBits ((d + 1) * (2 * K + J + 3)) := registerBits_mono (by nlinarith)
    _ ≤ registerBits (d + 1) + registerBits (2 * K + J + 3) := registerBits_mul_le _ _
    _ ≤ _ := by
      unfold registerBits
      have h := Nat.log_le_self 2 (2 * K + J + 3)
      omega

lemma accumulator_bits (d J : ℕ) :
    registerBits (3 * d * 2 ^ J + 1) ≤ J + registerBits (d + 1) + 3 := by
  apply registerBits_le_of_lt_pow (by omega)
  have hd := lt_two_pow_registerBits (d + 1)
  have hp : 0 < 2 ^ J := by positivity
  have hh := Nat.mul_lt_mul_of_pos_right hd hp
  have hbound : 3 * d * 2 ^ J + 1 < 8 * 2 ^ registerBits (d + 1) * 2 ^ J := by
    nlinarith
  convert hbound using 1 <;> simp only [pow_add] <;> ring

lemma evaluatorBits_polylog (U : ℕ) :
    evaluatorBits U ≤ 2 * registerBits (U + 1) + 3 := by
  have h := (registerBits_mono (show U + 2 ≤ 2 * (U + 1) by omega)).trans
    (registerBits_mul_le 2 (U + 1))
  norm_num [registerBits] at h
  unfold evaluatorBits registerBits
  omega

/-- A fully expanded polynomial upper bound for the sequential workspace. -/
theorem decoderBits_polylog (d U K q : ℕ) (hq0 : q ≠ 0)
    (hq : q ≤ 2 * primeThreshold d U) :
    decoderBits d U (levelCount d) K q ≤
      K * ((K + 1) * (8 + 2 * registerBits (d + 1) + registerBits (U + 1))) +
      ((K + 1) * (8 + 2 * registerBits (d + 1) + registerBits (U + 1)) +
      (K * (registerBits (d + 1) + (8 + 2 * registerBits (d + 1) + registerBits (U + 1))) +
      (8 * (2 * registerBits (d + 1) + 2 * K + 4) +
      ((2 * registerBits (U + 1) + 3) + (2 * registerBits (d + 1) + 3))))) := by
  have hcounter := scan_counter_bits d (levelCount d) K
  have hacc := accumulator_bits d (levelCount d)
  have hdim := (logarithmic_dimensions d).1
  have hqbits := prime_registerBits_bound d U q hq0 hq
  unfold decoderBits
  gcongr
  · omega
  · exact evaluatorBits_polylog U
  · omega

/-- An optional candidate slot uses one activity bit in addition to its data. -/
lemma option_fits {A : Type*} [Fintype A] {a : ℕ} (hA : FitsBits A a) :
    FitsBits (Option A) (a + 1) := by
  unfold FitsBits at *
  rw [Fintype.card_option, pow_succ]
  have hp : 0 < 2 ^ a := by positivity
  omega

/-- Exact size of the compact candidate code used by the operational enumerator. -/
lemma compactCandidate_card (d U K : ℕ) :
    Fintype.card (Fin K → Option (Fin d × Fin (2 * U + 1))) =
      (1 + d * (2 * U + 1)) ^ K := by
  simp only [Fintype.card_fun, Fintype.card_option, Fintype.card_prod, Fintype.card_fin]
  congr 1
  omega

/-- Compact candidates require polynomial memory even when their exhaustive
search takes exponential time. -/
lemma compactCandidate_fits (d U K : ℕ) :
    FitsBits (Fin K → Option (Fin d × Fin (2 * U + 1)))
      (K * (registerBits (d + 1) + registerBits (2 * U + 1) + 1)) := by
  apply array_fits K
  apply option_fits
  apply prod_fits
  · simpa only [FitsBits, Fintype.card_fin] using
      (show d ≤ d + 1 by omega).trans (lt_two_pow_registerBits (d + 1)).le
  · exact fin_fits (2 * U + 1)

/-- Includes the terminal value of the exhaustive candidate-search counter. -/
lemma compactCounter_fits (d U K : ℕ) :
    FitsBits (Fin ((1 + d * (2 * U + 1)) ^ K + 1))
      (K * (registerBits (d + 1) + registerBits (2 * U + 1) + 1) + 1) := by
  have h := option_fits (compactCandidate_fits d U K)
  simpa only [FitsBits, Fintype.card_option, compactCandidate_card, Fintype.card_fin] using h

/-- Independent copies retain their online states and final outputs. They
reuse one sequential decoder workspace and one incoming-update reader. -/
abbrev AmplifiedState (d U J ℓ K q R : ℕ) :=
  (Fin R → OnlineState J ℓ K q) ×
  (Fin R → Fin (3 * d * 2 ^ J + 1)) ×
  DecoderWorkspace d U J K q × UpdateReader q

lemma amplified_fits (d U J ℓ K q R : ℕ) [NeZero q] :
    FitsBits (AmplifiedState d U J ℓ K q R)
      (R * onlineBits J ℓ K q +
      (R * registerBits (3 * d * 2 ^ J + 1) +
      (decoderBits d U J K q + (1 + registerBits q)))) :=
  prod_fits (array_fits R (online_fits J ℓ K q))
    (prod_fits (array_fits R (fin_fits (3 * d * 2 ^ J + 1)))
      (prod_fits (decoder_fits d U J K q) (update_reader_fits q)))

end Paper02.StreamingSpace
