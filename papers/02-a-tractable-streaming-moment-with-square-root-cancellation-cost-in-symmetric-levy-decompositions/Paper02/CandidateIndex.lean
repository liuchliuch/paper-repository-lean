import Paper02.CompactCandidates
import Mathlib.Algebra.BigOperators.Fin

/-! # Arithmetic indexing of bounded sparse candidates

The finite counter is decoded by repeated quotient and remainder.  No abstract
choice of a finite-type enumeration is used by the decoding function.
-/
namespace Paper02.CandidateIndex

open CompactCandidates

def base (d U : ℕ) : ℕ := 1 + d * (2 * U + 1)

lemma base_pos (d U : ℕ) : 0 < base d U := by unfold base; omega

/-- Digit zero is an inactive slot. Every other digit contains its coordinate
quotient and bounded-frequency remainder. -/
def slotDecode {d U : ℕ} (digit : Fin (base d U)) : Option (Fin d × Fin (2 * U + 1)) :=
  if h : digit.val = 0 then none else
    some (⟨(digit.val - 1) / (2 * U + 1), by
      apply (Nat.div_lt_iff_lt_mul (by omega : 0 < 2 * U + 1)).2
      have hd := digit.isLt
      unfold base at hd
      omega⟩,
      ⟨(digit.val - 1) % (2 * U + 1), Nat.mod_lt _ (by omega)⟩)

/-- Arithmetic rank of a single slot. -/
def slotEncode {d U : ℕ} : Option (Fin d × Fin (2 * U + 1)) → Fin (base d U)
  | none => ⟨0, base_pos d U⟩
  | some (i, a) => ⟨1 + (a.val + (2 * U + 1) * i.val), by
      have hi := i.isLt
      have ha := a.isLt
      unfold base
      nlinarith⟩

@[simp] lemma slotDecode_slotEncode {d U : ℕ} (entry : Option (Fin d × Fin (2 * U + 1))) :
    slotDecode (slotEncode entry) = entry := by
  cases entry with
  | none => simp [slotEncode, slotDecode]
  | some entry =>
    rcases entry with ⟨i, a⟩
    have ha := a.isLt
    have hv : 0 < 2 * U + 1 := by omega
    simp only [slotEncode, slotDecode]
    rw [dif_neg (by omega)]
    congr 1
    apply Prod.ext <;> apply Fin.ext
    · simp only [Nat.add_sub_cancel_left]
      rw [Nat.add_mul_div_left _ _ hv, Nat.div_eq_of_lt ha]
      omega
    · simp only [Nat.add_sub_cancel_left]
      simpa [Nat.add_mod, Nat.mul_mod] using Nat.mod_eq_of_lt ha

/-- The explicit digit at slot `j`. -/
def digit {d U K : ℕ} (n : Fin ((base d U) ^ K)) (j : Fin K) : Fin (base d U) :=
  ⟨n.val / (base d U) ^ j.val % base d U, Nat.mod_lt _ (base_pos d U)⟩

/-- Numeric counter to compact candidate, using only quotient and remainder. -/
def unrank {d U K : ℕ} (n : Fin ((base d U) ^ K)) : CompactCode d U K :=
  fun j => slotDecode (digit n j)

@[simp] lemma unrank_apply {d U K : ℕ} (n : Fin ((base d U) ^ K)) (j : Fin K) :
    unrank n j = slotDecode ⟨n.val / (base d U) ^ j.val % base d U,
      Nat.mod_lt _ (base_pos d U)⟩ := rfl

/-- The arithmetic rank is the usual finite base expansion. -/
def rank {d U K : ℕ} (code : CompactCode d U K) : Fin ((base d U) ^ K) :=
  finFunctionFinEquiv (fun j => slotEncode (code j))

lemma digit_rank {d U K : ℕ} (code : CompactCode d U K) (j : Fin K) :
    digit (rank code) j = slotEncode (code j) := by
  have h := congrFun (finFunctionFinEquiv.symm_apply_apply (fun j => slotEncode (code j))) j
  exact h

@[simp] theorem unrank_rank {d U K : ℕ} (code : CompactCode d U K) :
    unrank (rank code) = code := by
  funext j
  change slotDecode (digit (rank code) j) = code j
  rw [digit_rank, slotDecode_slotEncode]

/-- Every compact candidate is reached by the actual finite arithmetic counter. -/
theorem unrank_surjective (d U K : ℕ) : Function.Surjective (unrank (d := d) (U := U) (K := K)) :=
  fun code => ⟨rank code, unrank_rank code⟩

end Paper02.CandidateIndex
