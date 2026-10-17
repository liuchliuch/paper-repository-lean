import Paper23.CertificateBucketMerge

/-!
# Bridges from literal buckets to existing sparse certificate blocks

These lemmas combine independently checked small unpacking equalities.
They do not execute `packBuckets`, inspect bucket labels, or impose any
sortedness condition on the original coordinate entries.
-/
namespace Paper23.CertificateChecks
open Cubical

/-- Forget bucket labels and concatenate the sparse entries in bucket order. -/
def unpackBuckets (bs : BucketVector) : List (ℕ × ℤ) := bs.flatMap Prod.snd

@[simp] theorem unpackBuckets_nil : unpackBuckets [] = [] := rfl

@[simp] theorem unpackBuckets_cons (b : ℕ × List (ℕ × ℤ)) (bs : BucketVector) :
    unpackBuckets (b :: bs) = b.2 ++ unpackBuckets bs := rfl

@[simp] theorem unpackBuckets_append (xs ys : BucketVector) :
    unpackBuckets (xs ++ ys) = unpackBuckets xs ++ unpackBuckets ys := by
  simp [unpackBuckets]

/-- Literal bucket entries represent exactly their concatenated original chain. -/
theorem bucketChain_eq_codeChain_unpackBuckets (bs : BucketVector) :
    bucketChain bs = codeChain (unpackBuckets bs) :=
  (codeChain_flatMap bs Prod.snd).symm

/-- A small checked unpacking equality immediately gives equality of actual chains. -/
theorem bucketChain_of_unpack_eq (bs : BucketVector) (xs : List (ℕ × ℤ))
    (checked : unpackBuckets bs = xs) : bucketChain bs = codeChain xs := by
  rw [bucketChain_eq_codeChain_unpackBuckets, checked]

/-- Integer chain semantics of concatenated existing sparse blocks. -/
theorem codeChain_flatten (parts : List (List (ℕ × ℤ))) :
    codeChain parts.flatten = (parts.map codeChain).sum := by
  induction parts with
  | nil => rfl
  | cons xs parts ih =>
    simp only [List.flatten_cons, codeChain_append, List.map_cons, List.sum_cons, ih]

/-- Concatenating literal bucket blocks adds their original integer chains. -/
theorem bucketChain_flatten (parts : List BucketVector) :
    bucketChain parts.flatten = (parts.map bucketChain).sum := by
  induction parts with
  | nil => rfl
  | cons bs parts ih =>
    simp only [List.flatten_cons, bucketChain_append, List.map_cons, List.sum_cons, ih]

/-- The corresponding generic list-sum formula for indexed bucket blocks. -/
theorem bucketChain_flatMap {α : Type*} (indices : List α) (f : α → BucketVector) :
    bucketChain (indices.flatMap f) = (indices.map fun i => bucketChain (f i)).sum := by
  induction indices with
  | nil => rfl
  | cons i indices ih =>
    simp only [List.flatMap_cons, bucketChain_append, List.map_cons, List.sum_cons, ih]

/-- Unpacking commutes with concatenation of bucket blocks. -/
theorem unpackBuckets_flatten (parts : List BucketVector) :
    unpackBuckets parts.flatten = (parts.map unpackBuckets).flatten := by
  induction parts with
  | nil => rfl
  | cons bs parts ih =>
    simp only [List.flatten_cons, unpackBuckets_append, List.map_cons, ih]

/-- One equality of the list of small unpacked blocks suffices for the full chain. -/
theorem bucketChain_flatten_of_unpack_parts_eq (bs : List BucketVector)
    (parts : List (List (ℕ × ℤ))) (checked : bs.map unpackBuckets = parts) :
    bucketChain bs.flatten = codeChain parts.flatten := by
  rw [bucketChain_eq_codeChain_unpackBuckets, unpackBuckets_flatten, checked]

/-- Combine small blockwise chain certificates without constructing a packed vector. -/
theorem bucketChain_flatMap_of_chain_eq {α : Type*} (indices : List α)
    (bs : α → BucketVector) (parts : α → List (ℕ × ℤ))
    (checked : ∀ i ∈ indices, bucketChain (bs i) = codeChain (parts i)) :
    bucketChain (indices.flatMap bs) = codeChain (indices.flatMap parts) := by
  rw [bucketChain_flatMap, codeChain_flatMap]
  exact congrArg List.sum (List.map_congr_left checked)

/-- Indexed wrapper for independently kernel-checked unpacking equalities. -/
theorem bucketChain_flatMap_of_unpack_eq {α : Type*} (indices : List α)
    (bs : α → BucketVector) (parts : α → List (ℕ × ℤ))
    (checked : ∀ i ∈ indices, unpackBuckets (bs i) = parts i) :
    bucketChain (indices.flatMap bs) = codeChain (indices.flatMap parts) := by
  apply bucketChain_flatMap_of_chain_eq
  intro i hi
  exact bucketChain_of_unpack_eq (bs i) (parts i) (checked i hi)

/-- A list of small unpacking proofs combines directly via `List.Forall₂`.
The number of blocks is arbitrary, including a generated list of 256 blocks. -/
theorem bucketChain_flatten_of_forall₂_unpack
    {bs : List BucketVector} {parts : List (List (ℕ × ℤ))}
    (checked : List.Forall₂ (fun b xs => unpackBuckets b = xs) bs parts) :
    bucketChain bs.flatten = codeChain parts.flatten := by
  induction checked with
  | nil => rfl
  | cons hhead htail ih =>
    simp only [List.flatten_cons, bucketChain_append, codeChain_append]
    rw [bucketChain_eq_codeChain_unpackBuckets, hhead, ih]

/-- The same block bridge expressed in the existing `chunkChain` sum semantics.
This form lets callers keep the original sparse pieces as separate constants. -/
theorem bucketChain_flatten_eq_chunkChain_of_forall₂_unpack
    {bs : List BucketVector} {parts : List (List (ℕ × ℤ))}
    (checked : List.Forall₂ (fun b xs => unpackBuckets b = xs) bs parts) :
    bucketChain bs.flatten = chunkChain parts :=
  (bucketChain_flatten_of_forall₂_unpack checked).trans (codeChain_flatten parts)

/-- Apply a literal-bucket bridge after coefficientwise reduction modulo six. -/
theorem reduce_bucketChain_of_unpack_eq (bs : BucketVector) (xs : List (ℕ × ℤ))
    (checked : unpackBuckets bs = xs) :
    reduceChain (bucketChain bs) = reduceChain (codeChain xs) :=
  congrArg reduceChain (bucketChain_of_unpack_eq bs xs checked)

/-- Blockwise modular bridge with no large packing computation. -/
theorem reduce_bucketChain_flatten_of_forall₂_unpack
    {bs : List BucketVector} {parts : List (List (ℕ × ℤ))}
    (checked : List.Forall₂ (fun b xs => unpackBuckets b = xs) bs parts) :
    reduceChain (bucketChain bs.flatten) = reduceChain (chunkChain parts) :=
  congrArg reduceChain (bucketChain_flatten_eq_chunkChain_of_forall₂_unpack checked)

end Paper23.CertificateChecks
