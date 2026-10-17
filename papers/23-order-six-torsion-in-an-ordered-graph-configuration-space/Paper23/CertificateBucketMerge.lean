import Paper23.CertificateModulo

/-!
# Sparse certificate normalization in bounded coordinate buckets

Bucket labels guide executable merging but do not enter the represented chain.
All preservation theorems therefore hold without assumptions on labels,
sortedness, or uniqueness.  Packing uses a tail-recursive left fold and then
reverses the outer and inner accumulation orders.
-/
namespace Paper23.CertificateChecks
open Cubical

/-- A bucket label together with its sparse integer entries. -/
abbrev BucketVector := List (ℕ × List (ℕ × ℤ))

/-- The original-coordinate integer chain represented by all buckets.
The outer natural-number labels have no semantic role. -/
noncomputable def bucketChain (bs : BucketVector) : RawChain :=
  (bs.map fun b => codeChain b.2).sum

@[simp] theorem bucketChain_nil : bucketChain [] = 0 := rfl

@[simp] theorem bucketChain_cons (b : ℕ × List (ℕ × ℤ)) (bs : BucketVector) :
    bucketChain (b :: bs) = codeChain b.2 + bucketChain bs := rfl

@[simp] theorem bucketChain_append (xs ys : BucketVector) :
    bucketChain (xs ++ ys) = bucketChain xs + bucketChain ys := by
  simp [bucketChain]

/-- Reversing sparse entries does not change the commutative integer chain. -/
theorem codeChain_reverse (xs : List (ℕ × ℤ)) : codeChain xs.reverse = codeChain xs := by
  simp [codeChain]

/-- Reversing buckets does not change their represented chain. -/
theorem bucketChain_reverse (bs : BucketVector) : bucketChain bs.reverse = bucketChain bs := by
  simp [bucketChain]

/-- Reversing each bucket's entries also leaves its chain unchanged. -/
theorem bucketChain_reverse_inner (bs : BucketVector) :
    bucketChain (bs.map fun b => (b.1,b.2.reverse)) = bucketChain bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.map_cons, bucketChain_cons, codeChain_reverse, ih]

/-- Prepend one entry to the current bucket when its label agrees, otherwise
start a new bucket.  The accumulator stores both orders in reverse. -/
def push (acc : BucketVector) (p : ℕ × ℤ) : BucketVector :=
  match acc with
  | [] => [(p.1 / 5041,[p])]
  | (k,ys) :: rest =>
    if p.1 / 5041 = k then (k,p :: ys) :: rest
    else (p.1 / 5041,[p]) :: acc

/-- One tail-recursive accumulation step adds precisely the new original entry. -/
theorem bucketChain_push (acc : BucketVector) (p : ℕ × ℤ) :
    bucketChain (push acc p) = p.2 • basis (decodeCube p.1) + bucketChain acc := by
  cases acc with
  | nil => simp [push]
  | cons b bs =>
    rcases b with ⟨k,ys⟩
    by_cases h : p.1 / 5041 = k <;> simp [push,h,add_assoc]

/-- The fold invariant does not require contiguous or correctly labelled groups. -/
theorem bucketChain_foldl_push (xs : List (ℕ × ℤ)) (acc : BucketVector) :
    bucketChain (xs.foldl push acc) = codeChain xs + bucketChain acc := by
  induction xs generalizing acc with
  | nil => simp
  | cons p xs ih =>
    rw [List.foldl_cons, ih, bucketChain_push, codeChain_cons]
    abel

/-- Group adjacent entries by the quotient of their coordinate code by 5041.
For sorted sparse input, this retains the input's outer and inner order. -/
def packBuckets (xs : List (ℕ × ℤ)) : BucketVector :=
  (xs.foldl push []).reverse.map fun b => (b.1,b.2.reverse)

/-- Packing changes only the finite expression for the original integer chain. -/
theorem bucketChain_packBuckets (xs : List (ℕ × ℤ)) :
    bucketChain (packBuckets xs) = codeChain xs := by
  rw [packBuckets, bucketChain_reverse_inner, bucketChain_reverse, bucketChain_foldl_push]
  simp

/-- Merge outer buckets using bounded fuel, merging entries only for equal
bucket labels.  At zero fuel concatenation still preserves chain semantics. -/
def mergeBucketsFuel (fuel : ℕ) (xs ys : BucketVector) : BucketVector :=
  Nat.rec (motive := fun _ => BucketVector → BucketVector → BucketVector)
    (fun xs ys => xs ++ ys)
    (fun _ rec xs ys => match xs,ys with
      | [],ys => ys
      | xs,[] => xs
      | x :: xs,y :: ys =>
        if x.1 < y.1 then x :: rec xs (y :: ys)
        else if y.1 < x.1 then y :: rec (x :: xs) ys
        else if merge x.2 y.2 = [] then rec xs ys
        else (x.1,merge x.2 y.2) :: rec xs ys)
    fuel xs ys

/-- The outer merge adds the original integer chains, even for arbitrary labels. -/
theorem bucketChain_mergeBucketsFuel (fuel : ℕ) (xs ys : BucketVector) :
    bucketChain (mergeBucketsFuel fuel xs ys) = bucketChain xs + bucketChain ys := by
  induction fuel generalizing xs ys with
  | zero => exact bucketChain_append xs ys
  | succ fuel ih =>
    simp only [mergeBucketsFuel] at ih
    cases xs with
    | nil => simp [mergeBucketsFuel]
    | cons x xs =>
      cases ys with
      | nil => simp [mergeBucketsFuel]
      | cons y ys =>
        by_cases hxy : x.1 < y.1
        · simp only [mergeBucketsFuel, if_pos hxy, bucketChain_cons, ih]
          abel
        · by_cases hyx : y.1 < x.1
          · simp only [mergeBucketsFuel, if_neg hxy, if_pos hyx, bucketChain_cons, ih]
            abel
          · by_cases hzero : merge x.2 y.2 = []
            · have hz : codeChain x.2 + codeChain y.2 = 0 := by
                rw [← codeChain_merge, hzero, codeChain_nil]
              simp only [mergeBucketsFuel, if_neg hxy, if_neg hyx, if_pos hzero, ih,
                bucketChain_cons]
              calc
                _ = (codeChain x.2 + codeChain y.2) +
                    (bucketChain xs + bucketChain ys) := by rw [hz,zero_add]
                _ = _ := by abel
            · simp only [mergeBucketsFuel, if_neg hxy, if_neg hyx, if_neg hzero,
                bucketChain_cons, codeChain_merge, ih]
              abel

/-- The executable outer merge uses only the lengths of the much smaller
bucket lists; each inner call is the already certified sparse merge. -/
def mergeBuckets (xs ys : BucketVector) : BucketVector :=
  mergeBucketsFuel (xs.length + ys.length) xs ys

/-- Bucket merging preserves the sum in the original cubical chain group. -/
theorem bucketChain_mergeBuckets (xs ys : BucketVector) :
    bucketChain (mergeBuckets xs ys) = bucketChain xs + bucketChain ys :=
  bucketChain_mergeBucketsFuel _ xs ys

/-- Reduce each bucket modulo six, dropping empty buckets. -/
def modularBuckets (bs : BucketVector) : BucketVector :=
  List.rec [] (fun b _ rec =>
    if reduceEntries b.2 = [] then rec else (b.1,reduceEntries b.2) :: rec) bs

/-- Bucketwise reduction preserves the reduced original-coordinate chain. -/
theorem modularBuckets_sound (bs : BucketVector) :
    reduceChain (bucketChain (modularBuckets bs)) = reduceChain (bucketChain bs) := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    simp only [modularBuckets] at ih
    rcases b with ⟨k,xs⟩
    by_cases h : reduceEntries xs = []
    · have hz : reduceChain (codeChain xs) = 0 := by
        rw [← reduceEntries_sound xs, h, codeChain_nil, map_zero]
      simp only [modularBuckets, if_pos h, bucketChain_cons, map_add, ih, hz, zero_add]
    · simp only [modularBuckets, if_neg h, bucketChain_cons, map_add, reduceEntries_sound, ih]

/-- Merge the small outer lists and then reduce each individual bucket. -/
def modularMergeBuckets (xs ys : BucketVector) : BucketVector :=
  modularBuckets (mergeBuckets xs ys)

/-- Bucket normalization proves the same addition identity modulo six in the
original cubical chain group. -/
theorem modularMergeBuckets_sound (xs ys : BucketVector) :
    reduceChain (bucketChain (modularMergeBuckets xs ys)) =
      reduceChain (bucketChain xs) + reduceChain (bucketChain ys) := by
  rw [modularMergeBuckets, modularBuckets_sound, bucketChain_mergeBuckets, map_add]

end Paper23.CertificateChecks
