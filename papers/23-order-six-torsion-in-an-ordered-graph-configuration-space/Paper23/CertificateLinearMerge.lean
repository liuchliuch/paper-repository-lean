import Paper23.CertificateModulo

/-!
# A structurally recursive sparse merge

The outer recursion is on the first list.  For one fixed head, `mergeHead`
recurses only on the second list and receives the outer recursive result as
a function.  Neither recursion computes a length, carries fuel, or invokes
a well-founded recursion package.  The correctness theorem is about the
original integer cubical chain, with no sortedness assumptions.
-/
namespace Paper23.CertificateChecks
open Cubical

/-- Merge one fixed first-list head, recursively consuming the second list. -/
def mergeHead (x : ℕ × ℤ) (xs : List (ℕ × ℤ))
    (rec : List (ℕ × ℤ) → List (ℕ × ℤ)) (ys : List (ℕ × ℤ)) : List (ℕ × ℤ) :=
  List.rec (x :: xs) (fun y ys ih =>
    if x.1 < y.1 then x :: rec (y :: ys)
    else if y.1 < x.1 then y :: ih
    else if x.2 + y.2 = 0 then rec ys
    else (x.1,x.2+y.2) :: rec ys) ys

/-- The inner structural recursion preserves the original-coordinate chain,
provided the supplied outer recursive function has its inductive semantics. -/
theorem codeChain_mergeHead (x : ℕ × ℤ) (xs : List (ℕ × ℤ))
    (rec : List (ℕ × ℤ) → List (ℕ × ℤ))
    (hrec : ∀ ys, codeChain (rec ys) = codeChain xs + codeChain ys)
    (ys : List (ℕ × ℤ)) :
    codeChain (mergeHead x xs rec ys) = codeChain (x :: xs) + codeChain ys := by
  induction ys with
  | nil => simp [mergeHead]
  | cons y ys ih =>
    simp only [mergeHead] at ih
    by_cases hxy : x.1 < y.1
    · simp only [mergeHead, if_pos hxy, codeChain_cons, hrec]
      abel
    · by_cases hyx : y.1 < x.1
      · simp only [mergeHead, if_neg hxy, if_pos hyx, codeChain_cons, ih]
        abel
      · have hk : x.1 = y.1 := by omega
        by_cases hzero : x.2 + y.2 = 0
        · simp only [mergeHead, if_neg hxy, if_neg hyx, if_pos hzero]
          rw [hrec]
          simp only [codeChain_cons, ← hk]
          have hs : x.2 • basis (decodeCube x.1) + y.2 • basis (decodeCube x.1) = 0 := by
            rw [← add_smul, hzero, zero_smul]
          calc
            _ = (x.2 • basis (decodeCube x.1) + y.2 • basis (decodeCube x.1)) +
                (codeChain xs + codeChain ys) := by rw [hs, zero_add]
            _ = _ := by abel
        · simp only [mergeHead, if_neg hxy, if_neg hyx, if_neg hzero]
          rw [codeChain_cons, hrec]
          simp only [codeChain_cons, ← hk, add_smul]
          abel

/-- Sparse merge defined directly by the structural list recursor.
At a nonempty first list, the recursive function on its tail is passed to
`mergeHead`; this avoids both repeated lengths and a fuel argument. -/
def linearMerge (xs : List (ℕ × ℤ)) : List (ℕ × ℤ) → List (ℕ × ℤ) :=
  List.rec (fun ys => ys) (fun x xs rec ys => mergeHead x xs rec ys) xs

@[simp] theorem linearMerge_nil (ys : List (ℕ × ℤ)) : linearMerge [] ys = ys := rfl

@[simp] theorem linearMerge_cons (x : ℕ × ℤ) (xs ys : List (ℕ × ℤ)) :
    linearMerge (x :: xs) ys = mergeHead x xs (linearMerge xs) ys := rfl

/-- Every structural merge denotes the sum of the two original integer chains. -/
theorem codeChain_linearMerge (xs ys : List (ℕ × ℤ)) :
    codeChain (linearMerge xs ys) = codeChain xs + codeChain ys := by
  induction xs generalizing ys with
  | nil => simp
  | cons x xs ih =>
    exact codeChain_mergeHead x xs (linearMerge xs) ih ys

/-- Structural sparse merge followed by canonical coefficient reduction modulo six. -/
def linearModularMerge (xs ys : List (ℕ × ℤ)) : List (ℕ × ℤ) :=
  reduceEntries (linearMerge xs ys)

/-- The new executable modular merge has the same original-chain semantics
as addition after coefficientwise reduction modulo six. -/
theorem linearModularMerge_sound (xs ys : List (ℕ × ℤ)) :
    reduceChain (codeChain (linearModularMerge xs ys)) =
      reduceChain (codeChain xs) + reduceChain (codeChain ys) := by
  rw [linearModularMerge, reduceEntries_sound, codeChain_linearMerge, map_add]

end Paper23.CertificateChecks
