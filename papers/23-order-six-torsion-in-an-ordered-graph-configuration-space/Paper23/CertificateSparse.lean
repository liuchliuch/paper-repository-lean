import Paper23.CertificateEncoding
import Mathlib.Tactic.Abel

/-! A sparse integer-chain normalizer. Its correctness is proved with respect
to the original cubical Finsupp chain, before any numerical instance is used. -/
namespace Paper23.CertificateChecks
open Cubical CertificateData

/-- Structurally recursive merge. At fuel zero concatenation still preserves
its represented chain; the numerical checker must verify the computed normal
form. Explicit fuel keeps all closed checks reducible by the ordinary kernel. -/
def mergeFuel (fuel : ℕ) (xs ys : List (ℕ × ℤ)) : List (ℕ × ℤ) :=
  Nat.rec (motive := fun _ => List (ℕ × ℤ) → List (ℕ × ℤ) → List (ℕ × ℤ))
    (fun xs ys => xs ++ ys)
    (fun _ rec xs ys => match xs,ys with
      | [],ys => ys
      | xs,[] => xs
      | x :: xs,y :: ys =>
        if x.1 < y.1 then x :: rec xs (y :: ys)
        else if y.1 < x.1 then y :: rec (x :: xs) ys
        else if x.2 + y.2 = 0 then rec xs ys
        else (x.1,x.2+y.2) :: rec xs ys)
    fuel xs ys

theorem codeChain_mergeFuel (fuel : ℕ) (xs ys : List (ℕ × ℤ)) :
    codeChain (mergeFuel fuel xs ys) = codeChain xs + codeChain ys := by
  induction fuel generalizing xs ys with
  | zero => exact codeChain_append xs ys
  | succ fuel ih =>
    simp only [mergeFuel] at ih
    cases xs with
    | nil => simp [mergeFuel]
    | cons x xs =>
      cases ys with
      | nil => simp [mergeFuel]
      | cons y ys =>
        by_cases hxy : x.1 < y.1
        · simp only [mergeFuel, if_pos hxy, codeChain_cons, ih]
          abel
        · by_cases hyx : y.1 < x.1
          · simp only [mergeFuel, if_neg hxy, if_pos hyx, codeChain_cons, ih]
            abel
          · have hk : x.1 = y.1 := by omega
            by_cases hzero : x.2 + y.2 = 0
            · simp only [mergeFuel, if_neg hxy, if_neg hyx, if_pos hzero]
              rw [ih]
              simp only [codeChain_cons, ← hk]
              have hs : x.2 • basis (decodeCube x.1) + y.2 • basis (decodeCube x.1) = 0 := by
                rw [← add_smul, hzero, zero_smul]
              calc
                _ = (x.2 • basis (decodeCube x.1) + y.2 • basis (decodeCube x.1)) +
                    (codeChain xs + codeChain ys) := by rw [hs, zero_add]
                _ = _ := by abel
            · simp only [mergeFuel, if_neg hxy, if_neg hyx, if_neg hzero]
              rw [codeChain_cons, ih]
              simp only [codeChain_cons, ← hk, add_smul]
              abel

/-- Length fuel suffices for merging two sparse lists. Preservation does not
require sortedness, a uniqueness invariant, or any unchecked external result. -/
def merge (xs ys : List (ℕ × ℤ)) : List (ℕ × ℤ) :=
  mergeFuel (xs.length + ys.length) xs ys

theorem codeChain_merge (xs ys : List (ℕ × ℤ)) :
    codeChain (merge xs ys) = codeChain xs + codeChain ys :=
  codeChain_mergeFuel _ xs ys

/-- One level of a balanced merge tree. -/
def mergePass (xs : List (List (ℕ × ℤ))) : List (List (ℕ × ℤ)) :=
  (List.rec (motive := fun _ => List (List (ℕ × ℤ)) × List (List (ℕ × ℤ)))
    ([],[])
    (fun a tail state =>
      ((match tail with | [] => [a] | b :: _ => merge a b :: state.2),state.1)) xs).1

noncomputable def chunkChain (xss : List (List (ℕ × ℤ))) : RawChain :=
  (xss.map codeChain).sum

theorem chunkChain_mergePass (xss : List (List (ℕ × ℤ))) :
    chunkChain (mergePass xss) = chunkChain xss := by
  induction xss using List.twoStepInduction with
  | nil => rfl
  | singleton a => rfl
  | cons_cons a b rest ih _ =>
    change codeChain (merge a b) + chunkChain (mergePass rest) =
      codeChain a + (codeChain b + chunkChain rest)
    rw [codeChain_merge, ih]
    abel

/-- Fuel bounds the number of merge levels; at a singleton the process stops.
Any fuel value preserves the represented chain. -/
def collapse (fuel : ℕ) (xs : List (List (ℕ × ℤ))) : List (List (ℕ × ℤ)) :=
  Nat.rec (motive := fun _ => List (List (ℕ × ℤ)) → List (List (ℕ × ℤ)))
    (fun xs => xs)
    (fun _ rec xs => match xs with
      | [] => []
      | [x] => [x]
      | xs => rec (mergePass xs)) fuel xs

theorem chunkChain_collapse (n : ℕ) (xss : List (List (ℕ × ℤ))) :
    chunkChain (collapse n xss) = chunkChain xss := by
  induction n generalizing xss with
  | zero => rfl
  | succ n ih =>
    match xss with
    | [] => rfl
    | [x] => rfl
    | a :: b :: rest =>
      change chunkChain (collapse n (mergePass (a :: b :: rest))) = _
      rw [ih, chunkChain_mergePass]

/-- Two actual endpoint faces in increasing-moving-edge orientation. -/
def codeFace (t : FaceData) : List (ℕ × ℤ) :=
  let s := movingSign t.edge (t.pre ++ t.post)
  [(encodeCube t.upper, s), (encodeCube t.lower, -s)]

theorem codeChain_codeFace (t : FaceData) (hlen : t.cube.length = 4) :
    codeChain (codeFace t) = t.movingTerm := by
  have hu : t.upper.length = 4 := by
    simpa [FaceData.upper, FaceData.cube] using hlen
  have hl : t.lower.length = 4 := by
    simpa [FaceData.lower, FaceData.cube] using hlen
  simp only [codeFace, codeChain_cons, codeChain_nil, decodeCube_encodeCube _ hu,
    decodeCube_encodeCube _ hl]
  simp [FaceData.movingTerm, sub_eq_add_neg]

/-- Direct endpoint expansion of one decoded labelled cube. -/
def codeBoundary (k : ℕ) : List (ℕ × ℤ) :=
  (faces (decodeCube k)).flatMap codeFace

theorem codeChain_codeBoundary (k : ℕ)
    (hc : (decodeCube k).Pairwise ClosureDisjoint) :
    codeChain (codeBoundary k) = boundary (basis (decodeCube k)) := by
  rw [codeBoundary, codeChain_flatMap, boundary_basis_eq_moving_faces _ hc]
  apply congrArg List.sum
  apply List.map_congr_left
  intro t ht
  apply codeChain_codeFace
  rw [faces_spec ht]
  rfl

def scaleEntries (a : ℤ) (xs : List (ℕ × ℤ)) : List (ℕ × ℤ) :=
  xs.map (fun p => (p.1, a*p.2))

theorem codeChain_scaleEntries (a : ℤ) (xs : List (ℕ × ℤ)) :
    codeChain (scaleEntries a xs) = a • codeChain xs := by
  induction xs with
  | nil => simp [scaleEntries]
  | cons p xs ih =>
    change (a * p.2) • basis (decodeCube p.1) + codeChain (scaleEntries a xs) =
      a • (p.2 • basis (decodeCube p.1) + codeChain xs)
    rw [ih, smul_add, mul_smul]

/-- Endpoint differential on the sparse code representation. -/
def codeDifferential (xs : List (ℕ × ℤ)) : List (ℕ × ℤ) :=
  xs.flatMap (fun p => scaleEntries p.2 (codeBoundary p.1))

theorem codeChain_codeDifferential (xs : List (ℕ × ℤ))
    (h : ∀ p ∈ xs, (decodeCube p.1).Pairwise ClosureDisjoint) :
    codeChain (codeDifferential xs) = boundary (codeChain xs) := by
  induction xs with
  | nil => simp [codeDifferential]
  | cons p xs ih =>
    have hp := h p (by simp)
    have ht : ∀ p ∈ xs, (decodeCube p.1).Pairwise ClosureDisjoint := by
      intro p hp
      exact h p (by simp [hp])
    simp only [codeDifferential, List.flatMap_cons, codeChain_append]
    rw [codeChain_scaleEntries, codeChain_codeBoundary _ hp]
    change p.2 • boundary (basis (decodeCube p.1)) + codeChain (codeDifferential xs) = _
    rw [ih ht, codeChain_cons, map_add, map_smul]

theorem chunkChain_singletons (xs : List (ℕ × ℤ)) :
    chunkChain (xs.map (fun p => [p])) = codeChain xs := by
  induction xs with
  | nil => simp [chunkChain]
  | cons p xs ih =>
    simp only [List.map_cons, chunkChain, List.map_cons, List.sum_cons,
      codeChain_cons, codeChain_nil, add_zero] at ih ⊢
    rw [ih]

/-- Any kernel-checked result of the merge normalizer denotes the same actual
cubical chain. This is the soundness theorem for generated sparse checks. -/
theorem normalization_sound (fuel : ℕ) (xs ys : List (ℕ × ℤ))
    (checked : collapse fuel (xs.map (fun p => [p])) = [ys]) :
    codeChain ys = codeChain xs := by
  have h := chunkChain_collapse fuel (xs.map (fun p => [p]))
  rw [checked, chunkChain_singletons] at h
  simpa [chunkChain] using h

/-- In particular, an empty normalized endpoint expansion proves an actual
boundary is zero. The finite equality premise is what numerical certificates
must discharge by kernel computation. -/
theorem boundary_zero_of_checked (fuel : ℕ) (xs : List (ℕ × ℤ))
    (valid : ∀ p ∈ xs, (decodeCube p.1).Pairwise ClosureDisjoint)
    (checked : collapse fuel ((codeDifferential xs).map (fun p => [p])) = [[]]) :
    boundary (codeChain xs) = 0 := by
  have h := normalization_sound fuel (codeDifferential xs) [] checked
  rw [codeChain_codeDifferential _ valid] at h
  exact h.symm

end Paper23.CertificateChecks
