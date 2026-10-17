import Paper37.CachedDP
import Paper37.RefinedContinuation

/-! A cache-using executable version of the occupied-type recurrence. The
coefficient caches and observed histogram are shared by every refinement state
and every support-size component extracted from the resulting table. -/
namespace Paper37.CachedRefinedDP
open Finset Paper37.DP Paper37.Envelope Paper37.ContinuationDP
open Paper37.AdaptiveDP Paper37.RefinedContinuation Paper37.CachedDP

private def subIdx {N : ℕ} (k : Fin (N+1)) (b : ℕ) : Fin (N+1) :=
  ⟨k.val-b,lt_of_le_of_lt (Nat.sub_le _ _) k.isLt⟩

/-- Cached recurrence entry. Its summand uses only bounded lookups, guarded
comparisons, additions, subtractions and multiplications. -/
def cachedRefinedEntry (N : ℕ) (c : Cache N) (A : ℕ) (d : Fin N)
    (old : RefinedLayer N) (k u j : Fin (N+1)) : ℕ × ℕ :=
  let ad := c.observed[d.val+1]
  (∑ b ∈ range (k.val+1),
    if (d.val+1)*b≤u.val ∧ (if 0<ad+b then 1 else 0)≤j.val then
      chooseAt c k b * powerAt c (ad+b) *
        (refinedAt old (subIdx k b) (subIdx u ((d.val+1)*b))
          (subIdx j (if 0<ad+b then 1 else 0))).1 else 0,
   ∑ b ∈ range (k.val+1),
    if (d.val+1)*b≤u.val ∧ (if 0<ad+b then 1 else 0)≤j.val then
      chooseAt c k b * powerAt c (ad+b) *
        ((refinedAt old (subIdx k b) (subIdx u ((d.val+1)*b))
            (subIdx j (if 0<ad+b then 1 else 0))).2 +
          (if A<d.val+1 then b else 0) *
            (refinedAt old (subIdx k b) (subIdx u ((d.val+1)*b))
              (subIdx j (if 0<ad+b then 1 else 0))).1) else 0)

private def plainEntry (N : ℕ) (a : ℕ → ℕ) (A d : ℕ) (old : RefinedLayer N)
    (k u j : Fin (N+1)) : ℕ×ℕ :=
    (∑ b ∈ range (k.val+1),
      if (d+1)*b ≤ u.val ∧ (if 0<a (d+1)+b then 1 else 0) ≤ j.val then
        k.val.choose b*(a (d+1)+b)^(a (d+1)+b)*
          (refinedAt old (subIdx k b) (subIdx u ((d+1)*b)) (subIdx j (if 0<a (d+1)+b then 1 else 0))).1 else 0,
     ∑ b ∈ range (k.val+1),
      if (d+1)*b ≤ u.val ∧ (if 0<a (d+1)+b then 1 else 0) ≤ j.val then
        k.val.choose b*(a (d+1)+b)^(a (d+1)+b)*
          ((refinedAt old (subIdx k b) (subIdx u ((d+1)*b)) (subIdx j (if 0<a (d+1)+b then 1 else 0))).2 +
            (if A<d+1 then b else 0)*
              (refinedAt old (subIdx k b) (subIdx u ((d+1)*b)) (subIdx j (if 0<a (d+1)+b then 1 else 0))).1) else 0)


lemma cachedRefinedEntry_correct (N : ℕ) (a : ℕ → ℕ) (A : ℕ) (d : Fin N)
    (old : RefinedLayer N) (k u j : Fin (N+1)) (ha : ∀ i≤N, a i≤N) :
    cachedRefinedEntry N (makeCache N a) A d old k u j =
      plainEntry N a A d.val old k u j := by
  have had : (makeCache N a).observed[d.val+1] = a (d.val+1) := by
    simp [makeCache]
  simp only [cachedRefinedEntry, plainEntry, had]
  apply Prod.ext
  · dsimp only
    apply sum_congr rfl
    intro b hb
    have hbN : b≤N := by have hh := mem_range.mp hb; have hk := k.isLt; omega
    have haN : a (d.val+1)≤N := ha _ (by omega)
    rw [chooseAt_correct N a k b hbN, powerAt_correct N a (a (d.val+1)+b) (by omega)]
  · dsimp only
    apply sum_congr rfl
    intro b hb
    have hbN : b≤N := by have hh := mem_range.mp hb; have hk := k.isLt; omega
    have haN : a (d.val+1)≤N := ha _ (by omega)
    rw [chooseAt_correct N a k b hbN, powerAt_correct N a (a (d.val+1)+b) (by omega)]

def cachedRefinedStep (N : ℕ) (c : Cache N) (A : ℕ) (d : Fin N)
    (old : RefinedLayer N) : RefinedLayer N :=
  Vector.ofFn fun k => Vector.ofFn fun u => Vector.ofFn fun j =>
    cachedRefinedEntry N c A d old k u j

lemma cachedRefinedStep_correct (N : ℕ) (a : ℕ → ℕ) (A : ℕ) (d : Fin N)
    (old : RefinedLayer N) (ha : ∀ i≤N, a i≤N) :
    cachedRefinedStep N (makeCache N a) A d old = refinedStep N a A d.val old := by
  apply Vector.ext
  intro k hk
  apply Vector.ext
  intro u hu
  apply Vector.ext
  intro j hj
  simp only [cachedRefinedStep, refinedStep, Vector.getElem_ofFn]
  change cachedRefinedEntry N (makeCache N a) A d old ⟨k,hk⟩ ⟨u,hu⟩ ⟨j,hj⟩ =
    plainEntry N a A d.val old ⟨k,hk⟩ ⟨u,hu⟩ ⟨j,hj⟩
  exact cachedRefinedEntry_correct N a A d old ⟨k,hk⟩ ⟨u,hu⟩ ⟨j,hj⟩ ha

/-- One cached refinement table, materialized a layer at a time. -/
def cachedRefinedRun (N : ℕ) (c : Cache N) (A : ℕ) : ℕ → RefinedLayer N
  | 0 => Vector.ofFn fun k => Vector.ofFn fun u => Vector.ofFn fun j =>
      (if k.val=0 ∧ u.val=0 ∧ j.val=0 then 1 else 0,0)
  | d+1 => if hd : d<N then
      cachedRefinedStep N c A ⟨d,hd⟩ (cachedRefinedRun N c A d)
    else cachedRefinedRun N c A d

/-- The cache optimization computes exactly the same materialized table. -/
theorem cachedRefinedRun_correct (N : ℕ) (a : ℕ → ℕ) (A d : ℕ) (hd : d≤N)
    (ha : ∀ i≤N, a i≤N) :
    cachedRefinedRun N (makeCache N a) A d = refinedRun N a A d := by
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [cachedRefinedRun, dif_pos (by omega : d<N), ih (by omega),
      cachedRefinedStep_correct N a A ⟨d,by omega⟩ _ ha]
    rfl

/-- The cached all-restrictions query parses and caches coefficients once,
computes one refinement table, and extracts all support restrictions from it. -/
def cachedEvaluateRestrictedAll (H : ℕ) (z : List Bool) (R : ℕ) : Vector ℚ (H+1) :=
  let coeff := makeObservedCache H z
  let table := cachedRefinedRun H coeff (parseAge 0 z) H
  restrictedFromTable H z R table

theorem cachedEvaluateRestrictedAll_eq (H : ℕ) (z : List Bool) (R : ℕ) (hz : z.length≤H) :
    cachedEvaluateRestrictedAll H z R = evaluateRestrictedAll H z R := by
  unfold cachedEvaluateRestrictedAll evaluateRestrictedAll
  dsimp only
  rw [makeObservedCache_eq, cachedRefinedRun_correct H (observedCounts z) (parseAge 0 z) H
    (le_refl H) (observedCounts_le_horizon H z hz)]

theorem cachedEvaluateRestrictedAll_correct (H : ℕ) (z : List Bool) (R : ℕ)
    (hH : z.length+R≤H) (t : Fin (H+1)) :
    (cachedEvaluateRestrictedAll H z R)[t.val] =
      Paper37.Adaptive.restrictedContinuation (z.length+R) t.val z := by
  rw [cachedEvaluateRestrictedAll_eq H z R (by omega)]
  exact evaluateRestrictedAll_correct H z R hH t

end Paper37.CachedRefinedDP
