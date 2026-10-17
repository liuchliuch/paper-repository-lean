import Paper37.ContinuationDP
import Paper37.DPBounds

/-! Explicit finite coefficient caches for the executable ordinary renewal DP.
Pascal coefficients and self-powers are built once. Every recurrence summand
then reads the caches and the preceding materialized layer. -/
namespace Paper37.CachedDP
open Finset Paper37.DP Paper37.ContinuationDP Paper37.Envelope

/-- A truncated Pascal row, generated using additions and previous-row lookups. -/
def pascalRow (N : ℕ) : ℕ → Vector ℕ (N+1)
  | 0 => Vector.ofFn fun b => if b.val=0 then 1 else 0
  | k+1 =>
    let old := pascalRow N k
    Vector.ofFn fun b => old[b.val] +
      if hb : 0<b.val then old[b.val-1]'(by omega) else 0

lemma pascalRow_correct (N k : ℕ) (b : Fin (N+1)) :
    (pascalRow N k)[b.val] = k.choose b.val := by
  induction k generalizing b with
  | zero =>
    simp only [pascalRow,Vector.getElem_ofFn]
    cases hb : b.val with
    | zero => simp
    | succ c => simp
  | succ k ih =>
    simp only [pascalRow,Vector.getElem_ofFn]
    rw [ih]
    by_cases hb : b.val=0
    · simp [hb]
    · have hp : 0<b.val := by omega
      rw [dif_pos hp]
      rw [ih ⟨b.val-1,by omega⟩]
      change k.choose b.val+k.choose (b.val-1)=(k+1).choose b.val
      have he : b.val=(b.val-1)+1 := by omega
      rw [he,Nat.choose_succ_succ]
      simp only [Nat.add_sub_cancel]
      ring

/-- Materialized Pascal coefficients `0≤b,k≤N`. Each row is independently
produced by Pascal's recurrence, so this simple preprocessing is cubic. -/
def chooseCache (N : ℕ) : Vector (Vector ℕ (N+1)) (N+1) :=
  Vector.ofFn fun k => pascalRow N k.val

lemma chooseCache_correct (N : ℕ) (k b : Fin (N+1)) :
    (chooseCache N)[k.val][b.val] = k.val.choose b.val := by
  simp only [chooseCache,Vector.getElem_ofFn,pascalRow_correct]

/-- Linear repeated multiplication, including `0^0=1`. -/
def linearPower (c : ℕ) : ℕ → ℕ
  | 0 => 1
  | m+1 => c*linearPower c m

lemma linearPower_correct (c m : ℕ) : linearPower c m = c^m := by
  induction m with
  | zero => rfl
  | succ m ih => rw [linearPower,ih,pow_succ]; ring

/-- Self-power values cover even infeasible table states: `a_d+b≤2N`. -/
def powerCache (N : ℕ) : Vector ℕ (2*N+1) :=
  Vector.ofFn fun c => linearPower c.val c.val

lemma powerCache_correct (N : ℕ) (c : Fin (2*N+1)) :
    (powerCache N)[c.val] = c.val^c.val := by
  simp only [powerCache,Vector.getElem_ofFn,linearPower_correct]

/-- All values needed by one query. -/
structure Cache (N : ℕ) where
  choose : Vector (Vector ℕ (N+1)) (N+1)
  power : Vector ℕ (2*N+1)
  observed : Vector ℕ (N+1)

def makeCache (N : ℕ) (a : ℕ → ℕ) : Cache N :=
  ⟨chooseCache N,powerCache N,Vector.ofFn fun d => a d.val⟩

/-- Source observed counts are parsed once and stored as one finite vector. -/
def makeObservedCache (N : ℕ) (z : List Bool) : Cache N :=
  let gaps := (parseGaps 0 z).map Nat.succ
  ⟨chooseCache N,powerCache N,Vector.ofFn fun d => gaps.count d.val⟩

lemma makeObservedCache_eq (N : ℕ) (z : List Bool) :
    makeObservedCache N z = makeCache N (observedCounts z) := rfl

def chooseAt {N : ℕ} (c : Cache N) (k : Fin (N+1)) (b : ℕ) : ℕ :=
  if hb : b<N+1 then c.choose[k.val][b] else 0

def powerAt {N : ℕ} (c : Cache N) (v : ℕ) : ℕ :=
  if hv : v<2*N+1 then c.power[v] else 0

lemma chooseAt_correct (N : ℕ) (a : ℕ → ℕ) (k : Fin (N+1)) (b : ℕ) (hb : b≤N) :
    chooseAt (makeCache N a) k b = k.val.choose b := by
  simp only [chooseAt,dif_pos (by omega : b<N+1),makeCache]
  exact chooseCache_correct N k ⟨b,by omega⟩

lemma powerAt_correct (N : ℕ) (a : ℕ → ℕ) (v : ℕ) (hv : v≤2*N) :
    powerAt (makeCache N a) v = v^v := by
  simp only [powerAt,dif_pos (by omega : v<2*N+1),makeCache]
  exact powerCache_correct N ⟨v,by omega⟩

private def subIdx {N : ℕ} (k : Fin (N+1)) (b : ℕ) : Fin (N+1) :=
  ⟨k.val-b,lt_of_le_of_lt (Nat.sub_le _ _) k.isLt⟩

/-- One cached layer: no choose computation, exponentiation or prefix scan
occurs inside either bounded sum. -/
def cachedStep (N : ℕ) (c : Cache N) (A : ℕ) (d : Fin N) (old : Layer N) : Layer N :=
  let ad := c.observed[d.val+1]
  Vector.ofFn fun k => Vector.ofFn fun u =>
    (∑ b ∈ range (min k.val (u.val/(d.val+1))+1),
      chooseAt c k b * powerAt c (ad+b) *
        (old[(subIdx k b).val][(subIdx u ((d.val+1)*b)).val]).1,
     ∑ b ∈ range (min k.val (u.val/(d.val+1))+1),
      chooseAt c k b * powerAt c (ad+b) *
        ((old[(subIdx k b).val][(subIdx u ((d.val+1)*b)).val]).2 +
          (if A<d.val+1 then b else 0)*
            (old[(subIdx k b).val][(subIdx u ((d.val+1)*b)).val]).1))

lemma cachedStep_correct (N : ℕ) (a : ℕ → ℕ) (A : ℕ) (d : Fin N) (old : Layer N)
    (ha : ∀ i≤N, a i≤N) :
    cachedStep N (makeCache N a) A d old = step N a A d.val old := by
  apply Vector.ext
  intro k hk
  apply Vector.ext
  intro u hu
  simp only [cachedStep,step,makeCache,Vector.getElem_ofFn]
  apply Prod.ext
  · dsimp only
    apply sum_congr rfl
    intro b hb
    have hbk := min_le_left k (u/(d.val+1))
    have hb' := mem_range.mp hb
    have hbN : b≤N := by omega
    have ha' : a (d.val+1)≤N := ha _ (by omega)
    have hch := chooseAt_correct N a ⟨k,hk⟩ b hbN
    have hp := powerAt_correct N a (a (d.val+1)+b) (by omega)
    dsimp only [makeCache] at hch hp
    rw [hch,hp]
    rfl
  · dsimp only
    apply sum_congr rfl
    intro b hb
    have hbk := min_le_left k (u/(d.val+1))
    have hb' := mem_range.mp hb
    have hbN : b≤N := by omega
    have ha' : a (d.val+1)≤N := ha _ (by omega)
    have hch := chooseAt_correct N a ⟨k,hk⟩ b hbN
    have hp := powerAt_correct N a (a (d.val+1)+b) (by omega)
    dsimp only [makeCache] at hch hp
    rw [hch,hp]
    rfl

/-- Cached finite DP; its out-of-horizon extension leaves the last layer alone. -/
def cachedRun (N : ℕ) (c : Cache N) (A : ℕ) : ℕ → Layer N
  | 0 => Vector.ofFn fun k => Vector.ofFn fun u => (if k.val=0 ∧ u.val=0 then 1 else 0,0)
  | d+1 => if hd : d<N then cachedStep N c A ⟨d,hd⟩ (cachedRun N c A d) else cachedRun N c A d

/-- Cached evaluation computes the original independent DP values exactly. -/
theorem cachedRun_correct (N : ℕ) (a : ℕ → ℕ) (A d : ℕ) (hd : d≤N)
    (ha : ∀ i≤N, a i≤N) : cachedRun N (makeCache N a) A d = run N a A d := by
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [cachedRun,dif_pos (by omega : d<N),ih (by omega),cachedStep_correct N a A ⟨d,by omega⟩ _ ha]
    rfl

lemma parseGaps_length_le (a : ℕ) (z : List Bool) : (parseGaps a z).length ≤ z.length := by
  induction z generalizing a with
  | nil => simp [parseGaps]
  | cons b z ih => cases b <;> simp [parseGaps] <;> have hh := ih a <;> have hh' := ih (a+1) <;> have hh0 := ih 0 <;> omega

lemma observedCounts_le_horizon (N : ℕ) (z : List Bool) (hz : z.length≤N) :
    ∀ i≤N, observedCounts z i≤N := by
  intro i hi
  unfold observedCounts
  exact (List.count_le_length).trans (by simpa using (parseGaps_length_le 0 z).trans hz)

/-- The source query uses one parsed histogram and one coefficient cache. -/
def cachedEvaluateContinuation (H : ℕ) (z : List Bool) (R : ℕ) : ℚ :=
  let A := parseAge 0 z
  let r := (parseGaps 0 z).length
  let T := A+R
  let coeff := makeObservedCache H z
  let table := cachedRun H coeff A H
  histogramMass H z 0 +
    ∑ k ∈ Icc 1 T, ∑ u ∈ Icc k T,
      (((layerAt table k u).2/k:ℕ):ℚ) / ((r+k:ℕ):ℚ)^(r+k)

/-- The cache-using executable query returns the exact exhaustive source sum. -/
theorem cachedEvaluateContinuation_correct (H : ℕ) (z : List Bool) (R : ℕ)
    (hH : z.length+R≤H) :
    cachedEvaluateContinuation H z R = Paper37.Prediction.continuationMass (z.length+R) z := by
  rw [← evaluateContinuation_correct H z R hH]
  unfold cachedEvaluateContinuation evaluateContinuation
  dsimp only
  rw [makeObservedCache_eq,cachedRun_correct H (observedCounts z) (parseAge 0 z) H (le_refl H)
    (observedCounts_le_horizon H z (by omega))]

/-- Exact number of additions performed by the Pascal-row builder. -/
def pascalAdds (N : ℕ) : ℕ → ℕ
  | 0 => 0
  | k+1 => pascalAdds N k+(N+1)

lemma pascalAdds_eq (N k : ℕ) : pascalAdds N k = k*(N+1) := by
  induction k with
  | zero => simp [pascalAdds]
  | succ k ih => simp [pascalAdds,ih,Nat.add_mul]

/-- The sum of the row builders' addition counts, including deliberate row
recomputation used by the executable choose cache. -/
def chooseCacheAdds (N : ℕ) : ℕ := ∑ k : Fin (N+1), pascalAdds N k.val

lemma chooseCacheAdds_le (N : ℕ) : chooseCacheAdds N ≤ (N+1)^3 := by
  unfold chooseCacheAdds
  calc
    _ ≤ ∑ _k : Fin (N+1), (N+1)^2 := by
      apply sum_le_sum
      intro k hk
      rw [pascalAdds_eq,pow_two]
      exact Nat.mul_le_mul_right _ (by omega)
    _ = _ := by simp [pow_succ]; ring

/-- The literal multiplication-recursion count of the self-power builders. -/
def powerCacheMuls (N : ℕ) : ℕ := ∑ c : Fin (2*N+1), c.val

lemma powerCacheMuls_le (N : ℕ) : powerCacheMuls N ≤ (2*N+1)^2 := by
  unfold powerCacheMuls
  calc
    _ ≤ ∑ _c : Fin (2*N+1), (2*N+1) := by
      apply sum_le_sum
      intro c hc
      omega
    _ = _ := by simp [pow_two]

/-- Equality-comparison count of caching every source histogram coordinate
by one traversal of the already parsed gap list. -/
def observedCacheComparisons (N : ℕ) (z : List Bool) : ℕ :=
  (N+1)*(parseGaps 0 z).length

lemma observedCacheComparisons_le (N : ℕ) (z : List Bool) (hz : z.length≤N) :
    observedCacheComparisons N z ≤ (N+1)^2 := by
  unfold observedCacheComparisons
  rw [pow_two]
  exact Nat.mul_le_mul_left _ ((parseGaps_length_le 0 z).trans (hz.trans (Nat.le_succ N)))

/-- All cached values used by a query have the bit bounds of the previously
proved integer estimates. -/
theorem cachedRun_binarySize (N : ℕ) (z : List Bool) (A d : ℕ)
    (k u : Fin (N+1)) (hN : 0<N) (hd : d≤N) (hz : z.length≤N)
    (ha : (gapSet d).sum (observedCounts z)≤N) :
    ((cachedRun N (makeObservedCache N z) A d)[k.val][u.val]).1.size ≤ (4*N)*(2*N).size+1 ∧
    ((cachedRun N (makeObservedCache N z) A d)[k.val][u.val]).2.size ≤ (4*N+1)*(2*N).size+1 := by
  rw [makeObservedCache_eq,cachedRun_correct N (observedCounts z) A d hd (observedCounts_le_horizon N z hz)]
  exact run_binarySize N (observedCounts z) A d k u hN hd ha

end Paper37.CachedDP
