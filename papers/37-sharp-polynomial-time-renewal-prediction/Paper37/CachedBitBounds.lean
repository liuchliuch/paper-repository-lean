import Paper37.CachedOperations

/-! Binary lengths of the actual caches and cached DP, together with the
explicit scalar interface for a generic quadratic-cost integer simulation.
No polynomial-time property of this predictor is assumed. -/
namespace Paper37.CachedBitBounds
open Finset Paper37.DP Paper37.ContinuationDP Paper37.Envelope
open Paper37.CachedDP Paper37.CachedOperations

lemma observedCounts_total (N : ℕ) (z : List Bool) (hz : z.length≤N) :
    (gapSet N).sum (observedCounts z) = (parseGaps 0 z).length := by
  have hh := sum_count_of_support ((parseGaps 0 z).map Nat.succ) (gapSet N) (observed_support z N hz)
  simpa [observedCounts] using hh

lemma observedCounts_sum_le (N : ℕ) (z : List Bool) (d : ℕ) (hd : d≤N) (hz : z.length≤N) :
    (gapSet d).sum (observedCounts z) ≤ N := by
  calc
    _ ≤ (gapSet N).sum (observedCounts z) := sum_le_sum_of_subset (gapSet_mono hd)
    _ = (parseGaps 0 z).length := observedCounts_total N z hz
    _ ≤ N := (parseGaps_length_le 0 z).trans hz

/-- The cached-run bit bound now has only actual source prefix/horizon inputs. -/
theorem cachedRun_binarySize_source (N : ℕ) (z : List Bool) (A d : ℕ)
    (k u : Fin (N+1)) (hN : 0<N) (hd : d≤N) (hz : z.length≤N) :
    ((cachedRun N (makeObservedCache N z) A d)[k.val][u.val]).1.size ≤ (4*N)*(2*N).size+1 ∧
    ((cachedRun N (makeObservedCache N z) A d)[k.val][u.val]).2.size ≤ (4*N+1)*(2*N).size+1 :=
  cachedRun_binarySize N z A d k u hN hd hz (observedCounts_sum_le N z d hd hz)

/-- Every intermediate partial power in cache construction, not just its last
value, has the stated bit bound. -/
lemma linearPower_binarySize (N c m : ℕ) (hm : m≤c) (hc : c≤N) :
    (linearPower c m).size ≤ N*N.size+1 := by
  rw [linearPower_correct]
  apply binarySize_le_of_le_pow
  by_cases hN : N=0
  · subst N
    have hcz : c=0 := by omega
    have hmz : m=0 := by omega
    subst c
    subst m
    rfl
  · exact (Nat.pow_le_pow_left hc m).trans (Nat.pow_le_pow_right (by omega) (hm.trans hc))

/-- Literal binary payload of all three coefficient/count cache arrays. -/
def cacheBinarySize {N : ℕ} (c : Cache N) : ℕ :=
  (∑ k : Fin (N+1), ∑ b : Fin (N+1), (c.choose[k.val][b.val]).size) +
    (∑ v : Fin (2*N+1), (c.power[v.val]).size) +
    ∑ d : Fin (N+1), (c.observed[d.val]).size

lemma cacheBinarySize_le (N : ℕ) (z : List Bool) (hz : z.length≤N) :
    cacheBinarySize (makeObservedCache N z) ≤
      (N+1)^3 + (2*N+1)*(2*N*(2*N).size+1) + (N+1)*N.size := by
  rw [makeObservedCache_eq]
  unfold cacheBinarySize
  apply Nat.add_le_add
  · apply Nat.add_le_add
    · calc
        _ ≤ ∑ _k : Fin (N+1), ∑ _b : Fin (N+1), (N+1) := by
          apply sum_le_sum
          intro k hk
          apply sum_le_sum
          intro b hb
          simp only [makeCache,chooseCache_correct]
          exact choose_binarySize N k.val b.val (by omega)
        _ = _ := by simp [pow_succ, Nat.mul_assoc]
    · calc
        _ ≤ ∑ _v : Fin (2*N+1), (2*N*(2*N).size+1) := by
          apply sum_le_sum
          intro v hv
          simp only [makeCache,powerCache_correct]
          exact selfPower_binarySize (2*N) v.val (by omega)
        _ = _ := by simp
  · calc
      _ ≤ ∑ _d : Fin (N+1), N.size := by
        apply sum_le_sum
        intro d hd
        simp only [makeCache,Vector.getElem_ofFn]
        exact Nat.size_le_size (observedCounts_le_horizon N z hz d.val (by omega))
      _ = _ := by simp

/-- A generic schoolbook arithmetic-to-machine simulation may use this bound.
Its only external premise concerns *all* integer primitives of a given bit
length; it says nothing about this predictor's complexity. -/
theorem quadratic_simulation_budget (N W C K B work : ℕ)
    (primitiveCost : ℕ → ℕ)
    (hprimitive : ∀ b, primitiveCost b ≤ K*(b+1)^2)
    (hwork : work≤W*(N+1)^5)
    (hbits : B≤C*(N+1)^3*N.size) :
    work*primitiveCost B ≤
      K*W*(C+1)^2*(N+1)^11*(N.size+1)^2 := by
  have hone : 1≤(N+1)^3*(N.size+1) := by
    have hh : 0<(N+1)^3*(N.size+1) := by positivity
    omega
  have hsmall : C*(N+1)^3*N.size ≤ C*(N+1)^3*(N.size+1) :=
    Nat.mul_le_mul_left _ (Nat.le_succ _)
  have hb : B+1≤(C+1)*(N+1)^3*(N.size+1) := by nlinarith
  calc
    _ ≤ (W*(N+1)^5)*(K*(B+1)^2) := Nat.mul_le_mul hwork (hprimitive B)
    _ ≤ (W*(N+1)^5)*(K*((C+1)*(N+1)^3*(N.size+1))^2) := by
      exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hb _))
    _ = _ := by ring

end Paper37.CachedBitBounds
