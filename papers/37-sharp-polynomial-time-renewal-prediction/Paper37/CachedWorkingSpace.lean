import Paper37.CachedCorePolynomial

namespace Paper37.CachedCoreProgram
open Paper37.BoundedLoop Paper37.CachedDP Paper37.DP

lemma size_two_mul_le (N : ℕ) : (2*N).size≤N.size+1 := by
  apply Nat.size_le.mpr
  rw [pow_succ]
  have hh := Nat.lt_size_self N
  omega

/-- The native array frame retains the sharper cubic times binary-width
bound, although the generic compiler is allowed a coarser polynomial peak. -/
theorem sourceFrameBound_binary (N : ℕ) :
    sourceFrameBound N≤100*(N+1)^3*(N.size+1) := by
  have hs := size_two_mul_le N
  have hsm := Nat.mul_le_mul_left (10*(N+1)^3) hs
  have hn : 1≤N.size+1 := by omega
  have hnm := Nat.mul_le_mul_left (50*(N+1)^3) hn
  unfold sourceFrameBound layerSizeBound sourceWidth chooseSizeBound
  nlinarith [Nat.zero_le (N^3),Nat.zero_le (N^3*N.size)]

/-- Exact bit payload of the two actual materialized layers and the three
shared coefficient/histogram caches, including array delimiters. The last
term budgets the fixed scalar/index registers of the rolling recurrence. -/
def workingSet (N : ℕ) (z : List Bool) (A d : ℕ) : ℕ :=
  let c := makeObservedCache N z
  (layerValue (cachedRun N c A d)).representationSize+
    (layerValue (cachedRun N c A (d+1))).representationSize+
    (chooseValue c).representationSize+(powerValue c).representationSize+
    (observedValue c).representationSize+16*(2*N.size+2)

theorem workingSet_binary (N : ℕ) (z : List Bool) (A d : ℕ)
    (hN : 0<N) (hz : z.length≤N) (hd : d<N) :
    workingSet N z A d≤250*(N+1)^3*(N.size+1) := by
  have hl := source_layer_size N z A d hN hz (by omega)
  have hr := source_layer_size N z A (d+1) hN hz (by omega)
  have hc := source_choose_size N z
  have hp := source_power_size N z
  have ho := source_observed_size N z hz
  have hf := sourceFrameBound_binary N
  have hmono : N.size+1≤(N+1)^3*(N.size+1) := by
    have hh : 0<(N+1)^3 := by positivity
    simpa using Nat.mul_le_mul_right (N.size+1) (show 1≤(N+1)^3 by omega)
  unfold workingSet
  dsimp only
  unfold sourceFrameBound at hf
  nlinarith

end Paper37.CachedCoreProgram
