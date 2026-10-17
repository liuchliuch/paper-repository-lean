import Paper37.RefinedValueSize
import Paper37.CachedWorkingSpace

namespace Paper37.RefinedCoreProgram
open Paper37.BoundedLoop Paper37.CachedDP Paper37.DP Paper37.CachedRefinedDP
open Paper37.CachedCoreProgram (chooseValue powerValue observedValue sourceWidth source_choose_size
  source_power_size source_observed_size)

/-- The refinement retains the sharp fourth-power times binary-width frame
bound; the subsequent generic TM simulation may use a coarser polynomial. -/
theorem sourceFrameBound_binary (N:ℕ) :
    sourceFrameBound N≤250*(N+1)^4*(N.size+1) := by
  have hf:=Paper37.CachedCoreProgram.sourceFrameBound_binary N
  have hl:layerSizeBound N (sourceWidth N)=
      (N+1)*Paper37.CachedCoreProgram.layerSizeBound N (sourceWidth N)+2 := by
    rfl
  have hb:Paper37.CachedCoreProgram.layerSizeBound N (sourceWidth N)≤
      Paper37.CachedCoreProgram.sourceFrameBound N := (Paper37.CachedCoreProgram.sourceFrame_contains N).1
  have hm:=Nat.mul_le_mul_left (N+1) hb
  have hm2:=Nat.mul_le_mul_left (N+1) hf
  have heq:(N+1)*(100*(N+1)^3*(N.size+1))=100*(N+1)^4*(N.size+1) := by ring
  rw [heq] at hm2
  have hp:(N+1)^3*(N.size+1)≤(N+1)^4*(N.size+1) :=
    Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) (by decide))
  have hone:1≤(N+1)^4*(N.size+1) := by
    have hh:0<(N+1)^4*(N.size+1) := by positivity
    omega
  unfold sourceFrameBound
  rw [hl]
  nlinarith

/-- Actual rolling storage: both materialized three-axis layers, the three
shared finite caches, and the fixed scalar/index registers. -/
def workingSet (N:ℕ) (z:List Bool) (A d:ℕ) : ℕ :=
  let c:=makeObservedCache N z
  (layerValue (cachedRefinedRun N c A d)).representationSize+
    (layerValue (cachedRefinedRun N c A (d+1))).representationSize+
    (chooseValue c).representationSize+(powerValue c).representationSize+
    (observedValue c).representationSize+20*(4*sourceWidth N+2*N.size+4)

theorem workingSet_binary (N:ℕ) (z:List Bool) (A d:ℕ)
    (hN:0<N) (hz:z.length≤N) (hd:d<N) :
    workingSet N z A d≤2000*(N+1)^4*(N.size+1) := by
  have hl:=source_layer_size N z A d hN hz (by omega)
  have hr:=source_layer_size N z A (d+1) hN hz (by omega)
  have hc:=source_choose_size N z
  have hp:=source_power_size N z
  have ho:=source_observed_size N z hz
  have hf:=sourceFrameBound_binary N
  have hmono:N.size+1≤(N+1)^4*(N.size+1) := by
    have hh:0<(N+1)^4 := by positivity
    simpa using Nat.mul_le_mul_right (N.size+1) (show 1≤(N+1)^4 by omega)
  have hs2:=Paper37.CachedCoreProgram.size_two_mul_le N
  have hs2m:=Nat.mul_le_mul_left (4*N+1) hs2
  have hw:sourceWidth N≤10*(N+1)*(N.size+1) := by
    unfold Paper37.CachedCoreProgram.sourceWidth
    nlinarith
  have hwm:(N+1)*(N.size+1)≤(N+1)^4*(N.size+1) :=
    Nat.mul_le_mul_right _ (by simpa only [pow_one] using
      (Nat.pow_le_pow_right (show 1≤N+1 by omega) (show 1≤(4:ℕ) by decide)))
  unfold workingSet
  dsimp only
  unfold sourceFrameBound Paper37.CachedCoreProgram.sourceFrameBound at hf
  nlinarith

end Paper37.RefinedCoreProgram
