import Paper37.RefinedCorePeak
import Paper37.RefinedWorkingSpace

namespace Paper37.RefinedCoreProgram
open Paper37.BoundedLoop Paper37.CachedDP Paper37.DP Paper37.CachedRefinedDP Paper37.ContinuationDP
open Paper37.CachedCoreProgram (chooseValue powerValue observedValue)

lemma sourceFrameBound_polynomial (N:ℕ) : sourceFrameBound N≤250*(N+1)^5 := by
  calc
    _≤250*(N+1)^4*(N.size+1) := sourceFrameBound_binary N
    _≤250*(N+1)^4*(N+1) := Nat.mul_le_mul_left _ (Nat.add_le_add_right (binarySize_le_self N) 1)
    _=_ := by ring

lemma stepPeakBound_le (N:ℕ) :
    stepPeakBound N≤10000000*(N+1)^3*(sourceFrameBound N+1) := by
  let S:=sourceFrameBound N+1
  have hS:1≤S := by dsimp [S];omega
  have hm1:S≤(N+1)*S := by simpa using Nat.mul_le_mul_right S (show 1≤N+1 by omega)
  have hm2:S≤(N+1)^2*S := by
    simpa using Nat.mul_le_mul_right S (show 1≤(N+1)^2 from one_le_pow₀ (by omega))
  have hm3:S≤(N+1)^3*S := by
    simpa using Nat.mul_le_mul_right S (show 1≤(N+1)^3 from one_le_pow₀ (by omega))
  have hc:cellPeakBound N≤600002*S := by unfold cellPeakBound;dsimp [S];omega
  have hjm:=Nat.mul_le_mul (show N+2≤2*(N+1) by omega) hc
  have hj:jPeakBound N≤1300000*(N+1)*S := by
    unfold jPeakBound
    change (N+2)*cellPeakBound N+5*S+2≤_
    nlinarith [hjm]
  have hum:=Nat.mul_le_mul (show N+2≤2*(N+1) by omega) hj
  have hu:uPeakBound N≤3000000*(N+1)^2*S := by
    unfold uPeakBound
    change (N+2)*jPeakBound N+5*S+2≤_
    nlinarith [hum]
  have hkm:=Nat.mul_le_mul (show N+2≤2*(N+1) by omega) hu
  unfold stepPeakBound
  change (N+2)*uPeakBound N+5*S+2≤10000000*(N+1)^3*S
  nlinarith [hkm]

lemma stepPeakBound_polynomial (N:ℕ) : stepPeakBound N≤2510000000*(N+1)^8 := by
  have hf:=sourceFrameBound_polynomial N
  have hp:1≤(N+1)^5 := one_le_pow₀ (by omega)
  have ha:sourceFrameBound N+1≤251*(N+1)^5 := by omega
  calc
    _≤10000000*(N+1)^3*(sourceFrameBound N+1) := stepPeakBound_le N
    _≤10000000*(N+1)^3*(251*(N+1)^5) := Nat.mul_le_mul_left _ ha
    _=_ := by ring

/-- The fixed AST's dynamic representation peak is polynomial on the actual
source input, with no intermediate execution trace supplied by a caller. -/
theorem coreProgram_source_peak_polynomial (N:ℕ) (z:List Bool) (A:ℕ) (ρ:Env)
    (hN:0<N) (hz:z.length≤N) (hA:A≤N)
    (h0:ρ 0=.nat N) (h1:ρ 1=.nat A) (h2:ρ 2=chooseValue (makeObservedCache N z))
    (h3:ρ 3=powerValue (makeObservedCache N z)) (h4:ρ 4=observedValue (makeObservedCache N z)) :
    coreProgram.peak ρ≤2510000000*(N+1)^8 :=
  (coreProgram_source_peak_le N z A ρ hN hz hA h0 h1 h2 h3 h4).trans (stepPeakBound_polynomial N)

theorem coreProgram_source (N:ℕ) (z:List Bool) (A:ℕ) (ρ:Env) (hz:z.length≤N)
    (h0:ρ 0=.nat N) (h1:ρ 1=.nat A) (h2:ρ 2=chooseValue (makeObservedCache N z))
    (h3:ρ 3=powerValue (makeObservedCache N z)) (h4:ρ 4=observedValue (makeObservedCache N z)) :
    coreProgram.eval ρ=layerValue (Paper37.AdaptiveDP.refinedRun N (observedCounts z) A N) := by
  rw [coreProgram_eval (makeObservedCache N z) A ρ h0 h1 h2 h3 h4,makeObservedCache_eq,
    cachedRefinedRun_correct N (observedCounts z) A N le_rfl (observedCounts_le_horizon N z hz)]

/-- Value, evaluator work, and all actual intermediate representations concern
one fixed finite program and the very same source histogram. -/
theorem source_core_certificate (N:ℕ) (z:List Bool) (A:ℕ) (ρ:Env)
    (hN:0<N) (hz:z.length≤N) (hA:A≤N)
    (h0:ρ 0=.nat N) (h1:ρ 1=.nat A) (h2:ρ 2=chooseValue (makeObservedCache N z))
    (h3:ρ 3=powerValue (makeObservedCache N z)) (h4:ρ 4=observedValue (makeObservedCache N z)) :
    coreProgram.eval ρ=layerValue (Paper37.AdaptiveDP.refinedRun N (observedCounts z) A N) ∧
      coreProgram.work ρ≤400*(N+1)^5 ∧ coreProgram.peak ρ≤2510000000*(N+1)^8 :=
  ⟨coreProgram_source N z A ρ hz h0 h1 h2 h3 h4,coreProgram_work_quintic ρ N h0,
    coreProgram_source_peak_polynomial N z A ρ hN hz hA h0 h1 h2 h3 h4⟩

end Paper37.RefinedCoreProgram
