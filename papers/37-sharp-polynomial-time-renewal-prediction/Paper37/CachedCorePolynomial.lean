import Paper37.CachedCorePeak
import Paper37.CachedFramePolynomial

namespace Paper37.CachedCoreProgram
open Paper37.BoundedLoop Paper37.CachedDP Paper37.DP Paper37.ContinuationDP

lemma stepPeakBound_polynomial (N : ℕ) : stepPeakBound N≤101000000*(N+1)^6 := by
  have hf := sourceFrameBound_polynomial N
  have hp : 1≤(N+1)^4 := by
    have hh : 0<(N+1)^4 := by positivity
    omega
  have ha : sourceFrameBound N+1≤101*(N+1)^4 := by omega
  calc
    _ ≤ 1000000*(N+1)^2*(sourceFrameBound N+1) := stepPeakBound_le N
    _ ≤ 1000000*(N+1)^2*(101*(N+1)^4) := Nat.mul_le_mul_left _ ha
    _ = _ := by ring

theorem coreProgram_peak_polynomial (N : ℕ) (z : List Bool) (A : ℕ) (ρ : Env)
    (hN : 0<N) (hz : z.length≤N) (hA : A≤N)
    (h0 : ρ 0=.nat N) (h1 : ρ 1=.nat A) (h2 : ρ 2=chooseValue (makeObservedCache N z))
    (h3 : ρ 3=powerValue (makeObservedCache N z)) (h4 : ρ 4=observedValue (makeObservedCache N z)) :
    coreProgram.peak ρ≤101000000*(N+1)^6 :=
  (coreProgram_source_peak_le N z A ρ hN hz hA h0 h1 h2 h3 h4).trans (stepPeakBound_polynomial N)

theorem coreProgram_source_peak_polynomial (N : ℕ) (z : List Bool) (A : ℕ) (ρ : Env)
    (hN : 0<N) (hz : z.length≤N) (hA : A≤N)
    (h0 : ρ 0=.nat N) (h1 : ρ 1=.nat A) (h2 : ρ 2=chooseValue (makeObservedCache N z))
    (h3 : ρ 3=powerValue (makeObservedCache N z)) (h4 : ρ 4=observedValue (makeObservedCache N z)) :
    coreProgram.peak ρ≤200000000*(N+1)^6 :=
  (coreProgram_peak_polynomial N z A ρ hN hz hA h0 h1 h2 h3 h4).trans (by omega)

/-- All components concern the same fixed first-order program and the same
actual source input. Neither its value, cost nor intermediate payload bound
is supplied as an assumption. -/
theorem source_core_certificate (N : ℕ) (z : List Bool) (A : ℕ) (ρ : Env)
    (hN : 0<N) (hz : z.length≤N) (hA : A≤N)
    (h0 : ρ 0=.nat N) (h1 : ρ 1=.nat A) (h2 : ρ 2=chooseValue (makeObservedCache N z))
    (h3 : ρ 3=powerValue (makeObservedCache N z)) (h4 : ρ 4=observedValue (makeObservedCache N z)) :
    coreProgram.eval ρ=layerValue (run N (observedCounts z) A N) ∧
      coreProgram.work ρ≤200*(N+1)^4 ∧
      coreProgram.peak ρ≤101000000*(N+1)^6 :=
  ⟨coreProgram_source N z A ρ hz h0 h1 h2 h3 h4,
    coreProgram_work_le ρ N h0,
    coreProgram_peak_polynomial N z A ρ hN hz hA h0 h1 h2 h3 h4⟩

end Paper37.CachedCoreProgram
