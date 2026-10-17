import Paper37.CachedValueSize

namespace Paper37.CachedCoreProgram
open Paper37.DP

theorem sourceFrameBound_polynomial (N : ℕ) : sourceFrameBound N≤100*(N+1)^4 := by
  have hs := binarySize_le_self (2*N)
  have hn := binarySize_le_self N
  unfold sourceFrameBound layerSizeBound sourceWidth chooseSizeBound
  have hp : 0≤N^3 := Nat.zero_le _
  have hp4 : 0≤N^4 := Nat.zero_le _
  nlinarith

end Paper37.CachedCoreProgram
