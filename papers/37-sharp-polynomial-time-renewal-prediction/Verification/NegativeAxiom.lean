import Paper37.FullBlockMachine
import Paper37.CompleteResults
import Paper37.CachedQueries
import Paper37.CachedRefinedOperations
import Paper37.AdaptiveIntegerOutput
import Paper37.SequentialRegret
import Paper37.CountdownRefinement
import Paper37.StationaryCompression
import Paper37.KnownSupportCycle
import Paper37.CachedCorePolynomial
import Paper37.CachedWorkingSpace
import Paper37.RefinedCorePolynomial
import Paper37.RefinedWorkingSpace
import Paper37.UniformQueryMachine
import Paper37.UniformConditionalMachine
import Paper37.UniformNormalizerMachine
import Paper37.UniformAdaptiveQueryMachine
import Paper37.UniformBatchMachine
import Paper37.SpecifiedQueryBatchPeak
import Paper37.IntegerPredictorProgramWork
import Paper37.AdaptiveQueryWork

open scoped BigOperators ENNReal
namespace Verification
/- Isolated illegal-axiom fixture; excluded from production and its audit. -/
axiom forbidden_boundary_contract : ∀ (n : Nat),
  @Eq.{1} ENNReal (Paper37.Prediction.substitutedMinimaxRisk n)
    (ENNReal.ofReal
      (Real.log
        (@OfNat.ofNat.{0} Real (nat_lit 2)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))))
theorem contract_0001 : ∀ (n : Nat),
  @Eq.{1} ENNReal (Paper37.Prediction.substitutedMinimaxRisk n)
    (ENNReal.ofReal
      (Real.log
        (@OfNat.ofNat.{0} Real (nat_lit 2)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))) := forbidden_boundary_contract
end Verification
