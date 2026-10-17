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

/- Frozen explicit closed target types; no proof placeholders.
Challenge and solution reuse the production proofs. The independent contract
is each explicit type below, reviewed through the source-anchor inventory.
Whole-library checks and official comparison are verification_deferred_by_user. -/
open scoped BigOperators ENNReal
universe u_1
noncomputable section
namespace Verification
theorem contract_0001 :
    ∀ (n : Nat),
      @Eq.{1} ENNReal (Paper37.Prediction.substitutedMinimaxRisk n)
        (ENNReal.ofReal
          (Real.log
            (@OfNat.ofNat.{0} Real (nat_lit 2)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))) := @Paper37.Prediction.substitutedMinimaxRisk_eq_log_two

theorem contract_0002 :
    ∀ (n : Nat),
      @Eq.{1} ENNReal (Paper37.Prediction.historywiseMinimaxRisk n)
        (ENNReal.ofReal
          (Real.log
            (@OfNat.ofNat.{0} Real (nat_lit 2)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))) := @Paper37.Prediction.historywiseMinimaxRisk_eq_log_two

theorem contract_0003 :
    ∀ (N : Nat),
      @LE.le.{0} Real Real.instLE (@Rat.cast.{0} Real Real.instRatCast (Paper37.Prediction.ordinaryNormalizer N))
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
            (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@OfNat.ofNat.{0} Real (nat_lit 2)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                (@Nat.cast.{0} Real Real.instNatCast N).sqrt)
              Paper37.AnalyticBounds.partitionConstant))
          (Real.exp
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Paper37.AnalyticBounds.partitionConstant
              (@Nat.cast.{0} Real Real.instNatCast N).sqrt))) := @Paper37.RateUpper.ordinaryNormalizer_exp_bound

theorem contract_0004 :
    @Monotone.{0, 0} Nat Real Nat.instPreorder Real.instPreorder Paper37.Envelope.Z := @Paper37.Envelope.Z_monotone

theorem contract_0005 :
    ∀ (μ : Paper37.Renewal.Law) (x : List.{0} Bool),
      @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
          (Paper37.Renewal.blockMass μ x) →
        @LE.le.{0} Real Real.instLE
          (Real.log
            (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (Paper37.Renewal.blockMass μ x) (@Rat.cast.{0} Real Real.instRatCast (Paper37.Prediction.blockAssignment x))))
          (Paper37.AnalyticBounds.redundancyBound (@List.length.{0} Bool x)) := @Paper37.RateUpper.pointwise_block_regret

theorem contract_0006 :
    ∀ (μ : Paper37.Renewal.Law) (N : Nat),
      @LE.le.{0} Real Real.instLE (Paper37.CompressionPrediction.blockKL μ N) (Paper37.AnalyticBounds.redundancyBound N) := @Paper37.RateUpper.block_redundancy

theorem contract_0007 :
    ∀ (a : Nat → Nat) (d k u : Nat),
      @Eq.{1} Nat
        (Paper37.DP.Gd a
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          k u)
        (@Finset.sum.{0, 0} Nat Nat Nat.instAddCommMonoid
          (Finset.range
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@Min.min.{0} Nat instMinNat k
                (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) u
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          fun b =>
          @HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (k.choose b)
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@Monoid.toNatPow.{0} Nat Nat.instMonoid))
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (a
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  b)
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (a
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  b)))
            (Paper37.DP.Gd a d (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) k b)
              (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) u
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  b)))) := @Paper37.DP.Gd_recurrence

theorem contract_0008 :
    ∀ (a : Nat → Nat) (A d k u : Nat),
      @Eq.{1} Nat
        (Paper37.DP.Sd a A
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          k u)
        (@Finset.sum.{0, 0} Nat Nat Nat.instAddCommMonoid
          (Finset.range
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@Min.min.{0} Nat instMinNat k
                (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) u
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          fun b =>
          @HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (k.choose b)
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@Monoid.toNatPow.{0} Nat Nat.instMonoid))
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (a
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  b)
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (a
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  b)))
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (Paper37.DP.Sd a A d (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) k b)
                (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) u
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                    b)))
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@ite.{1} Nat
                  (@LT.lt.{0} Nat instLTNat A
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  (A.decLt
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  b (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                (Paper37.DP.Gd a d (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) k b)
                  (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) u
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                      b)))))) := @Paper37.DP.Sd_recurrence

theorem contract_0009 :
    ∀ (a : Nat → Nat) (A d k u : Nat), @Dvd.dvd.{0} Nat Nat.instDvd k (Paper37.DP.Sd a A d k u) := @Paper37.DP.Sd_divisible

theorem contract_0010 :
    ∀ (H : Nat) (z : List.{0} Bool) (R : Nat),
      @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@List.length.{0} Bool z) R)
          H →
        @Eq.{1} Rat
          (Paper37.Prediction.continuationMass
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@List.length.{0} Bool z) R) z)
          (@HAdd.hAdd.{0, 0, 0} Rat Rat Rat (@instHAdd.{0} Rat Rat.instAdd) (Paper37.Prediction.wordEnvelope z)
            (@Finset.sum.{0, 0} Nat Rat Rat.addCommMonoid
              (@Finset.Icc.{0} Nat Nat.instPreorder Nat.instLocallyFiniteOrder
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (Paper37.Envelope.parseAge (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) z) R))
              fun k =>
              @Finset.sum.{0, 0} Nat Rat Rat.addCommMonoid
                (@Finset.Icc.{0} Nat Nat.instPreorder Nat.instLocallyFiniteOrder k
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (Paper37.Envelope.parseAge (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) z) R))
                fun u =>
                @HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
                  (@Nat.cast.{0} Rat Rat.instNatCast
                    (Paper37.DP.Sd (Paper37.ContinuationDP.observedCounts z)
                      (Paper37.Envelope.parseAge (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) z) H k u))
                  (@HMul.hMul.{0, 0, 0} Rat Rat Rat (@instHMul.{0} Rat Rat.instMul) (@Nat.cast.{0} Rat Rat.instNatCast k)
                    (@HPow.hPow.{0, 0, 0} Rat Nat Rat (@instHPow.{0, 0} Rat Nat Rat.instPowNat)
                      (@Nat.cast.{0} Rat Rat.instNatCast
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (@List.length.{0} Nat
                            (Paper37.Envelope.parseGaps (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) z))
                          k))
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (@List.length.{0} Nat
                          (Paper37.Envelope.parseGaps (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) z))
                        k))))) := @Paper37.ContinuationDP.continuationMass_eq_multisetDP

theorem contract_0011 :
    ∀ (N t : Nat),
      @LT.lt.{0} Nat instLTNat t N →
        @Eq.{1} Rat (Paper37.Prediction.blockConditional N (@List.replicate.{0} Bool t Bool.false))
          (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
            (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))
            (@Nat.cast.{0} Rat Rat.instNatCast
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) N t)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) := @Paper37.EnvelopeBridge.blockConditional_zeros

theorem contract_0012 :
    ∀ (N j : Nat) (z : List.{0} Bool),
      @LT.lt.{0} Nat instLTNat
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) j
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (@List.length.{0} Bool z))
          N →
        @Eq.{1} Rat
          (Paper37.Prediction.blockConditional N
            (@HAppend.hAppend.{0, 0, 0} (List.{0} Bool) (List.{0} Bool) (List.{0} Bool)
              (@instHAppendOfAppend.{0} (List.{0} Bool) (@List.instAppend.{0} Bool)) (@List.replicate.{0} Bool j Bool.false)
              (@List.cons.{0} Bool Bool.true z)))
          (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
            (Paper37.Prediction.continuationMass
              (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) N
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) j
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (@HAppend.hAppend.{0, 0, 0} (List.{0} Bool) (List.{0} Bool) (List.{0} Bool)
                (@instHAppendOfAppend.{0} (List.{0} Bool) (@List.instAppend.{0} Bool)) z
                (@List.cons.{0} Bool Bool.true (@List.nil.{0} Bool))))
            (@HAdd.hAdd.{0, 0, 0} Rat Rat Rat (@instHAdd.{0} Rat Rat.instAdd)
              (Paper37.Prediction.continuationMass
                (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) N
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) j
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (@HAppend.hAppend.{0, 0, 0} (List.{0} Bool) (List.{0} Bool) (List.{0} Bool)
                  (@instHAppendOfAppend.{0} (List.{0} Bool) (@List.instAppend.{0} Bool)) z
                  (@List.cons.{0} Bool Bool.false (@List.nil.{0} Bool))))
              (Paper37.Prediction.continuationMass
                (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) N
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) j
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (@HAppend.hAppend.{0, 0, 0} (List.{0} Bool) (List.{0} Bool) (List.{0} Bool)
                  (@instHAppendOfAppend.{0} (List.{0} Bool) (@List.instAppend.{0} Bool)) z
                  (@List.cons.{0} Bool Bool.true (@List.nil.{0} Bool)))))) := @Paper37.EnvelopeBridge.blockConditional_firstRenewal

theorem contract_0013 :
    ∀ (N L : Nat) (z : List.{0} Bool),
      @LE.le.{0} Nat instLENat L N →
        @LE.le.{0} Nat instLENat (@List.length.{0} Bool z) N →
          @LE.le.{0} Nat instLENat (Paper37.CachedOperations.coreWork N L z)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 100) (instOfNatNat (nat_lit 100)))
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@Monoid.toNatPow.{0} Nat Nat.instMonoid))
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) N
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))) := @Paper37.CachedOperations.coreWork_quartic

theorem contract_0014 :
    ∀ (N L q C : Nat) (z : List.{0} Bool),
      @LE.le.{0} Nat instLENat L N →
        @LE.le.{0} Nat instLENat (@List.length.{0} Bool z) N →
          @LE.le.{0} Nat instLENat q
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) C
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) N
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
            @LE.le.{0} Nat instLENat
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) q (Paper37.CachedOperations.coreWork N L z))
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 100) (instOfNatNat (nat_lit 100))) C)
                (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@Monoid.toNatPow.{0} Nat Nat.instMonoid))
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) N
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))) := @Paper37.CachedOperations.batch_coreWork_quintic

theorem contract_0015 :
    ∀ (N : Nat) (a : Nat → Nat) (A d : Nat),
      @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) N →
        @LE.le.{0} Nat instLENat d N →
          @LE.le.{0} Nat instLENat (@Finset.sum.{0, 0} Nat Nat Nat.instAddCommMonoid (Paper37.DP.gapSet d) a) N →
            @LE.le.{0} Nat instLENat
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                (@Paper37.DP.layerBinarySize N (Paper37.DP.run N a A d)))
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                  (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@Monoid.toNatPow.{0} Nat Nat.instMonoid))
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) N
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) N)
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) N).size)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) := @Paper37.DP.rollingBinarySize

theorem contract_0016 :
    ∀ (H : Nat) (z : List.{0} Bool) (R : Nat),
      @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@List.length.{0} Bool z) R)
          H →
        @Eq.{1} Rat
          (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
            (@Nat.cast.{0} Rat Rat.instNatCast (@Prod.fst.{0, 0} Nat Nat (Paper37.CachedOutput.evaluatePair H z R)))
            (@Nat.cast.{0} Rat Rat.instNatCast (@Prod.snd.{0, 0} Nat Nat (Paper37.CachedOutput.evaluatePair H z R))))
          (Paper37.Prediction.continuationMass
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@List.length.{0} Bool z) R) z) := @Paper37.CachedOutput.evaluatePair_correct

theorem contract_0017 :
    ∀ (n : Nat) (x : List.{0} Bool),
      @Eq.{1} Nat (@List.length.{0} Bool x) n →
        @LE.le.{0} Nat instLENat (Paper37.IntegerOutput.pairSize (Paper37.IntegerPredictor.predictorPair n x))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) n
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (Paper37.IntegerPredictor.queryBitBound
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
              n.size)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) := @Paper37.IntegerPredictor.predictorPair_binarySize

theorem contract_0018 :
    ∀ (H : Nat), @Eq.{1} Rat (Paper37.CachedQueries.cachedNormalizer H) (Paper37.Prediction.ordinaryNormalizer H) := @Paper37.CachedQueries.cachedNormalizer_correct

theorem contract_0019 :
    ∀ (x : List.{0} Bool),
      @Eq.{1} Rat (Paper37.CachedQueries.cachedBlockAssignment x) (Paper37.Prediction.blockAssignment x) := @Paper37.CachedQueries.cachedBlockAssignment_correct

theorem contract_0020 :
    ∀ (μ : Paper37.Renewal.Law) (x : List.{0} Bool),
      @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
          (Paper37.Renewal.blockMass μ x) →
        @LE.le.{0} Real Real.instLE
          (@Finset.sum.{0, 0} Nat Real Real.instAddCommMonoid (Finset.range (@List.length.{0} Bool x)) fun t =>
            Real.log
              (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                (@Paper37.Compression.Distribution.mass.{0} Bool Bool.fintype
                  (Paper37.RenewalCompression.next μ (@List.take.{0} Bool t x))
                  (@Option.getD.{0} Bool
                    (@GetElem?.getElem?.{0, 0, 0} (List.{0} Bool) Nat Bool
                      (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Bool as))
                      (@List.instGetElem?NatLtLength.{0} Bool) x t)
                    Bool.false))
                (@ite.{1} Real
                  (@Eq.{1} Bool
                    (@Option.getD.{0} Bool
                      (@GetElem?.getElem?.{0, 0, 0} (List.{0} Bool) Nat Bool
                        (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Bool as))
                        (@List.instGetElem?NatLtLength.{0} Bool) x t)
                      Bool.false)
                    Bool.true)
                  (instDecidableEqBool
                    (@Option.getD.{0} Bool
                      (@GetElem?.getElem?.{0, 0, 0} (List.{0} Bool) Nat Bool
                        (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Bool as))
                        (@List.instGetElem?NatLtLength.{0} Bool) x t)
                      Bool.false)
                    Bool.true)
                  (@Rat.cast.{0} Real Real.instRatCast
                    (Paper37.ContinuationDP.evaluateConditional (@List.length.{0} Bool x) (@List.take.{0} Bool t x)))
                  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                    (@Rat.cast.{0} Real Real.instRatCast
                      (Paper37.ContinuationDP.evaluateConditional (@List.length.{0} Bool x) (@List.take.{0} Bool t x)))))))
          (Paper37.AnalyticBounds.redundancyBound (@List.length.{0} Bool x)) := @Paper37.SequentialRegret.computed_path_log_regret

theorem contract_0021 :
    ∀ (μ : Paper37.Renewal.Law) {k t : Nat} (o : Paper37.RenewalCompression.Word k) (s : Paper37.RenewalCompression.Word t)
      (y : Bool) (c : Nat),
      @Eq.{1} Real
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@Paper37.CountdownRefinement.countableJointMass μ k t o s y c)
          (@Finset.sum.{0, 0} (Paper37.RenewalCompression.Word k) Real Real.instAddCommMonoid
            (@Finset.univ.{0} (Paper37.RenewalCompression.Word k) (@Vector.fintype.{0} Bool Bool.fintype k)) fun o' =>
            @Finset.sum.{0, 0} Bool Real Real.instAddCommMonoid (@Finset.univ.{0} Bool Bool.fintype) fun y' =>
              @Paper37.CountdownRefinement.countableJointMass μ k t o' s y' c))
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@Finset.sum.{0, 0} Bool Real Real.instAddCommMonoid (@Finset.univ.{0} Bool Bool.fintype) fun y' =>
            @Paper37.CountdownRefinement.countableJointMass μ k t o s y' c)
          (@Finset.sum.{0, 0} (Paper37.RenewalCompression.Word k) Real Real.instAddCommMonoid
            (@Finset.univ.{0} (Paper37.RenewalCompression.Word k) (@Vector.fintype.{0} Bool Bool.fintype k)) fun o' =>
            @Paper37.CountdownRefinement.countableJointMass μ k t o' s y c)) := @Paper37.CountdownRefinement.suffix_regeneration_unbounded

theorem contract_0022 :
    ∀ (μ : Paper37.Renewal.Law) {k t : Nat} (o : Paper37.RenewalCompression.Word k) (s : Paper37.RenewalCompression.Word t)
      (y : Bool),
      @Eq.{1} Real
        (@tsum.{0, 0} Real Nat Real.instAddCommMonoid
          (@UniformSpace.toTopologicalSpace.{0} Real (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
          (fun c => @Paper37.CountdownRefinement.countableJointMass μ k t o s y c) (SummationFilter.unconditional.{0} Nat))
        (Paper37.Renewal.blockMass μ
          (@HAppend.hAppend.{0, 0, 0} (List.{0} Bool) (List.{0} Bool) (List.{0} Bool)
            (@instHAppendOfAppend.{0} (List.{0} Bool) (@List.instAppend.{0} Bool))
            (@HAppend.hAppend.{0, 0, 0} (List.{0} Bool) (List.{0} Bool) (List.{0} Bool)
              (@instHAppendOfAppend.{0} (List.{0} Bool) (@List.instAppend.{0} Bool))
              (@Subtype.val.{1} (List.{0} Bool) (fun l => @Eq.{1} Nat (@List.length.{0} Bool l) k) o)
              (@Subtype.val.{1} (List.{0} Bool) (fun l => @Eq.{1} Nat (@List.length.{0} Bool l) t) s))
            (@List.cons.{0} Bool y (@List.nil.{0} Bool)))) := @Paper37.CountdownRefinement.tsum_countableJointMass

theorem contract_0023 :
    ∀ (P : Paper37.StationaryCompression.StationaryBinaryLaw) (n : Nat)
      (hn : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n)
      (Q :
        @Paper37.Compression.Distribution.{0}
          (Paper37.RenewalCompression.Word
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (@Vector.fintype.{0} Bool Bool.fintype
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (hQ :
        ∀
          (x :
            Paper37.RenewalCompression.Word
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))),
          @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
            (@Paper37.Compression.Distribution.mass.{0}
              (Paper37.RenewalCompression.Word
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (@Vector.fintype.{0} Bool Bool.fintype
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              Q x)),
      @LE.le.{0} ENNReal (@Preorder.toLE.{0} ENNReal (@PartialOrder.toPreorder.{0} ENNReal ENNReal.instPartialOrder))
        (Paper37.StationaryCompression.risk n
          (Paper37.StationaryCompression.sourcePredictor
            (Paper37.StationaryCompression.extendAssignment
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              Q hQ)
            n hn)
          P)
        (ENNReal.ofReal
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
              (@Paper37.Compression.Distribution.kl.{0}
                (Paper37.RenewalCompression.Word
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (@Vector.fintype.{0} Bool Bool.fintype
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (Paper37.StationaryCompression.blockDistribution P
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                Q)
              (@Finset.sum.{0, 0} Nat Real Real.instAddCommMonoid (Finset.range n) fun t =>
                Paper37.StationaryCompression.memory P
                  (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) n
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) t
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) t
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
            (@Nat.cast.{0} Real Real.instNatCast n))) := @Paper37.StationaryCompression.compression_to_prediction_single

theorem contract_0024 :
    ∀ (μ : Paper37.Renewal.Law) (n : Nat) (olderLength : Nat → Nat),
      @LE.le.{0} Real Real.instLE
        (@Finset.sum.{0, 0} Nat Real Real.instAddCommMonoid (Finset.range n) fun t =>
          Paper37.RenewalCompression.memory μ
            (olderLength
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) t
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) t
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (Real.log
          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (@Nat.cast.{0} Real Real.instNatCast n)
            (@OfNat.ofNat.{0} Real (nat_lit 2)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))) := @Paper37.RenewalCountdown.renewal_memory_sum_bound

theorem contract_0025 :
    ∀ (n : Nat) (hn : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n),
      @LE.le.{0} ENNReal (@Preorder.toLE.{0} ENNReal (@PartialOrder.toPreorder.{0} ENNReal ENNReal.instPartialOrder))
        (@iSup.{0, 1} ENNReal Paper37.Renewal.Law
          (@ConditionallyCompleteLattice.toSupSet.{0} ENNReal
            (@ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal
              (@ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal
                (@CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrder))))
          fun μ => Paper37.Prediction.risk n (Paper37.CompressionPrediction.sourcePredictor n hn) μ)
        (ENNReal.ofReal
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
              (Paper37.AnalyticBounds.redundancyBound
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (Real.log
                (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                  (@Nat.cast.{0} Real Real.instNatCast n)
                  (@OfNat.ofNat.{0} Real (nat_lit 2)
                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))))
            (@Nat.cast.{0} Real Real.instNatCast n))) := @Paper37.RateUpper.supremum_source_risk_upper

theorem contract_0026 :
    ∀ (n : Nat),
      @Eq.{1} Rat (Paper37.Prediction.predict n (@List.replicate.{0} Bool n Bool.false))
        (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
          (@HSub.hSub.{0, 0, 0} Rat Rat Rat (@instHSub.{0} Rat Rat.instSub)
            (harmonic
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))))
          (@Nat.cast.{0} Rat Rat.instNatCast n)) := @Paper37.ZeroHistory.predict_zeros

theorem contract_0027 :
    ∀ (μ : Paper37.Renewal.Law) {n : Nat},
      @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) n →
        @LE.le.{0} ENNReal (@Preorder.toLE.{0} ENNReal (@PartialOrder.toPreorder.{0} ENNReal ENNReal.instPartialOrder))
          (@HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
            (@instHMul.{0} ENNReal
              (@Distrib.toMul.{0} ENNReal
                (@NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal
                  (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal
                    (@Semiring.toNonAssocSemiring.{0} ENNReal
                      (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))))
            (ENNReal.ofReal (Paper37.Renewal.blockMass μ (@List.replicate.{0} Bool n Bool.false)))
            (Paper37.Boundary.kl (Paper37.Renewal.conditional μ (@List.replicate.{0} Bool n Bool.false))
              (@Rat.cast.{0} Real Real.instRatCast (Paper37.Prediction.predict n (@List.replicate.{0} Bool n Bool.false)))))
          (ENNReal.ofReal
            (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@OfNat.ofNat.{0} Real (nat_lit 3)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
                (Real.log
                  (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                    (@Nat.cast.{0} Real Real.instNatCast n)
                    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))))
              (@Nat.cast.{0} Real Real.instNatCast n))) := @Paper37.ZeroHistory.zero_contribution_kl_le

theorem contract_0028 :
    ∀ (L s : Nat),
      @LE.le.{0} Rat Rat.instLE (Paper37.Adaptive.restrictedNormalizer L s)
        (@Nat.cast.{0} Rat Rat.instNatCast (Paper37.AnalyticBounds.restrictedCountBound L s)) := @Paper37.Adaptive.restrictedNormalizer_le_countBound

theorem contract_0029 :
    ∀ (L s : Nat),
      @LE.le.{0} Rat Rat.instLE (Paper37.Adaptive.restrictedNormalizer L s)
        (@HPow.hPow.{0, 0, 0} Rat Nat Rat (@instHPow.{0, 0} Rat Nat Rat.instPowNat)
          (@HAdd.hAdd.{0, 0, 0} Rat Rat Rat (@instHAdd.{0} Rat Rat.instAdd) (@Nat.cast.{0} Rat Rat.instNatCast L)
            (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) s)
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) := @Paper37.Adaptive.restrictedNormalizer_le_pow

theorem contract_0030 :
    ∀ (μ : Paper37.Renewal.Law) (x : List.{0} Bool),
      @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@List.length.{0} Bool x) →
        @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
            (Paper37.Renewal.blockMass μ x) →
          @LE.le.{0} Real Real.instLE
            (Real.log
              (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                (Paper37.Renewal.blockMass μ x) (@Rat.cast.{0} Real Real.instRatCast (Paper37.Adaptive.adaptiveBlock x))))
            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
              (Real.log
                (@OfNat.ofNat.{0} Real (nat_lit 2)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
              (@Min.min.{0} Real Real.instMin (Paper37.AnalyticBounds.redundancyBound (@List.length.{0} Bool x))
                (Paper37.Adaptive.occupiedPenalty (@List.length.{0} Bool x) (Paper37.Adaptive.kappa x)))) := @Paper37.AdaptiveRisk.adaptive_log_oracle_source

theorem contract_0031 :
    ∀ (H t : Nat) (z : List.{0} Bool) (R : Nat),
      @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@List.length.{0} Bool z) R)
          H →
        @Eq.{1} Rat
          (Paper37.Adaptive.restrictedContinuation
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@List.length.{0} Bool z) R) t z)
          (@HAdd.hAdd.{0, 0, 0} Rat Rat Rat (@instHAdd.{0} Rat Rat.instAdd) (Paper37.Adaptive.restrictedEnvelope t z)
            (@Finset.sum.{0, 0} Nat Rat Rat.addCommMonoid
              (@Finset.Icc.{0} Nat Nat.instPreorder Nat.instLocallyFiniteOrder
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (Paper37.Envelope.parseAge (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) z) R))
              fun k =>
              @Finset.sum.{0, 0} Nat Rat Rat.addCommMonoid
                (@Finset.Icc.{0} Nat Nat.instPreorder Nat.instLocallyFiniteOrder k
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (Paper37.Envelope.parseAge (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) z) R))
                fun u =>
                @HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
                  (@Nat.cast.{0} Rat Rat.instNatCast
                    (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv)
                      (@Finset.sum.{0, 0} Nat Nat Nat.instAddCommMonoid
                        (Finset.range
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) t
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                        fun j =>
                        Paper37.AdaptiveDP.refinedSd (Paper37.ContinuationDP.observedCounts z)
                          (Paper37.Envelope.parseAge (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) z) H k u
                          j)
                      k))
                  (@HPow.hPow.{0, 0, 0} Rat Nat Rat (@instHPow.{0, 0} Rat Nat Rat.instPowNat)
                    (@Nat.cast.{0} Rat Rat.instNatCast
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (@List.length.{0} Nat
                          (Paper37.Envelope.parseGaps (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) z))
                        k))
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@List.length.{0} Nat
                        (Paper37.Envelope.parseGaps (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) z))
                      k)))) := @Paper37.RefinedContinuation.restrictedContinuation_eq_integerDP

theorem contract_0032 :
    ∀ (N L : Nat) (z : List.{0} Bool),
      @LE.le.{0} Nat instLENat L N →
        @LE.le.{0} Nat instLENat (@List.length.{0} Bool z) N →
          @LE.le.{0} Nat instLENat (Paper37.CachedRefinedOperations.coreWork N L z)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 200) (instOfNatNat (nat_lit 200)))
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@Monoid.toNatPow.{0} Nat Nat.instMonoid))
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) N
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))) := @Paper37.CachedRefinedOperations.coreWork_quintic

theorem contract_0033 :
    ∀ (n : Nat) (x : List.{0} Bool),
      @Eq.{1} Nat (@List.length.{0} Bool x) n →
        @Eq.{1} Rat
          (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
            (@Nat.cast.{0} Rat Rat.instNatCast (@Prod.fst.{0, 0} Nat Nat (Paper37.AdaptiveIntegerOutput.predictorPair n x)))
            (@Nat.cast.{0} Rat Rat.instNatCast
              (@Prod.snd.{0, 0} Nat Nat (Paper37.AdaptiveIntegerOutput.predictorPair n x))))
          (Paper37.Adaptive.adaptivePredict n x) := @Paper37.AdaptiveIntegerOutput.predictorPair_exact

theorem contract_0034 :
    ∀ (n : Nat) (x : List.{0} Bool),
      @Eq.{1} Nat (@List.length.{0} Bool x) n →
        @LE.le.{0} Nat instLENat (Paper37.IntegerOutput.pairSize (Paper37.AdaptiveIntegerOutput.predictorPair n x))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) n
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (Paper37.AdaptiveIntegerOutput.conditionalBitBound
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
              n.size)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) := @Paper37.AdaptiveIntegerOutput.predictorPair_binarySize

theorem contract_0035 :
    ∀ (μ : Paper37.Renewal.Law) (n : Nat)
      (hn : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n),
      @LE.le.{0} ENNReal (@Preorder.toLE.{0} ENNReal (@PartialOrder.toPreorder.{0} ENNReal ENNReal.instPartialOrder))
        (Paper37.Prediction.risk n (Paper37.AdaptivePrediction.sourcePredictor n hn) μ)
        (ENNReal.ofReal
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                (Real.log
                  (@OfNat.ofNat.{0} Real (nat_lit 2)
                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
                (@Min.min.{0} Real Real.instMin
                  (Paper37.AnalyticBounds.redundancyBound
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (@OfNat.ofNat.{0} Real (nat_lit 2)
                          (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                        (Paper37.AnalyticBounds.occupiedComplexity
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                          (fun d =>
                            μ.mass
                              (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) d
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                          (Paper37.Renewal.mean μ)))
                      (@OfNat.ofNat.{0} Real (nat_lit 6)
                        (@instOfNatAtLeastTwo.{0} Real (nat_lit 6) Real.instNatCast
                          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
                            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))))
                    (Real.log
                      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                        (@Nat.cast.{0} Real Real.instNatCast n)
                        (@OfNat.ofNat.{0} Real (nat_lit 2)
                          (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))))))
              (Real.log
                (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                  (@Nat.cast.{0} Real Real.instNatCast n)
                  (@OfNat.ofNat.{0} Real (nat_lit 2)
                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))))
            (@Nat.cast.{0} Real Real.instNatCast n))) := @Paper37.AdaptivePrediction.adaptive_risk_oracle

theorem contract_0036 :
    ∀ (μ : Paper37.Renewal.Law) (s : Nat) (S : Finset.{0} Nat),
      (∀ (d : Nat),
          Not (@Membership.mem.{0, 0} Nat (Finset.{0} Nat) (@Finset.instMembership.{0} Nat) S d) →
            @Eq.{1} Real (μ.mass d) (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))) →
        @LE.le.{0} Nat instLENat (@Finset.card.{0} Nat S) s →
          ∀ (n : Nat) (hn : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n),
            @LE.le.{0} ENNReal (@Preorder.toLE.{0} ENNReal (@PartialOrder.toPreorder.{0} ENNReal ENNReal.instPartialOrder))
              (Paper37.Prediction.risk n
                (Paper37.AdaptivePrediction.sourcePredictor n
                  (@Decidable.byContradiction
                    (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n)
                    (Nat.decLt (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n) fun a =>
                    Paper37.TailAdaptation.finite_support_rate._proof_1 s S n hn a))
                μ)
              (ENNReal.ofReal
                (@Min.min.{0} Real Real.instMin
                  (@HDiv.hDiv.{0, 0, 0} Real Real Real
                    (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                    Paper37.TailAdaptation.universalConstant (@Nat.cast.{0} Real Real.instNatCast n).sqrt)
                  (@HDiv.hDiv.{0, 0, 0} Real Real Real
                    (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (@OfNat.ofNat.{0} Real (nat_lit 19)
                          (@instOfNatAtLeastTwo.{0} Real (nat_lit 19) Real.instNatCast
                            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 18) (instOfNatNat (nat_lit 18)))
                              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 17) (instOfNatNat (nat_lit 17)))))))
                        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                          (@Nat.cast.{0} Real Real.instNatCast s)
                          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
                      (Real.log (@Nat.cast.{0} Real Real.instNatCast n)))
                    (@Nat.cast.{0} Real Real.instNatCast n)))) := @Paper37.TailAdaptation.finite_support_rate

theorem contract_0037 :
    ∀ (μ : Paper37.Renewal.Law) (C c : Real),
      @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) C →
        @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) c →
          (∀ (d : Nat),
              @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) d →
                @LE.le.{0} Real Real.instLE
                  (μ.mass
                    (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) d
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) C
                    (Real.exp
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (@Neg.neg.{0} Real Real.instNeg c) (@Nat.cast.{0} Real Real.instNatCast d))))) →
            ∀ (n : Nat) (hn : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n),
              @LE.le.{0} ENNReal
                (@Preorder.toLE.{0} ENNReal (@PartialOrder.toPreorder.{0} ENNReal ENNReal.instPartialOrder))
                (Paper37.Prediction.risk n
                  (Paper37.AdaptivePrediction.sourcePredictor n
                    (@Decidable.byContradiction
                      (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n)
                      (Nat.decLt (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n) fun a =>
                      Paper37.TailAdaptation.adaptive_universal_risk._proof_1 n hn a))
                  μ)
                (ENNReal.ofReal
                  (@HDiv.hDiv.{0, 0, 0} Real Real Real
                    (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                      (Paper37.TailAdaptation.exponentialConstant C c)
                      (@HPow.hPow.{0, 0, 0} Real Nat Real
                        (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid))
                        (Real.log (@Nat.cast.{0} Real Real.instNatCast n))
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                    (@Nat.cast.{0} Real Real.instNatCast n))) := @Paper37.TailAdaptation.exponential_tail_rate

theorem contract_0038 :
    ∀ (μ : Paper37.Renewal.Law) (C α : Real),
      @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) C →
        @LT.lt.{0} Real Real.instLT
            (@OfNat.ofNat.{0} Real (nat_lit 2)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
            α →
          (∀ (d : Nat),
              @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) d →
                @LE.le.{0} Real Real.instLE
                  (μ.mass
                    (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) d
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) C
                    (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
                      (@Nat.cast.{0} Real Real.instNatCast d) (@Neg.neg.{0} Real Real.instNeg α)))) →
            ∀ (n : Nat) (hn : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n),
              @LE.le.{0} ENNReal
                (@Preorder.toLE.{0} ENNReal (@PartialOrder.toPreorder.{0} ENNReal ENNReal.instPartialOrder))
                (Paper37.Prediction.risk n
                  (Paper37.AdaptivePrediction.sourcePredictor n
                    (@Decidable.byContradiction
                      (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n)
                      (Nat.decLt (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n) fun a =>
                      Paper37.TailAdaptation.adaptive_universal_risk._proof_1 n hn a))
                  μ)
                (ENNReal.ofReal
                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                      (Paper37.TailAdaptation.powerConstant C α)
                      (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
                        (@Nat.cast.{0} Real Real.instNatCast n)
                        (@Neg.neg.{0} Real Real.instNeg
                          (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                            (@HDiv.hDiv.{0, 0, 0} Real Real Real
                              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) α)))))
                    (Real.log (@Nat.cast.{0} Real Real.instNatCast n)))) := @Paper37.TailAdaptation.power_tail_rate

theorem contract_0039 :
    @Filter.Eventually.{0} Nat
      (fun n =>
        And
          (@LE.le.{0} ENNReal (@Preorder.toLE.{0} ENNReal (@PartialOrder.toPreorder.{0} ENNReal ENNReal.instPartialOrder))
            (ENNReal.ofReal
              (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                (Real.log (@Nat.cast.{0} Real Real.instNatCast n))
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@OfNat.ofNat.{0} Real (nat_lit 8)
                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 8) Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))))
                  (@Nat.cast.{0} Real Real.instNatCast n))))
            (Paper37.PeriodMinimax.periodMinimax n))
          (@LE.le.{0} ENNReal (@Preorder.toLE.{0} ENNReal (@PartialOrder.toPreorder.{0} ENNReal ENNReal.instPartialOrder))
            (Paper37.PeriodMinimax.periodMinimax n)
            (ENNReal.ofReal
              (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@OfNat.ofNat.{0} Real (nat_lit 20)
                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 20) Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 19) (instOfNatNat (nat_lit 19)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 18) (instOfNatNat (nat_lit 18)))))))
                  (Real.log (@Nat.cast.{0} Real Real.instNatCast n)))
                (@Nat.cast.{0} Real Real.instNatCast n)))))
      (@Filter.atTop.{0} Nat Nat.instPreorder) := @Paper37.PeriodMinimax.periodMinimax_rate

theorem contract_0040 :
    Paper37.EquilibriumCycle.EquilibriumCyclePrinciple →
      ∀ {n : Nat},
        @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 600) (instOfNatNat (nat_lit 600))) n →
          ∀ (q : Paper37.Prediction.RandomizedPredictor),
            @LE.le.{0} ENNReal (@Preorder.toLE.{0} ENNReal (@PartialOrder.toPreorder.{0} ENNReal ENNReal.instPartialOrder))
              (ENNReal.ofReal
                (@HDiv.hDiv.{0, 0, 0} Real Real Real
                  (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                    (@OfNat.ofNat.{0} Real (nat_lit 11)
                      (@instOfNatAtLeastTwo.{0} Real (nat_lit 11) Real.instNatCast
                        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10)))
                          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9)))))))
                    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                      (Real.log
                        (@OfNat.ofNat.{0} Real (nat_lit 2)
                          (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
                      (@HDiv.hDiv.{0, 0, 0} Real Real Real
                        (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                        (@OfNat.ofNat.{0} Real (nat_lit 2)
                          (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))))
                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                    (@OfNat.ofNat.{0} Real (nat_lit 40600)
                      (@instOfNatAtLeastTwo.{0} Real (nat_lit 40600) Real.instNatCast
                        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 40599) (instOfNatNat (nat_lit 40599)))
                          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 40598) (instOfNatNat (nat_lit 40598)))))))
                    (@Nat.cast.{0} Real Real.instNatCast n).sqrt)))
              (@iSup.{0, 1} ENNReal
                (@Subtype.{1} Paper37.Renewal.Law fun μ =>
                  Paper37.CycleGoodEvent.UniformHardClass (Paper37.BayesLowerBound.ceilingRoot n) μ)
                (@ConditionallyCompleteLattice.toSupSet.{0} ENNReal
                  (@ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal
                    (@ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal
                      (@CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal
                        ENNReal.instCompleteLinearOrder))))
                fun μ =>
                Paper37.Prediction.risk n q
                  (@Subtype.val.{1} Paper37.Renewal.Law
                    (fun μ => Paper37.CycleGoodEvent.UniformHardClass (Paper37.BayesLowerBound.ceilingRoot n) μ) μ)) := @Paper37.CycleGoodEvent.finite_support_lower_bound

theorem contract_0041 :
    Paper37.EquilibriumCycle.EquilibriumCyclePrinciple →
      ∀ {n : Nat},
        @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 600) (instOfNatNat (nat_lit 600))) n →
          @LE.le.{0} ENNReal (@Preorder.toLE.{0} ENNReal (@PartialOrder.toPreorder.{0} ENNReal ENNReal.instPartialOrder))
            (ENNReal.ofReal
              (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@OfNat.ofNat.{0} Real (nat_lit 11)
                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 11) Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9)))))))
                  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                    (Real.log
                      (@OfNat.ofNat.{0} Real (nat_lit 2)
                        (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
                    (@HDiv.hDiv.{0, 0, 0} Real Real Real
                      (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                      (@OfNat.ofNat.{0} Real (nat_lit 2)
                        (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))))
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@OfNat.ofNat.{0} Real (nat_lit 40600)
                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 40600) Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 40599) (instOfNatNat (nat_lit 40599)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 40598) (instOfNatNat (nat_lit 40598)))))))
                  (@Nat.cast.{0} Real Real.instNatCast n).sqrt)))
            (Paper37.Prediction.minimaxRisk n) := @Paper37.CycleGoodEvent.minimax_lower_bound

theorem contract_0042 :
    Paper37.EquilibriumCycle.EquilibriumCyclePrinciple →
      ∀ {b n : Nat},
        @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) b →
          @LE.le.{0} Nat instLENat
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 24) (instOfNatNat (nat_lit 24))) b)
              n →
            @LE.le.{0} Nat instLENat n (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) b b) →
              @LE.le.{0} Real Real.instLE
                (@HDiv.hDiv.{0, 0, 0} Real Real Real
                  (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                  (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                  (@OfNat.ofNat.{0} Real (nat_lit 8)
                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 8) Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))))))
                (Paper37.BayesLowerBound.goodPredictiveMass n b) := @Paper37.CycleGoodEvent.goodPredictiveMass_lower

theorem contract_0043 :
    ∀ {b : Nat},
      @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) b →
        ∀ (j : Nat) (x : List.{0} Bool) (z : Paper37.SupportPrior.Sample b),
          @Eq.{1} Real (@Paper37.SupportPrior.observationLikelihood b j x z)
            (@ite.{1} Real (@Paper37.SupportPrior.compatible b x z) (@Paper37.SupportPrior.compatible_decidable b x z)
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (Paper37.SupportPrior.likelihoodScale b x) (@Paper37.SupportPrior.boundaryWeight b j x z))
              (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))) := @Paper37.SupportPrior.observationLikelihood_factor

theorem contract_0044 :
    ∀ {b : Nat},
      @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) b →
        ∀ (j : Nat) (x : List.{0} Bool)
          (hZ :
            @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
              (@Paper37.LowerBound.FiniteLaw.expectation.{0} (Paper37.SupportPrior.Sample b)
                (@instFintypeProd.{0, 0}
                  (@Subtype.{1} (Finset.{0} Nat) fun x =>
                    @Membership.mem.{0, 0} (Finset.{0} Nat) (Finset.{0} (Finset.{0} Nat))
                      (@Finset.instMembership.{0} (Finset.{0} Nat)) (Paper37.SupportPrior.lowChoices b) x)
                  (@Subtype.{1} (Finset.{0} Nat) fun x =>
                    @Membership.mem.{0, 0} (Finset.{0} Nat) (Finset.{0} (Finset.{0} Nat))
                      (@Finset.instMembership.{0} (Finset.{0} Nat)) (Paper37.SupportPrior.highFreeChoices b) x)
                  (@Finset.Subtype.fintype.{0} (Finset.{0} Nat) (Paper37.SupportPrior.lowChoices b))
                  (@Finset.Subtype.fintype.{0} (Finset.{0} Nat) (Paper37.SupportPrior.highFreeChoices b)))
                (Paper37.SupportPrior.prior b) (@Paper37.SupportPrior.observationLikelihood b j x))),
          @LT.lt.{0} Nat instLTNat (Paper37.Renewal.ageFrom (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) x)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 24) (instOfNatNat (nat_lit 24))) b) →
            Not
                (@Membership.mem.{0, 0} Nat (Finset.{0} Nat) (@Finset.instMembership.{0} Nat)
                  (@List.toFinset.{0} Nat instDecidableEqNat
                    (Paper37.Renewal.gapsFrom (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) x))
                  (Paper37.Renewal.ageFrom (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) x)) →
              @LE.le.{0} Nat instLENat
                  (@List.length.{0} Nat
                    (Paper37.Renewal.gapsFrom (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) x))
                  b →
                And
                  (@LE.le.{0} Real Real.instLE
                    (@HDiv.hDiv.{0, 0, 0} Real Real Real
                      (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                      (@OfNat.ofNat.{0} Real (nat_lit 11)
                        (@instOfNatAtLeastTwo.{0} Real (nat_lit 11) Real.instNatCast
                          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10)))
                            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9)))))))
                      (@OfNat.ofNat.{0} Real (nat_lit 203)
                        (@instOfNatAtLeastTwo.{0} Real (nat_lit 203) Real.instNatCast
                          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 202) (instOfNatNat (nat_lit 202)))
                            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 201) (instOfNatNat (nat_lit 201))))))))
                    (@Paper37.LowerBound.FiniteLaw.eventMass.{0} (Paper37.SupportPrior.Sample b)
                      (@instFintypeProd.{0, 0}
                        (@Subtype.{1} (Finset.{0} Nat) fun x =>
                          @Membership.mem.{0, 0} (Finset.{0} Nat) (Finset.{0} (Finset.{0} Nat))
                            (@Finset.instMembership.{0} (Finset.{0} Nat)) (Paper37.SupportPrior.lowChoices b) x)
                        (@Subtype.{1} (Finset.{0} Nat) fun x =>
                          @Membership.mem.{0, 0} (Finset.{0} Nat) (Finset.{0} (Finset.{0} Nat))
                            (@Finset.instMembership.{0} (Finset.{0} Nat)) (Paper37.SupportPrior.highFreeChoices b) x)
                        (@Finset.Subtype.fintype.{0} (Finset.{0} Nat) (Paper37.SupportPrior.lowChoices b))
                        (@Finset.Subtype.fintype.{0} (Finset.{0} Nat) (Paper37.SupportPrior.highFreeChoices b)))
                      (@Paper37.SupportPrior.posterior b j x hZ)
                      (fun z =>
                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat) (@Finset.instMembership.{0} Nat)
                          (@Paper37.SupportPrior.support b z)
                          (Paper37.Renewal.ageFrom (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) x))
                      fun a =>
                      @Finset.decidableMem.{0} Nat instDecidableEqNat
                        (Paper37.Renewal.ageFrom (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) x)
                        (@Paper37.SupportPrior.support b a)))
                  (@LE.le.{0} Real Real.instLE
                    (@HDiv.hDiv.{0, 0, 0} Real Real Real
                      (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                      (@OfNat.ofNat.{0} Real (nat_lit 11)
                        (@instOfNatAtLeastTwo.{0} Real (nat_lit 11) Real.instNatCast
                          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10)))
                            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9)))))))
                      (@OfNat.ofNat.{0} Real (nat_lit 203)
                        (@instOfNatAtLeastTwo.{0} Real (nat_lit 203) Real.instNatCast
                          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 202) (instOfNatNat (nat_lit 202)))
                            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 201) (instOfNatNat (nat_lit 201))))))))
                    (@Paper37.LowerBound.FiniteLaw.eventMass.{0} (Paper37.SupportPrior.Sample b)
                      (@instFintypeProd.{0, 0}
                        (@Subtype.{1} (Finset.{0} Nat) fun x =>
                          @Membership.mem.{0, 0} (Finset.{0} Nat) (Finset.{0} (Finset.{0} Nat))
                            (@Finset.instMembership.{0} (Finset.{0} Nat)) (Paper37.SupportPrior.lowChoices b) x)
                        (@Subtype.{1} (Finset.{0} Nat) fun x =>
                          @Membership.mem.{0, 0} (Finset.{0} Nat) (Finset.{0} (Finset.{0} Nat))
                            (@Finset.instMembership.{0} (Finset.{0} Nat)) (Paper37.SupportPrior.highFreeChoices b) x)
                        (@Finset.Subtype.fintype.{0} (Finset.{0} Nat) (Paper37.SupportPrior.lowChoices b))
                        (@Finset.Subtype.fintype.{0} (Finset.{0} Nat) (Paper37.SupportPrior.highFreeChoices b)))
                      (@Paper37.SupportPrior.posterior b j x hZ)
                      (fun z =>
                        Not
                          (@Membership.mem.{0, 0} Nat (Finset.{0} Nat) (@Finset.instMembership.{0} Nat)
                            (@Paper37.SupportPrior.support b z)
                            (Paper37.Renewal.ageFrom (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) x)))
                      fun a =>
                      @instDecidableNot
                        (@Membership.mem.{0, 0} Nat (Finset.{0} Nat) (@Finset.instMembership.{0} Nat)
                          (@Paper37.SupportPrior.support b a)
                          (Paper37.Renewal.ageFrom (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) x))
                        (@Finset.decidableMem.{0} Nat instDecidableEqNat
                          (Paper37.Renewal.ageFrom (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) x)
                          (@Paper37.SupportPrior.support b a)))) := @Paper37.FiniteSupportLowerBound.posterior_stability

theorem contract_0045 :
    ∀ {Ω : Type u_1} [inst : MeasurableSpace.{u_1} Ω] (ρ : @MeasureTheory.Measure.{u_1} Ω inst)
      [@MeasureTheory.IsProbabilityMeasure.{u_1} Ω inst ρ] {b : Nat},
      @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) b →
        ∀ (j : Nat) (x : List.{0} Bool)
          (hZ :
            @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
              (@Paper37.LowerBound.FiniteLaw.expectation.{0} (Paper37.SupportPrior.Sample b)
                (@instFintypeProd.{0, 0}
                  (@Subtype.{1} (Finset.{0} Nat) fun x =>
                    @Membership.mem.{0, 0} (Finset.{0} Nat) (Finset.{0} (Finset.{0} Nat))
                      (@Finset.instMembership.{0} (Finset.{0} Nat)) (Paper37.SupportPrior.lowChoices b) x)
                  (@Subtype.{1} (Finset.{0} Nat) fun x =>
                    @Membership.mem.{0, 0} (Finset.{0} Nat) (Finset.{0} (Finset.{0} Nat))
                      (@Finset.instMembership.{0} (Finset.{0} Nat)) (Paper37.SupportPrior.highFreeChoices b) x)
                  (@Finset.Subtype.fintype.{0} (Finset.{0} Nat) (Paper37.SupportPrior.lowChoices b))
                  (@Finset.Subtype.fintype.{0} (Finset.{0} Nat) (Paper37.SupportPrior.highFreeChoices b)))
                (Paper37.SupportPrior.prior b) (@Paper37.SupportPrior.observationLikelihood b j x))),
          @LT.lt.{0} Nat instLTNat (Paper37.Renewal.ageFrom (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) x)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 24) (instOfNatNat (nat_lit 24))) b) →
            Not
                (@Membership.mem.{0, 0} Nat (Finset.{0} Nat) (@Finset.instMembership.{0} Nat)
                  (@List.toFinset.{0} Nat instDecidableEqNat
                    (Paper37.Renewal.gapsFrom (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) x))
                  (Paper37.Renewal.ageFrom (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) x)) →
              @LE.le.{0} Nat instLENat
                  (@List.length.{0} Nat
                    (Paper37.Renewal.gapsFrom (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) x))
                  b →
                ∀ (q : Ω → Real),
                  (∀ (ω : Ω),
                      And
                        (@LE.le.{0} Real Real.instLE
                          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) (q ω))
                        (@LE.le.{0} Real Real.instLE (q ω)
                          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))) →
                    @LE.le.{0} ENNReal
                      (@Preorder.toLE.{0} ENNReal (@PartialOrder.toPreorder.{0} ENNReal ENNReal.instPartialOrder))
                      (ENNReal.ofReal
                        (@HDiv.hDiv.{0, 0, 0} Real Real Real
                          (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                            (@HDiv.hDiv.{0, 0, 0} Real Real Real
                              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                              (@OfNat.ofNat.{0} Real (nat_lit 11)
                                (@instOfNatAtLeastTwo.{0} Real (nat_lit 11) Real.instNatCast
                                  (@Nat.instAtLeastTwoHAddOfNat
                                    (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10)))
                                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9)))))))
                              (@OfNat.ofNat.{0} Real (nat_lit 203)
                                (@instOfNatAtLeastTwo.{0} Real (nat_lit 203) Real.instNatCast
                                  (@Nat.instAtLeastTwoHAddOfNat
                                    (@OfNat.ofNat.{0} Nat (nat_lit 202) (instOfNatNat (nat_lit 202)))
                                    (@Nat.instNeZeroSucc
                                      (@OfNat.ofNat.{0} Nat (nat_lit 201) (instOfNatNat (nat_lit 201))))))))
                            (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                              (Real.log
                                (@OfNat.ofNat.{0} Real (nat_lit 2)
                                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                                    (@Nat.instAtLeastTwoHAddOfNat
                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                      (@Nat.instNeZeroSucc
                                        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
                              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                                (@OfNat.ofNat.{0} Real (nat_lit 2)
                                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                                    (@Nat.instAtLeastTwoHAddOfNat
                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                      (@Nat.instNeZeroSucc
                                        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))))
                          (@Nat.cast.{0} Real Real.instNatCast
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@OfNat.ofNat.{0} Nat (nat_lit 24) (instOfNatNat (nat_lit 24))) b))))
                      (@MeasureTheory.lintegral.{u_1} Ω inst ρ fun ω =>
                        @Paper37.LowerBound.FiniteLaw.expectedKL.{0} (Paper37.SupportPrior.Sample b)
                          (@instFintypeProd.{0, 0}
                            (@Subtype.{1} (Finset.{0} Nat) fun x =>
                              @Membership.mem.{0, 0} (Finset.{0} Nat) (Finset.{0} (Finset.{0} Nat))
                                (@Finset.instMembership.{0} (Finset.{0} Nat)) (Paper37.SupportPrior.lowChoices b) x)
                            (@Subtype.{1} (Finset.{0} Nat) fun x =>
                              @Membership.mem.{0, 0} (Finset.{0} Nat) (Finset.{0} (Finset.{0} Nat))
                                (@Finset.instMembership.{0} (Finset.{0} Nat)) (Paper37.SupportPrior.highFreeChoices b) x)
                            (@Finset.Subtype.fintype.{0} (Finset.{0} Nat) (Paper37.SupportPrior.lowChoices b))
                            (@Finset.Subtype.fintype.{0} (Finset.{0} Nat) (Paper37.SupportPrior.highFreeChoices b)))
                          (@Paper37.SupportPrior.posterior b j x hZ)
                          (fun z =>
                            Paper37.Renewal.conditional (@Paper37.SupportPrior.law b z)
                              (@HAppend.hAppend.{0, 0, 0} (List.{0} Bool) (List.{0} Bool) (List.{0} Bool)
                                (@instHAppendOfAppend.{0} (List.{0} Bool) (@List.instAppend.{0} Bool))
                                (@List.replicate.{0} Bool j Bool.false) (@List.cons.{0} Bool Bool.true x)))
                          (q ω)) := @Paper37.FiniteSupportLowerBound.actual_randomized_posterior_radius

theorem contract_0046 :
    ∀ (μ : Paper37.Renewal.Law) (N : Nat),
      @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) N →
        @LE.le.{0} ENNReal (@Preorder.toLE.{0} ENNReal (@PartialOrder.toPreorder.{0} ENNReal ENNReal.instPartialOrder))
          (Paper37.AnytimePrediction.cumulativeRisk μ N)
          (ENNReal.ofReal
            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  Paper37.AnalyticBounds.partitionConstant
                  (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                    (@OfNat.ofNat.{0} Real (nat_lit 2)
                      (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                    (Real.sqrt
                      (@OfNat.ofNat.{0} Real (nat_lit 2)
                        (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))))
                (@Nat.cast.{0} Real Real.instNatCast N).sqrt)
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@HDiv.hDiv.{0, 0, 0} Real Real Real
                    (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                      (@OfNat.ofNat.{0} Real (nat_lit 3)
                        (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
                          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
                      (Real.log
                        (@OfNat.ofNat.{0} Real (nat_lit 2)
                          (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))))
                    (@OfNat.ofNat.{0} Real (nat_lit 2)
                      (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
                  (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                    (@Nat.cast.{0} Real Real.instNatCast N.log2)
                    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
                (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                  (@Nat.cast.{0} Real Real.instNatCast N.log2)
                  (@OfNat.ofNat.{0} Real (nat_lit 2)
                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))))) := @Paper37.AnytimePrediction.cumulativeRisk_upper

theorem contract_0047 :
    Paper37.EquilibriumCycle.EquilibriumCyclePrinciple →
      ∀ (N : Nat),
        @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2500) (instOfNatNat (nat_lit 2500))) N →
          And
            (@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
              Paper37.CumulativeLower.cumulativeConstant)
            (And
              (@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                Paper37.CumulativeLower.cumulativeUpperConstant)
              (And
                (@LE.le.{0} ENNReal
                  (@Preorder.toLE.{0} ENNReal (@PartialOrder.toPreorder.{0} ENNReal ENNReal.instPartialOrder))
                  (ENNReal.ofReal
                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                      Paper37.CumulativeLower.cumulativeConstant (@Nat.cast.{0} Real Real.instNatCast N).sqrt))
                  (Paper37.CumulativeLower.minimaxCumulativeRisk N))
                (And
                  (@LE.le.{0} ENNReal
                    (@Preorder.toLE.{0} ENNReal (@PartialOrder.toPreorder.{0} ENNReal ENNReal.instPartialOrder))
                    (Paper37.CumulativeLower.minimaxCumulativeRisk N)
                    (@iSup.{0, 1} ENNReal Paper37.Renewal.Law
                      (@ConditionallyCompleteLattice.toSupSet.{0} ENNReal
                        (@ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal
                          (@ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal
                            (@CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal
                              ENNReal.instCompleteLinearOrder))))
                      fun μ => Paper37.AnytimePrediction.cumulativeRisk μ N))
                  (@LE.le.{0} ENNReal
                    (@Preorder.toLE.{0} ENNReal (@PartialOrder.toPreorder.{0} ENNReal ENNReal.instPartialOrder))
                    (@iSup.{0, 1} ENNReal Paper37.Renewal.Law
                      (@ConditionallyCompleteLattice.toSupSet.{0} ENNReal
                        (@ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal
                          (@ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal
                            (@CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal
                              ENNReal.instCompleteLinearOrder))))
                      fun μ => Paper37.AnytimePrediction.cumulativeRisk μ N)
                    (ENNReal.ofReal
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        Paper37.CumulativeLower.cumulativeUpperConstant (@Nat.cast.{0} Real Real.instNatCast N).sqrt)))))) := @Paper37.CumulativePrediction.source_cumulative_rate

theorem contract_0048 :
    Paper37.EquilibriumCycle.EquilibriumCyclePrinciple →
      ∀ (μ : Paper37.Renewal.Law) {n B : Nat} [Nonempty.{1} (Fin B)],
        (∀ (d : Nat),
            @LE.le.{0} Nat instLENat B d →
              @Eq.{1} Real (μ.mass d) (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))) →
          @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) B →
            @LE.le.{0} Nat instLENat
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) B)
                n →
              have R :=
                Paper37.Prediction.risk n
                  (Paper37.KnownSupportWord.predictor B
                    (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                      (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) n B)
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  μ;
              And
                (@LE.le.{0} ENNReal
                  (@Preorder.toLE.{0} ENNReal (@PartialOrder.toPreorder.{0} ENNReal ENNReal.instPartialOrder)) R
                  (ENNReal.ofReal
                    (@HDiv.hDiv.{0, 0, 0} Real Real Real
                      (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                        (@Nat.cast.{0} Real Real.instNatCast B)
                        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (Paper37.Renewal.mean μ)
                        (@Nat.cast.{0} Real Real.instNatCast
                          (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) n B))))))
                (And
                  (@LE.le.{0} ENNReal
                    (@Preorder.toLE.{0} ENNReal (@PartialOrder.toPreorder.{0} ENNReal ENNReal.instPartialOrder)) R
                    (ENNReal.ofReal
                      (@HDiv.hDiv.{0, 0, 0} Real Real Real
                        (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                          (@Nat.cast.{0} Real Real.instNatCast B)
                          (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                            (@Nat.cast.{0} Real Real.instNatCast B)
                            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (Paper37.Renewal.mean μ)
                          (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                            (@Nat.cast.{0} Real Real.instNatCast n) (@Nat.cast.{0} Real Real.instNatCast B))))))
                  (And
                    (@LE.le.{0} ENNReal
                      (@Preorder.toLE.{0} ENNReal (@PartialOrder.toPreorder.{0} ENNReal ENNReal.instPartialOrder)) R
                      (ENNReal.ofReal
                        (@HDiv.hDiv.{0, 0, 0} Real Real Real
                          (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                            (@OfNat.ofNat.{0} Real (nat_lit 2)
                              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                            (@HPow.hPow.{0, 0, 0} Real Nat Real
                              (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid))
                              (@Nat.cast.{0} Real Real.instNatCast B)
                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (Paper37.Renewal.mean μ)
                            (@Nat.cast.{0} Real Real.instNatCast n)))))
                    (@LE.le.{0} ENNReal
                      (@Preorder.toLE.{0} ENNReal (@PartialOrder.toPreorder.{0} ENNReal ENNReal.instPartialOrder)) R
                      (ENNReal.ofReal
                        (@HDiv.hDiv.{0, 0, 0} Real Real Real
                          (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                            (@OfNat.ofNat.{0} Real (nat_lit 2)
                              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                            (@HPow.hPow.{0, 0, 0} Real Nat Real
                              (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid))
                              (@Nat.cast.{0} Real Real.instNatCast B)
                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                          (@Nat.cast.{0} Real Real.instNatCast n)))))) := @Paper37.KnownSupportCycle.risk_bounds

theorem contract_0049 :
    Paper37.EquilibriumCycle.EquilibriumCyclePrinciple →
      ∀ {n B : Nat},
        @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) B →
          @LE.le.{0} Nat instLENat
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) B)
              n →
            ∀ (μ : Paper37.Renewal.Law),
              (∀ (d : Nat),
                  @LE.le.{0} Nat instLENat B d →
                    @Eq.{1} Real (μ.mass d) (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))) →
                @LE.le.{0} ENNReal
                  (@Preorder.toLE.{0} ENNReal (@PartialOrder.toPreorder.{0} ENNReal ENNReal.instPartialOrder))
                  (Paper37.Prediction.risk n
                    (Paper37.KnownSupportWord.predictor B
                      (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                        (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) n B)
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    μ)
                  (ENNReal.ofReal
                    (@HDiv.hDiv.{0, 0, 0} Real Real Real
                      (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (@OfNat.ofNat.{0} Real (nat_lit 2)
                          (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                        (@HPow.hPow.{0, 0, 0} Real Nat Real
                          (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid))
                          (@Nat.cast.{0} Real Real.instNatCast B)
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                      (@Nat.cast.{0} Real Real.instNatCast n))) := @Paper37.KnownSupportCycle.predictor_uniform_bound

theorem contract_0050 :
    Paper37.EquilibriumCycle.EquilibriumCyclePrinciple →
      ∀ (n : Nat) (hn : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) n),
        And
          (@Eq.{1} ENNReal (Paper37.Prediction.substitutedMinimaxRisk n)
            (ENNReal.ofReal
              (Real.log
                (@OfNat.ofNat.{0} Real (nat_lit 2)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))))
          (And
            (@LE.le.{0} ENNReal (@Preorder.toLE.{0} ENNReal (@PartialOrder.toPreorder.{0} ENNReal ENNReal.instPartialOrder))
              (Paper37.Prediction.minimaxRisk n)
              (@iSup.{0, 1} ENNReal Paper37.Renewal.Law
                (@ConditionallyCompleteLattice.toSupSet.{0} ENNReal
                  (@ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal
                    (@ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal
                      (@CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal
                        ENNReal.instCompleteLinearOrder))))
                fun μ =>
                Paper37.Prediction.risk n
                  (Paper37.CompressionPrediction.sourcePredictor n
                    (@Decidable.byContradiction
                      (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n)
                      (Nat.decLt (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n) fun a =>
                      Paper37.MainResults.main_statistical_chain._proof_1 n hn a))
                  μ))
            (And
              (@LE.le.{0} ENNReal
                (@Preorder.toLE.{0} ENNReal (@PartialOrder.toPreorder.{0} ENNReal ENNReal.instPartialOrder))
                (@iSup.{0, 1} ENNReal Paper37.Renewal.Law
                  (@ConditionallyCompleteLattice.toSupSet.{0} ENNReal
                    (@ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal
                      (@ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal
                        (@CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal
                          ENNReal.instCompleteLinearOrder))))
                  fun μ =>
                  Paper37.Prediction.risk n
                    (Paper37.CompressionPrediction.sourcePredictor n
                      (@Decidable.byContradiction
                        (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n)
                        (Nat.decLt (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n) fun a =>
                        Paper37.MainResults.main_statistical_chain._proof_1 n hn a))
                    μ)
                (ENNReal.ofReal
                  (@HDiv.hDiv.{0, 0, 0} Real Real Real
                    (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                      (Paper37.AnalyticBounds.redundancyBound
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                      (Real.log
                        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                          (@Nat.cast.{0} Real Real.instNatCast n)
                          (@OfNat.ofNat.{0} Real (nat_lit 2)
                            (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))))
                    (@Nat.cast.{0} Real Real.instNatCast n))))
              (And
                (@LE.le.{0} ENNReal
                  (@Preorder.toLE.{0} ENNReal (@PartialOrder.toPreorder.{0} ENNReal ENNReal.instPartialOrder))
                  (ENNReal.ofReal
                    (@HDiv.hDiv.{0, 0, 0} Real Real Real
                      (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                        (Paper37.AnalyticBounds.redundancyBound
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                        (Real.log
                          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                            (@Nat.cast.{0} Real Real.instNatCast n)
                            (@OfNat.ofNat.{0} Real (nat_lit 2)
                              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))))
                      (@Nat.cast.{0} Real Real.instNatCast n)))
                  (ENNReal.ofReal
                    (@HDiv.hDiv.{0, 0, 0} Real Real Real
                      (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                        (@HDiv.hDiv.{0, 0, 0} Real Real Real
                          (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                            (@OfNat.ofNat.{0} Real (nat_lit 2)
                              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                            Real.pi)
                          (Real.sqrt
                            (@OfNat.ofNat.{0} Real (nat_lit 3)
                              (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
                                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))))
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                          (@OfNat.ofNat.{0} Real (nat_lit 3)
                            (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
                              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
                          (Real.sqrt
                            (@OfNat.ofNat.{0} Real (nat_lit 2)
                              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))))
                      (@Nat.cast.{0} Real Real.instNatCast n).sqrt)))
                (@LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 600) (instOfNatNat (nat_lit 600))) n →
                  @LE.le.{0} ENNReal
                    (@Preorder.toLE.{0} ENNReal (@PartialOrder.toPreorder.{0} ENNReal ENNReal.instPartialOrder))
                    (ENNReal.ofReal
                      (@HDiv.hDiv.{0, 0, 0} Real Real Real
                        (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                          (@OfNat.ofNat.{0} Real (nat_lit 11)
                            (@instOfNatAtLeastTwo.{0} Real (nat_lit 11) Real.instNatCast
                              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10)))
                                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9)))))))
                          (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                            (Real.log
                              (@OfNat.ofNat.{0} Real (nat_lit 2)
                                (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                                  (@Nat.instAtLeastTwoHAddOfNat
                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
                            (@HDiv.hDiv.{0, 0, 0} Real Real Real
                              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                              (@OfNat.ofNat.{0} Real (nat_lit 2)
                                (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                                  (@Nat.instAtLeastTwoHAddOfNat
                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                    (@Nat.instNeZeroSucc
                                      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))))
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                          (@OfNat.ofNat.{0} Real (nat_lit 40600)
                            (@instOfNatAtLeastTwo.{0} Real (nat_lit 40600) Real.instNatCast
                              (@Nat.instAtLeastTwoHAddOfNat
                                (@OfNat.ofNat.{0} Nat (nat_lit 40599) (instOfNatNat (nat_lit 40599)))
                                (@Nat.instNeZeroSucc
                                  (@OfNat.ofNat.{0} Nat (nat_lit 40598) (instOfNatNat (nat_lit 40598)))))))
                          (@Nat.cast.{0} Real Real.instNatCast n).sqrt)))
                    (Paper37.Prediction.minimaxRisk n))))) := @Paper37.MainResults.main_statistical_chain

theorem contract_0051 :
    Paper37.EquilibriumCycle.EquilibriumCyclePrinciple →
      @Exists.{1} Real fun c =>
        @Exists.{1} Real fun C =>
          And (@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) c)
            (And (@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) C)
              (∀ (n : Nat),
                @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 600) (instOfNatNat (nat_lit 600))) n →
                  And
                    (@LE.le.{0} ENNReal
                      (@Preorder.toLE.{0} ENNReal (@PartialOrder.toPreorder.{0} ENNReal ENNReal.instPartialOrder))
                      (ENNReal.ofReal
                        (@HDiv.hDiv.{0, 0, 0} Real Real Real
                          (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) c
                          (@Nat.cast.{0} Real Real.instNatCast n).sqrt))
                      (Paper37.Prediction.minimaxRisk n))
                    (@LE.le.{0} ENNReal
                      (@Preorder.toLE.{0} ENNReal (@PartialOrder.toPreorder.{0} ENNReal ENNReal.instPartialOrder))
                      (Paper37.Prediction.minimaxRisk n)
                      (ENNReal.ofReal
                        (@HDiv.hDiv.{0, 0, 0} Real Real Real
                          (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) C
                          (@Nat.cast.{0} Real Real.instNatCast n).sqrt))))) := @Paper37.MainResults.fixed_time_minimax_rate

theorem contract_0052 :
    ∀ (ρ : Paper37.BoundedLoop.Env) (x : List.{0} Bool),
      @Eq.{1} Paper37.BoundedLoop.Value (ρ (@OfNat.ofNat.{0} Nat (nat_lit 40) (instOfNatNat (nat_lit 40))))
          (Paper37.WordProgram.wordValue x) →
        have out := Paper37.BoundedLoop.Expr.eval ρ Paper37.IntegerPredictorProgram.predictorProgram;
        @Eq.{1} Rat
          (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
            (@Nat.cast.{0} Rat Rat.instNatCast
              (@Option.getD.{0} Paper37.BoundedLoop.Value
                  (@GetElem?.getElem?.{0, 0, 0} (List.{0} Paper37.BoundedLoop.Value) Nat Paper37.BoundedLoop.Value
                    (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Paper37.BoundedLoop.Value as))
                    (@List.instGetElem?NatLtLength.{0} Paper37.BoundedLoop.Value) out.arrayVal
                    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                  (Paper37.BoundedLoop.Value.nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))).natVal)
            (@Nat.cast.{0} Rat Rat.instNatCast
              (@Option.getD.{0} Paper37.BoundedLoop.Value
                  (@GetElem?.getElem?.{0, 0, 0} (List.{0} Paper37.BoundedLoop.Value) Nat Paper37.BoundedLoop.Value
                    (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Paper37.BoundedLoop.Value as))
                    (@List.instGetElem?NatLtLength.{0} Paper37.BoundedLoop.Value) out.arrayVal
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  (Paper37.BoundedLoop.Value.nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))).natVal))
          (Paper37.Prediction.predict (@List.length.{0} Bool x) x) := @Paper37.IntegerPredictorProgram.predictorProgram_source

theorem contract_0053 :
    ∀ (ρ : Paper37.BoundedLoop.Env) (x : List.{0} Bool),
      @Eq.{1} Paper37.BoundedLoop.Value (ρ (@OfNat.ofNat.{0} Nat (nat_lit 40) (instOfNatNat (nat_lit 40))))
          (Paper37.WordProgram.wordValue x) →
        @LE.le.{0} Nat instLENat (Paper37.BoundedLoop.Expr.work ρ Paper37.IntegerPredictorProgram.predictorProgram)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 3000) (instOfNatNat (nat_lit 3000)))
            (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@Monoid.toNatPow.{0} Nat Nat.instMonoid))
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@List.length.{0} Bool x)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))) := @Paper37.IntegerPredictorProgram.predictorProgram_work

theorem contract_0054 :
    ∀ (N : Nat) (z : List.{0} Bool) (A : Nat) (ρ : Paper37.BoundedLoop.Env),
      @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) N →
        @LE.le.{0} Nat instLENat (@List.length.{0} Bool z) N →
          @LE.le.{0} Nat instLENat A N →
            @Eq.{1} Paper37.BoundedLoop.Value (ρ (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                (Paper37.BoundedLoop.Value.nat N) →
              @Eq.{1} Paper37.BoundedLoop.Value (ρ (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  (Paper37.BoundedLoop.Value.nat A) →
                @Eq.{1} Paper37.BoundedLoop.Value (ρ (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (@Paper37.CachedCoreProgram.chooseValue N (Paper37.CachedDP.makeObservedCache N z)) →
                  @Eq.{1} Paper37.BoundedLoop.Value (ρ (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                      (@Paper37.CachedCoreProgram.powerValue N (Paper37.CachedDP.makeObservedCache N z)) →
                    @Eq.{1} Paper37.BoundedLoop.Value (ρ (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                        (@Paper37.CachedCoreProgram.observedValue N (Paper37.CachedDP.makeObservedCache N z)) →
                      And
                        (@Eq.{1} Paper37.BoundedLoop.Value
                          (Paper37.BoundedLoop.Expr.eval ρ Paper37.CachedCoreProgram.coreProgram)
                          (@Paper37.CachedCoreProgram.layerValue N
                            (Paper37.DP.run N (Paper37.ContinuationDP.observedCounts z) A N)))
                        (And
                          (@LE.le.{0} Nat instLENat (Paper37.BoundedLoop.Expr.work ρ Paper37.CachedCoreProgram.coreProgram)
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@OfNat.ofNat.{0} Nat (nat_lit 200) (instOfNatNat (nat_lit 200)))
                              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                (@instHPow.{0, 0} Nat Nat (@Monoid.toNatPow.{0} Nat Nat.instMonoid))
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) N
                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))
                          (@LE.le.{0} Nat instLENat (Paper37.BoundedLoop.Expr.peak ρ Paper37.CachedCoreProgram.coreProgram)
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@OfNat.ofNat.{0} Nat (nat_lit 101000000) (instOfNatNat (nat_lit 101000000)))
                              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                (@instHPow.{0, 0} Nat Nat (@Monoid.toNatPow.{0} Nat Nat.instMonoid))
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) N
                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))))) := @Paper37.CachedCoreProgram.source_core_certificate

theorem contract_0055 :
    ∀ (N : Nat) (z : List.{0} Bool) (A d : Nat),
      @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) N →
        @LE.le.{0} Nat instLENat (@List.length.{0} Bool z) N →
          @LT.lt.{0} Nat instLTNat d N →
            @LE.le.{0} Nat instLENat (Paper37.CachedCoreProgram.workingSet N z A d)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 250) (instOfNatNat (nat_lit 250)))
                  (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@Monoid.toNatPow.{0} Nat Nat.instMonoid))
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) N
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) N.size
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) := @Paper37.CachedCoreProgram.workingSet_binary

theorem contract_0056 :
    ∀ (N : Nat) (z : List.{0} Bool) (A : Nat) (ρ : Paper37.BoundedLoop.Env),
      @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) N →
        @LE.le.{0} Nat instLENat (@List.length.{0} Bool z) N →
          @LE.le.{0} Nat instLENat A N →
            @Eq.{1} Paper37.BoundedLoop.Value (ρ (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                (Paper37.BoundedLoop.Value.nat N) →
              @Eq.{1} Paper37.BoundedLoop.Value (ρ (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  (Paper37.BoundedLoop.Value.nat A) →
                @Eq.{1} Paper37.BoundedLoop.Value (ρ (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (@Paper37.CachedCoreProgram.chooseValue N (Paper37.CachedDP.makeObservedCache N z)) →
                  @Eq.{1} Paper37.BoundedLoop.Value (ρ (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                      (@Paper37.CachedCoreProgram.powerValue N (Paper37.CachedDP.makeObservedCache N z)) →
                    @Eq.{1} Paper37.BoundedLoop.Value (ρ (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                        (@Paper37.CachedCoreProgram.observedValue N (Paper37.CachedDP.makeObservedCache N z)) →
                      And
                        (@Eq.{1} Paper37.BoundedLoop.Value
                          (Paper37.BoundedLoop.Expr.eval ρ Paper37.RefinedCoreProgram.coreProgram)
                          (@Paper37.RefinedCoreProgram.layerValue N
                            (Paper37.AdaptiveDP.refinedRun N (Paper37.ContinuationDP.observedCounts z) A N)))
                        (And
                          (@LE.le.{0} Nat instLENat (Paper37.BoundedLoop.Expr.work ρ Paper37.RefinedCoreProgram.coreProgram)
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@OfNat.ofNat.{0} Nat (nat_lit 400) (instOfNatNat (nat_lit 400)))
                              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                (@instHPow.{0, 0} Nat Nat (@Monoid.toNatPow.{0} Nat Nat.instMonoid))
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) N
                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))))
                          (@LE.le.{0} Nat instLENat (Paper37.BoundedLoop.Expr.peak ρ Paper37.RefinedCoreProgram.coreProgram)
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@OfNat.ofNat.{0} Nat (nat_lit 2510000000) (instOfNatNat (nat_lit 2510000000)))
                              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                (@instHPow.{0, 0} Nat Nat (@Monoid.toNatPow.{0} Nat Nat.instMonoid))
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) N
                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))))) := @Paper37.RefinedCoreProgram.source_core_certificate

theorem contract_0057 :
    ∀ (N : Nat) (z : List.{0} Bool) (A d : Nat),
      @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) N →
        @LE.le.{0} Nat instLENat (@List.length.{0} Bool z) N →
          @LT.lt.{0} Nat instLTNat d N →
            @LE.le.{0} Nat instLENat (Paper37.RefinedCoreProgram.workingSet N z A d)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2000) (instOfNatNat (nat_lit 2000)))
                  (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@Monoid.toNatPow.{0} Nat Nat.instMonoid))
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) N
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) N.size
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) := @Paper37.RefinedCoreProgram.workingSet_binary

theorem contract_0058 :
    ∀ (ρ : Paper37.BoundedLoop.Env) (H : Nat) (z : List.{0} Bool) (R : Nat),
      @Eq.{1} Paper37.BoundedLoop.Value (ρ (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (Paper37.BoundedLoop.Value.nat H) →
        @Eq.{1} Paper37.BoundedLoop.Value (ρ (@OfNat.ofNat.{0} Nat (nat_lit 40) (instOfNatNat (nat_lit 40))))
            (Paper37.WordProgram.wordValue z) →
          @Eq.{1} Paper37.BoundedLoop.Value (ρ (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))))
              (Paper37.BoundedLoop.Value.nat R) →
            @LE.le.{0} Nat instLENat
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@List.length.{0} Bool z) R) H →
              @LE.le.{0} Nat instLENat (Paper37.BoundedLoop.Expr.work ρ Paper37.IntegerPredictorProgram.continuationProgram)
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 1000) (instOfNatNat (nat_lit 1000)))
                  (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@Monoid.toNatPow.{0} Nat Nat.instMonoid))
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) H
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))) := @Paper37.IntegerPredictorProgram.continuationProgram_work

theorem contract_0059 :
    ∀ (ρ : Paper37.BoundedLoop.Env) (H : Nat) (z : List.{0} Bool) (R : Nat),
      @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) H →
        @Eq.{1} Paper37.BoundedLoop.Value (ρ (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
            (Paper37.BoundedLoop.Value.nat H) →
          @Eq.{1} Paper37.BoundedLoop.Value (ρ (@OfNat.ofNat.{0} Nat (nat_lit 40) (instOfNatNat (nat_lit 40))))
              (Paper37.WordProgram.wordValue z) →
            @Eq.{1} Paper37.BoundedLoop.Value (ρ (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))))
                (Paper37.BoundedLoop.Value.nat R) →
              @LE.le.{0} Nat instLENat
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@List.length.{0} Bool z) R) H →
                @LE.le.{0} Nat instLENat
                  (Paper37.BoundedLoop.Expr.peak ρ Paper37.IntegerPredictorProgram.continuationProgram)
                  (Paper37.IntegerQueryProgramPeak.queryPeakBound H) := @Paper37.IntegerQueryProgramPeak.continuationProgram_peak

theorem contract_0060 :
    ∀ (ρ : Paper37.BoundedLoop.Env) (H : Nat) (y : List.{0} Bool),
      @Eq.{1} Paper37.BoundedLoop.Value (ρ (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (Paper37.BoundedLoop.Value.nat H) →
        @Eq.{1} Paper37.BoundedLoop.Value (ρ (@OfNat.ofNat.{0} Nat (nat_lit 40) (instOfNatNat (nat_lit 40))))
            (Paper37.WordProgram.wordValue y) →
          @LT.lt.{0} Nat instLTNat (@List.length.{0} Bool y) H →
            @LE.le.{0} Nat instLENat (Paper37.BoundedLoop.Expr.peak ρ Paper37.IntegerPredictorProgram.conditionalProgram)
              (Paper37.IntegerQueryProgramPeak.queryPeakBound H) := @Paper37.IntegerQueryProgramPeak.conditionalProgram_peak

theorem contract_0061 :
    ∀ (ρ : Paper37.BoundedLoop.Env) (x : List.{0} Bool),
      @Eq.{1} Paper37.BoundedLoop.Value (ρ (@OfNat.ofNat.{0} Nat (nat_lit 40) (instOfNatNat (nat_lit 40))))
          (Paper37.WordProgram.wordValue x) →
        @LE.le.{0} Nat instLENat (Paper37.BoundedLoop.Expr.peak ρ Paper37.IntegerPredictorProgram.predictorProgram)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 100000000000000000000) (instOfNatNat (nat_lit 100000000000000000000)))
            (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@Monoid.toNatPow.{0} Nat Nat.instMonoid))
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@List.length.{0} Bool x)
                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (@OfNat.ofNat.{0} Nat (nat_lit 13) (instOfNatNat (nat_lit 13))))) := @Paper37.IntegerPredictorProgram.predictorProgram_peak

theorem contract_0062 :
    Paper37.BoundedLoopMachine.BoundedLoopSimulationPrinciple →
      @Exists.{2}
        (@Turing.TM2ComputableInPolyTime (List.{0} Bool) Paper37.BoundedLoop.Value
          Paper37.UniformPredictionMachine.sourceEncoding Paper37.BoundedLoopEncoding.valueEncoding
          Paper37.UniformPredictionMachine.sourceRun)
        fun M =>
        And
          (∀
            (k :
              (@Turing.TM2ComputableAux.tm
                  (@Computability.Encoding.Γ.{0, 0} (List.{0} Bool)
                    (@Computability.FinEncoding.toEncoding.{0} (List.{0} Bool)
                      Paper37.UniformPredictionMachine.sourceEncoding))
                  (@Computability.Encoding.Γ.{0, 0} Paper37.BoundedLoop.Value
                    (@Computability.FinEncoding.toEncoding.{0} Paper37.BoundedLoop.Value
                      Paper37.BoundedLoopEncoding.valueEncoding))
                  (@Turing.TM2ComputableInPolyTime.toTM2ComputableAux (List.{0} Bool) Paper37.BoundedLoop.Value
                    Paper37.UniformPredictionMachine.sourceEncoding Paper37.BoundedLoopEncoding.valueEncoding
                    Paper37.UniformPredictionMachine.sourceRun M)).K),
            Finite.{1}
              ((@Turing.TM2ComputableAux.tm
                    (@Computability.Encoding.Γ.{0, 0} (List.{0} Bool)
                      (@Computability.FinEncoding.toEncoding.{0} (List.{0} Bool)
                        Paper37.UniformPredictionMachine.sourceEncoding))
                    (@Computability.Encoding.Γ.{0, 0} Paper37.BoundedLoop.Value
                      (@Computability.FinEncoding.toEncoding.{0} Paper37.BoundedLoop.Value
                        Paper37.BoundedLoopEncoding.valueEncoding))
                    (@Turing.TM2ComputableInPolyTime.toTM2ComputableAux (List.{0} Bool) Paper37.BoundedLoop.Value
                      Paper37.UniformPredictionMachine.sourceEncoding Paper37.BoundedLoopEncoding.valueEncoding
                      Paper37.UniformPredictionMachine.sourceRun M)).Γ
                k))
          (And
            (∀ (x : List.{0} Bool),
              @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                  (@List.length.{0} Bool x) →
                @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                  (@Option.getD.{0} Paper37.BoundedLoop.Value
                      (@GetElem?.getElem?.{0, 0, 0} (List.{0} Paper37.BoundedLoop.Value) Nat Paper37.BoundedLoop.Value
                        (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Paper37.BoundedLoop.Value as))
                        (@List.instGetElem?NatLtLength.{0} Paper37.BoundedLoop.Value)
                        (Paper37.UniformPredictionMachine.sourceRun x).arrayVal
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                      (Paper37.BoundedLoop.Value.nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))).natVal)
            (∀ (x : List.{0} Bool),
              @Eq.{1} Rat
                (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
                  (@Nat.cast.{0} Rat Rat.instNatCast
                    (@Option.getD.{0} Paper37.BoundedLoop.Value
                        (@GetElem?.getElem?.{0, 0, 0} (List.{0} Paper37.BoundedLoop.Value) Nat Paper37.BoundedLoop.Value
                          (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Paper37.BoundedLoop.Value as))
                          (@List.instGetElem?NatLtLength.{0} Paper37.BoundedLoop.Value)
                          (Paper37.UniformPredictionMachine.sourceRun x).arrayVal
                          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                        (Paper37.BoundedLoop.Value.nat
                          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))).natVal)
                  (@Nat.cast.{0} Rat Rat.instNatCast
                    (@Option.getD.{0} Paper37.BoundedLoop.Value
                        (@GetElem?.getElem?.{0, 0, 0} (List.{0} Paper37.BoundedLoop.Value) Nat Paper37.BoundedLoop.Value
                          (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Paper37.BoundedLoop.Value as))
                          (@List.instGetElem?NatLtLength.{0} Paper37.BoundedLoop.Value)
                          (Paper37.UniformPredictionMachine.sourceRun x).arrayVal
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                        (Paper37.BoundedLoop.Value.nat
                          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))).natVal))
                (Paper37.Prediction.predict (@List.length.{0} Bool x) x))) := @Paper37.UniformPredictionMachine.actualPredictor_polytime

theorem contract_0063 :
    Paper37.BoundedLoopMachine.BoundedLoopSimulationPrinciple →
      @Exists.{2}
        (@Turing.TM2ComputableInPolyTime Paper37.UniformQueryMachine.Query Paper37.BoundedLoop.Value
          Paper37.UniformQueryMachine.queryEncoding Paper37.BoundedLoopEncoding.valueEncoding
          Paper37.UniformQueryMachine.queryRun)
        fun M =>
        And
          (∀
            (k :
              (@Turing.TM2ComputableAux.tm
                  (@Computability.Encoding.Γ.{0, 0} Paper37.UniformQueryMachine.Query
                    (@Computability.FinEncoding.toEncoding.{0} Paper37.UniformQueryMachine.Query
                      Paper37.UniformQueryMachine.queryEncoding))
                  (@Computability.Encoding.Γ.{0, 0} Paper37.BoundedLoop.Value
                    (@Computability.FinEncoding.toEncoding.{0} Paper37.BoundedLoop.Value
                      Paper37.BoundedLoopEncoding.valueEncoding))
                  (@Turing.TM2ComputableInPolyTime.toTM2ComputableAux Paper37.UniformQueryMachine.Query
                    Paper37.BoundedLoop.Value Paper37.UniformQueryMachine.queryEncoding
                    Paper37.BoundedLoopEncoding.valueEncoding Paper37.UniformQueryMachine.queryRun M)).K),
            Finite.{1}
              ((@Turing.TM2ComputableAux.tm
                    (@Computability.Encoding.Γ.{0, 0} Paper37.UniformQueryMachine.Query
                      (@Computability.FinEncoding.toEncoding.{0} Paper37.UniformQueryMachine.Query
                        Paper37.UniformQueryMachine.queryEncoding))
                    (@Computability.Encoding.Γ.{0, 0} Paper37.BoundedLoop.Value
                      (@Computability.FinEncoding.toEncoding.{0} Paper37.BoundedLoop.Value
                        Paper37.BoundedLoopEncoding.valueEncoding))
                    (@Turing.TM2ComputableInPolyTime.toTM2ComputableAux Paper37.UniformQueryMachine.Query
                      Paper37.BoundedLoop.Value Paper37.UniformQueryMachine.queryEncoding
                      Paper37.BoundedLoopEncoding.valueEncoding Paper37.UniformQueryMachine.queryRun M)).Γ
                k))
          (And
            (∀ (q : Paper37.UniformQueryMachine.Query),
              @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                (@Option.getD.{0} Paper37.BoundedLoop.Value
                    (@GetElem?.getElem?.{0, 0, 0} (List.{0} Paper37.BoundedLoop.Value) Nat Paper37.BoundedLoop.Value
                      (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Paper37.BoundedLoop.Value as))
                      (@List.instGetElem?NatLtLength.{0} Paper37.BoundedLoop.Value)
                      (Paper37.UniformQueryMachine.queryRun q).arrayVal
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                    (Paper37.BoundedLoop.Value.nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))).natVal)
            (∀ (q : Paper37.UniformQueryMachine.Query),
              @Eq.{1} Rat
                (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
                  (@Nat.cast.{0} Rat Rat.instNatCast
                    (@Option.getD.{0} Paper37.BoundedLoop.Value
                        (@GetElem?.getElem?.{0, 0, 0} (List.{0} Paper37.BoundedLoop.Value) Nat Paper37.BoundedLoop.Value
                          (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Paper37.BoundedLoop.Value as))
                          (@List.instGetElem?NatLtLength.{0} Paper37.BoundedLoop.Value)
                          (Paper37.UniformQueryMachine.queryRun q).arrayVal
                          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                        (Paper37.BoundedLoop.Value.nat
                          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))).natVal)
                  (@Nat.cast.{0} Rat Rat.instNatCast
                    (@Option.getD.{0} Paper37.BoundedLoop.Value
                        (@GetElem?.getElem?.{0, 0, 0} (List.{0} Paper37.BoundedLoop.Value) Nat Paper37.BoundedLoop.Value
                          (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Paper37.BoundedLoop.Value as))
                          (@List.instGetElem?NatLtLength.{0} Paper37.BoundedLoop.Value)
                          (Paper37.UniformQueryMachine.queryRun q).arrayVal
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                        (Paper37.BoundedLoop.Value.nat
                          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))).natVal))
                (Paper37.Prediction.continuationMass
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@List.length.{0} Bool q.word)
                    q.remaining)
                  q.word))) := @Paper37.UniformQueryMachine.actualContinuation_polytime

theorem contract_0064 :
    Paper37.BoundedLoopMachine.BoundedLoopSimulationPrinciple →
      @Exists.{2}
        (@Turing.TM2ComputableInPolyTime Paper37.UniformConditionalMachine.ConditionalQuery Paper37.BoundedLoop.Value
          Paper37.UniformConditionalMachine.conditionalEncoding Paper37.BoundedLoopEncoding.valueEncoding
          Paper37.UniformConditionalMachine.conditionalRun)
        fun M =>
        And
          (∀
            (k :
              (@Turing.TM2ComputableAux.tm
                  (@Computability.Encoding.Γ.{0, 0} Paper37.UniformConditionalMachine.ConditionalQuery
                    (@Computability.FinEncoding.toEncoding.{0} Paper37.UniformConditionalMachine.ConditionalQuery
                      Paper37.UniformConditionalMachine.conditionalEncoding))
                  (@Computability.Encoding.Γ.{0, 0} Paper37.BoundedLoop.Value
                    (@Computability.FinEncoding.toEncoding.{0} Paper37.BoundedLoop.Value
                      Paper37.BoundedLoopEncoding.valueEncoding))
                  (@Turing.TM2ComputableInPolyTime.toTM2ComputableAux Paper37.UniformConditionalMachine.ConditionalQuery
                    Paper37.BoundedLoop.Value Paper37.UniformConditionalMachine.conditionalEncoding
                    Paper37.BoundedLoopEncoding.valueEncoding Paper37.UniformConditionalMachine.conditionalRun M)).K),
            Finite.{1}
              ((@Turing.TM2ComputableAux.tm
                    (@Computability.Encoding.Γ.{0, 0} Paper37.UniformConditionalMachine.ConditionalQuery
                      (@Computability.FinEncoding.toEncoding.{0} Paper37.UniformConditionalMachine.ConditionalQuery
                        Paper37.UniformConditionalMachine.conditionalEncoding))
                    (@Computability.Encoding.Γ.{0, 0} Paper37.BoundedLoop.Value
                      (@Computability.FinEncoding.toEncoding.{0} Paper37.BoundedLoop.Value
                        Paper37.BoundedLoopEncoding.valueEncoding))
                    (@Turing.TM2ComputableInPolyTime.toTM2ComputableAux Paper37.UniformConditionalMachine.ConditionalQuery
                      Paper37.BoundedLoop.Value Paper37.UniformConditionalMachine.conditionalEncoding
                      Paper37.BoundedLoopEncoding.valueEncoding Paper37.UniformConditionalMachine.conditionalRun M)).Γ
                k))
          (And
            (∀ (q : Paper37.UniformConditionalMachine.ConditionalQuery),
              @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                (@Option.getD.{0} Paper37.BoundedLoop.Value
                    (@GetElem?.getElem?.{0, 0, 0} (List.{0} Paper37.BoundedLoop.Value) Nat Paper37.BoundedLoop.Value
                      (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Paper37.BoundedLoop.Value as))
                      (@List.instGetElem?NatLtLength.{0} Paper37.BoundedLoop.Value)
                      (Paper37.UniformConditionalMachine.conditionalRun q).arrayVal
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                    (Paper37.BoundedLoop.Value.nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))).natVal)
            (∀ (q : Paper37.UniformConditionalMachine.ConditionalQuery),
              @Eq.{1} Rat
                (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
                  (@Nat.cast.{0} Rat Rat.instNatCast
                    (@Option.getD.{0} Paper37.BoundedLoop.Value
                        (@GetElem?.getElem?.{0, 0, 0} (List.{0} Paper37.BoundedLoop.Value) Nat Paper37.BoundedLoop.Value
                          (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Paper37.BoundedLoop.Value as))
                          (@List.instGetElem?NatLtLength.{0} Paper37.BoundedLoop.Value)
                          (Paper37.UniformConditionalMachine.conditionalRun q).arrayVal
                          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                        (Paper37.BoundedLoop.Value.nat
                          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))).natVal)
                  (@Nat.cast.{0} Rat Rat.instNatCast
                    (@Option.getD.{0} Paper37.BoundedLoop.Value
                        (@GetElem?.getElem?.{0, 0, 0} (List.{0} Paper37.BoundedLoop.Value) Nat Paper37.BoundedLoop.Value
                          (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Paper37.BoundedLoop.Value as))
                          (@List.instGetElem?NatLtLength.{0} Paper37.BoundedLoop.Value)
                          (Paper37.UniformConditionalMachine.conditionalRun q).arrayVal
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                        (Paper37.BoundedLoop.Value.nat
                          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))).natVal))
                (Paper37.Prediction.blockConditional q.horizon q.word))) := @Paper37.UniformConditionalMachine.actualConditional_polytime

theorem contract_0065 :
    Paper37.BoundedLoopMachine.BoundedLoopSimulationPrinciple →
      @Exists.{2}
        (@Turing.TM2ComputableInPolyTime Nat Paper37.BoundedLoop.Value Paper37.UniformNormalizerMachine.normalizerEncoding
          Paper37.BoundedLoopEncoding.valueEncoding Paper37.UniformNormalizerMachine.normalizerRun)
        fun M =>
        And
          (∀
            (k :
              (@Turing.TM2ComputableAux.tm
                  (@Computability.Encoding.Γ.{0, 0} Nat
                    (@Computability.FinEncoding.toEncoding.{0} Nat Paper37.UniformNormalizerMachine.normalizerEncoding))
                  (@Computability.Encoding.Γ.{0, 0} Paper37.BoundedLoop.Value
                    (@Computability.FinEncoding.toEncoding.{0} Paper37.BoundedLoop.Value
                      Paper37.BoundedLoopEncoding.valueEncoding))
                  (@Turing.TM2ComputableInPolyTime.toTM2ComputableAux Nat Paper37.BoundedLoop.Value
                    Paper37.UniformNormalizerMachine.normalizerEncoding Paper37.BoundedLoopEncoding.valueEncoding
                    Paper37.UniformNormalizerMachine.normalizerRun M)).K),
            Finite.{1}
              ((@Turing.TM2ComputableAux.tm
                    (@Computability.Encoding.Γ.{0, 0} Nat
                      (@Computability.FinEncoding.toEncoding.{0} Nat Paper37.UniformNormalizerMachine.normalizerEncoding))
                    (@Computability.Encoding.Γ.{0, 0} Paper37.BoundedLoop.Value
                      (@Computability.FinEncoding.toEncoding.{0} Paper37.BoundedLoop.Value
                        Paper37.BoundedLoopEncoding.valueEncoding))
                    (@Turing.TM2ComputableInPolyTime.toTM2ComputableAux Nat Paper37.BoundedLoop.Value
                      Paper37.UniformNormalizerMachine.normalizerEncoding Paper37.BoundedLoopEncoding.valueEncoding
                      Paper37.UniformNormalizerMachine.normalizerRun M)).Γ
                k))
          (And
            (∀ (L : Nat),
              @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                (@Option.getD.{0} Paper37.BoundedLoop.Value
                    (@GetElem?.getElem?.{0, 0, 0} (List.{0} Paper37.BoundedLoop.Value) Nat Paper37.BoundedLoop.Value
                      (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Paper37.BoundedLoop.Value as))
                      (@List.instGetElem?NatLtLength.{0} Paper37.BoundedLoop.Value)
                      (Paper37.UniformNormalizerMachine.normalizerRun L).arrayVal
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                    (Paper37.BoundedLoop.Value.nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))).natVal)
            (∀ (L : Nat),
              @Eq.{1} Rat
                (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
                  (@Nat.cast.{0} Rat Rat.instNatCast
                    (@Option.getD.{0} Paper37.BoundedLoop.Value
                        (@GetElem?.getElem?.{0, 0, 0} (List.{0} Paper37.BoundedLoop.Value) Nat Paper37.BoundedLoop.Value
                          (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Paper37.BoundedLoop.Value as))
                          (@List.instGetElem?NatLtLength.{0} Paper37.BoundedLoop.Value)
                          (Paper37.UniformNormalizerMachine.normalizerRun L).arrayVal
                          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                        (Paper37.BoundedLoop.Value.nat
                          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))).natVal)
                  (@Nat.cast.{0} Rat Rat.instNatCast
                    (@Option.getD.{0} Paper37.BoundedLoop.Value
                        (@GetElem?.getElem?.{0, 0, 0} (List.{0} Paper37.BoundedLoop.Value) Nat Paper37.BoundedLoop.Value
                          (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Paper37.BoundedLoop.Value as))
                          (@List.instGetElem?NatLtLength.{0} Paper37.BoundedLoop.Value)
                          (Paper37.UniformNormalizerMachine.normalizerRun L).arrayVal
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                        (Paper37.BoundedLoop.Value.nat
                          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))).natVal))
                (Paper37.Prediction.ordinaryNormalizer L))) := @Paper37.UniformNormalizerMachine.actualNormalizer_polytime

theorem contract_0066 :
    ∀ (ρ : Paper37.BoundedLoop.Env) (x : List.{0} Bool),
      @Eq.{1} Paper37.BoundedLoop.Value (ρ (@OfNat.ofNat.{0} Nat (nat_lit 40) (instOfNatNat (nat_lit 40))))
          (Paper37.WordProgram.wordValue x) →
        have out := Paper37.BoundedLoop.Expr.eval ρ Paper37.AdaptiveQueryProgram.predictorProgram;
        @Eq.{1} Rat
          (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
            (@Nat.cast.{0} Rat Rat.instNatCast
              (@Option.getD.{0} Paper37.BoundedLoop.Value
                  (@GetElem?.getElem?.{0, 0, 0} (List.{0} Paper37.BoundedLoop.Value) Nat Paper37.BoundedLoop.Value
                    (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Paper37.BoundedLoop.Value as))
                    (@List.instGetElem?NatLtLength.{0} Paper37.BoundedLoop.Value) out.arrayVal
                    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                  (Paper37.BoundedLoop.Value.nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))).natVal)
            (@Nat.cast.{0} Rat Rat.instNatCast
              (@Option.getD.{0} Paper37.BoundedLoop.Value
                  (@GetElem?.getElem?.{0, 0, 0} (List.{0} Paper37.BoundedLoop.Value) Nat Paper37.BoundedLoop.Value
                    (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Paper37.BoundedLoop.Value as))
                    (@List.instGetElem?NatLtLength.{0} Paper37.BoundedLoop.Value) out.arrayVal
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  (Paper37.BoundedLoop.Value.nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))).natVal))
          (Paper37.Adaptive.adaptivePredict (@List.length.{0} Bool x) x) := @Paper37.AdaptiveQueryProgram.predictorProgram_source

theorem contract_0067 :
    ∀ (ρ : Paper37.BoundedLoop.Env) (x : List.{0} Bool),
      @Eq.{1} Paper37.BoundedLoop.Value (ρ (@OfNat.ofNat.{0} Nat (nat_lit 40) (instOfNatNat (nat_lit 40))))
          (Paper37.WordProgram.wordValue x) →
        @LE.le.{0} Nat instLENat (Paper37.BoundedLoop.Expr.work ρ Paper37.AdaptiveQueryProgram.predictorProgram)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 6000) (instOfNatNat (nat_lit 6000)))
            (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@Monoid.toNatPow.{0} Nat Nat.instMonoid))
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@List.length.{0} Bool x)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))) := @Paper37.AdaptiveQueryProgram.predictorProgram_work

theorem contract_0068 :
    ∀ (ρ : Paper37.BoundedLoop.Env) (x : List.{0} Bool),
      @Eq.{1} Paper37.BoundedLoop.Value (ρ (@OfNat.ofNat.{0} Nat (nat_lit 40) (instOfNatNat (nat_lit 40))))
          (Paper37.WordProgram.wordValue x) →
        @LE.le.{0} Nat instLENat (Paper37.BoundedLoop.Expr.peak ρ Paper37.AdaptiveQueryProgram.predictorProgram)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@Monoid.toNatPow.{0} Nat Nat.instMonoid))
              (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10)))
              (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30))))
            (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@Monoid.toNatPow.{0} Nat Nat.instMonoid))
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@List.length.{0} Bool x)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (@OfNat.ofNat.{0} Nat (nat_lit 21) (instOfNatNat (nat_lit 21))))) := @Paper37.AdaptiveQueryPeak.predictorProgram_peak

theorem contract_0069 :
    Paper37.BoundedLoopMachine.BoundedLoopSimulationPrinciple →
      @Exists.{2}
        (@Turing.TM2ComputableInPolyTime (List.{0} Bool) Paper37.BoundedLoop.Value
          Paper37.UniformPredictionMachine.sourceEncoding Paper37.BoundedLoopEncoding.valueEncoding
          Paper37.UniformAdaptivePredictionMachine.sourceRun)
        fun M =>
        ∀
          (k :
            (@Turing.TM2ComputableAux.tm
                (@Computability.Encoding.Γ.{0, 0} (List.{0} Bool)
                  (@Computability.FinEncoding.toEncoding.{0} (List.{0} Bool)
                    Paper37.UniformPredictionMachine.sourceEncoding))
                (@Computability.Encoding.Γ.{0, 0} Paper37.BoundedLoop.Value
                  (@Computability.FinEncoding.toEncoding.{0} Paper37.BoundedLoop.Value
                    Paper37.BoundedLoopEncoding.valueEncoding))
                (@Turing.TM2ComputableInPolyTime.toTM2ComputableAux (List.{0} Bool) Paper37.BoundedLoop.Value
                  Paper37.UniformPredictionMachine.sourceEncoding Paper37.BoundedLoopEncoding.valueEncoding
                  Paper37.UniformAdaptivePredictionMachine.sourceRun M)).K),
          Finite.{1}
            ((@Turing.TM2ComputableAux.tm
                  (@Computability.Encoding.Γ.{0, 0} (List.{0} Bool)
                    (@Computability.FinEncoding.toEncoding.{0} (List.{0} Bool)
                      Paper37.UniformPredictionMachine.sourceEncoding))
                  (@Computability.Encoding.Γ.{0, 0} Paper37.BoundedLoop.Value
                    (@Computability.FinEncoding.toEncoding.{0} Paper37.BoundedLoop.Value
                      Paper37.BoundedLoopEncoding.valueEncoding))
                  (@Turing.TM2ComputableInPolyTime.toTM2ComputableAux (List.{0} Bool) Paper37.BoundedLoop.Value
                    Paper37.UniformPredictionMachine.sourceEncoding Paper37.BoundedLoopEncoding.valueEncoding
                    Paper37.UniformAdaptivePredictionMachine.sourceRun M)).Γ
              k) := @Paper37.UniformAdaptivePredictionMachine.sourceTM_exists

theorem contract_0070 :
    ∀ (x : List.{0} Bool),
      @Eq.{1} Rat
        (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
          (@Nat.cast.{0} Rat Rat.instNatCast
            (@Option.getD.{0} Paper37.BoundedLoop.Value
                (@GetElem?.getElem?.{0, 0, 0} (List.{0} Paper37.BoundedLoop.Value) Nat Paper37.BoundedLoop.Value
                  (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Paper37.BoundedLoop.Value as))
                  (@List.instGetElem?NatLtLength.{0} Paper37.BoundedLoop.Value)
                  (Paper37.UniformAdaptivePredictionMachine.sourceRun x).arrayVal
                  (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                (Paper37.BoundedLoop.Value.nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))).natVal)
          (@Nat.cast.{0} Rat Rat.instNatCast
            (@Option.getD.{0} Paper37.BoundedLoop.Value
                (@GetElem?.getElem?.{0, 0, 0} (List.{0} Paper37.BoundedLoop.Value) Nat Paper37.BoundedLoop.Value
                  (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Paper37.BoundedLoop.Value as))
                  (@List.instGetElem?NatLtLength.{0} Paper37.BoundedLoop.Value)
                  (Paper37.UniformAdaptivePredictionMachine.sourceRun x).arrayVal
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                (Paper37.BoundedLoop.Value.nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))).natVal))
        (Paper37.Adaptive.adaptivePredict (@List.length.{0} Bool x) x) := @Paper37.UniformAdaptivePredictionMachine.sourceRun_exact

theorem contract_0071 :
    Paper37.BoundedLoopMachine.BoundedLoopSimulationPrinciple →
      ∀ (strict : Bool),
        @Exists.{2}
          (@Turing.TM2ComputableInPolyTime (Paper37.UniformAdaptiveQueryMachine.Request strict) Paper37.BoundedLoop.Value
            (Paper37.UniformAdaptiveQueryMachine.requestEncoding strict) Paper37.BoundedLoopEncoding.valueEncoding
            (Paper37.UniformAdaptiveQueryMachine.requestRun strict))
          fun M =>
          And
            (∀
              (k :
                (@Turing.TM2ComputableAux.tm
                    (@Computability.Encoding.Γ.{0, 0} (Paper37.UniformAdaptiveQueryMachine.Request strict)
                      (@Computability.FinEncoding.toEncoding.{0} (Paper37.UniformAdaptiveQueryMachine.Request strict)
                        (Paper37.UniformAdaptiveQueryMachine.requestEncoding strict)))
                    (@Computability.Encoding.Γ.{0, 0} Paper37.BoundedLoop.Value
                      (@Computability.FinEncoding.toEncoding.{0} Paper37.BoundedLoop.Value
                        Paper37.BoundedLoopEncoding.valueEncoding))
                    (@Turing.TM2ComputableInPolyTime.toTM2ComputableAux (Paper37.UniformAdaptiveQueryMachine.Request strict)
                      Paper37.BoundedLoop.Value (Paper37.UniformAdaptiveQueryMachine.requestEncoding strict)
                      Paper37.BoundedLoopEncoding.valueEncoding (Paper37.UniformAdaptiveQueryMachine.requestRun strict)
                      M)).K),
              Finite.{1}
                ((@Turing.TM2ComputableAux.tm
                      (@Computability.Encoding.Γ.{0, 0} (Paper37.UniformAdaptiveQueryMachine.Request strict)
                        (@Computability.FinEncoding.toEncoding.{0} (Paper37.UniformAdaptiveQueryMachine.Request strict)
                          (Paper37.UniformAdaptiveQueryMachine.requestEncoding strict)))
                      (@Computability.Encoding.Γ.{0, 0} Paper37.BoundedLoop.Value
                        (@Computability.FinEncoding.toEncoding.{0} Paper37.BoundedLoop.Value
                          Paper37.BoundedLoopEncoding.valueEncoding))
                      (@Turing.TM2ComputableInPolyTime.toTM2ComputableAux
                        (Paper37.UniformAdaptiveQueryMachine.Request strict) Paper37.BoundedLoop.Value
                        (Paper37.UniformAdaptiveQueryMachine.requestEncoding strict)
                        Paper37.BoundedLoopEncoding.valueEncoding (Paper37.UniformAdaptiveQueryMachine.requestRun strict)
                        M)).Γ
                  k))
            (And
              (∀ (q : Paper37.UniformAdaptiveQueryMachine.Request strict),
                @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                  (@Option.getD.{0} Paper37.BoundedLoop.Value
                      (@GetElem?.getElem?.{0, 0, 0} (List.{0} Paper37.BoundedLoop.Value) Nat Paper37.BoundedLoop.Value
                        (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Paper37.BoundedLoop.Value as))
                        (@List.instGetElem?NatLtLength.{0} Paper37.BoundedLoop.Value)
                        (Paper37.UniformAdaptiveQueryMachine.requestRun strict q).arrayVal
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                      (Paper37.BoundedLoop.Value.nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))).natVal)
              (∀ (q : Paper37.UniformAdaptiveQueryMachine.Request strict),
                @Eq.{1} Rat
                  (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
                    (@Nat.cast.{0} Rat Rat.instNatCast
                      (@Option.getD.{0} Paper37.BoundedLoop.Value
                          (@GetElem?.getElem?.{0, 0, 0} (List.{0} Paper37.BoundedLoop.Value) Nat Paper37.BoundedLoop.Value
                            (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Paper37.BoundedLoop.Value as))
                            (@List.instGetElem?NatLtLength.{0} Paper37.BoundedLoop.Value)
                            (Paper37.UniformAdaptiveQueryMachine.requestRun strict q).arrayVal
                            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                          (Paper37.BoundedLoop.Value.nat
                            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))).natVal)
                    (@Nat.cast.{0} Rat Rat.instNatCast
                      (@Option.getD.{0} Paper37.BoundedLoop.Value
                          (@GetElem?.getElem?.{0, 0, 0} (List.{0} Paper37.BoundedLoop.Value) Nat Paper37.BoundedLoop.Value
                            (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Paper37.BoundedLoop.Value as))
                            (@List.instGetElem?NatLtLength.{0} Paper37.BoundedLoop.Value)
                            (Paper37.UniformAdaptiveQueryMachine.requestRun strict q).arrayVal
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                          (Paper37.BoundedLoop.Value.nat
                            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))).natVal))
                  (Paper37.UniformAdaptiveQueryMachine.sourceQuery strict q))) := @Paper37.UniformAdaptiveQueryMachine.actualQuery_polytime

theorem contract_0072 :
    ∀ (ρ : Paper37.BoundedLoop.Env) (H : Nat) (qs : List.{0} (List.{0} Bool)),
      @Eq.{1} Paper37.BoundedLoop.Value (ρ (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (Paper37.BoundedLoop.Value.nat H) →
        @Eq.{1} Paper37.BoundedLoop.Value (ρ (@OfNat.ofNat.{0} Nat (nat_lit 60) (instOfNatNat (nat_lit 60))))
            (Paper37.SpecifiedQueryBatch.wordsValue qs) →
          (∀ (y : List.{0} Bool),
              @Membership.mem.{0, 0} (List.{0} Bool) (List.{0} (List.{0} Bool)) (@List.instMembership.{0} (List.{0} Bool))
                  qs y →
                @LT.lt.{0} Nat instLTNat (@List.length.{0} Bool y) H) →
            @Eq.{1} Paper37.BoundedLoop.Value
              (Paper37.BoundedLoop.Expr.eval ρ
                (Paper37.SpecifiedQueryBatch.program Paper37.IntegerPredictorProgram.conditionalProgram))
              (Paper37.BoundedLoop.Value.array
                (@List.map.{0, 0} (List.{0} Bool) Paper37.BoundedLoop.Value
                  (fun y => Paper37.WordProgram.pairValue (Paper37.IntegerPredictor.conditionalPair H y)) qs)) := @Paper37.SpecifiedQueryBatch.standard_eval

theorem contract_0073 :
    ∀ (ρ : Paper37.BoundedLoop.Env) (H C : Nat) (qs : List.{0} (List.{0} Bool)),
      @Eq.{1} Paper37.BoundedLoop.Value (ρ (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (Paper37.BoundedLoop.Value.nat H) →
        @Eq.{1} Paper37.BoundedLoop.Value (ρ (@OfNat.ofNat.{0} Nat (nat_lit 60) (instOfNatNat (nat_lit 60))))
            (Paper37.SpecifiedQueryBatch.wordsValue qs) →
          (∀ (y : List.{0} Bool),
              @Membership.mem.{0, 0} (List.{0} Bool) (List.{0} (List.{0} Bool)) (@List.instMembership.{0} (List.{0} Bool))
                  qs y →
                @LT.lt.{0} Nat instLTNat (@List.length.{0} Bool y) H) →
            @LE.le.{0} Nat instLENat (@List.length.{0} (List.{0} Bool) qs)
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) C
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) H
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
              @LE.le.{0} Nat instLENat
                (Paper37.BoundedLoop.Expr.work ρ
                  (Paper37.SpecifiedQueryBatch.program Paper37.IntegerPredictorProgram.conditionalProgram))
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 2507) (instOfNatNat (nat_lit 2507))) C)
                    (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@Monoid.toNatPow.{0} Nat Nat.instMonoid))
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) H
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                      (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))))) := @Paper37.SpecifiedQueryBatch.standard_work

theorem contract_0074 :
    ∀ (ρ : Paper37.BoundedLoop.Env) (H C : Nat) (qs : List.{0} (List.{0} Bool)),
      @Eq.{1} Paper37.BoundedLoop.Value (ρ (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (Paper37.BoundedLoop.Value.nat H) →
        @Eq.{1} Paper37.BoundedLoop.Value (ρ (@OfNat.ofNat.{0} Nat (nat_lit 60) (instOfNatNat (nat_lit 60))))
            (Paper37.SpecifiedQueryBatch.wordsValue qs) →
          (∀ (y : List.{0} Bool),
              @Membership.mem.{0, 0} (List.{0} Bool) (List.{0} (List.{0} Bool)) (@List.instMembership.{0} (List.{0} Bool))
                  qs y →
                @LT.lt.{0} Nat instLTNat (@List.length.{0} Bool y) H) →
            @LE.le.{0} Nat instLENat (@List.length.{0} (List.{0} Bool) qs)
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) C
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) H
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
              @LE.le.{0} Nat instLENat
                (Paper37.BoundedLoop.Expr.peak ρ
                  (Paper37.SpecifiedQueryBatch.program Paper37.IntegerPredictorProgram.conditionalProgram))
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) C
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) H
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (Paper37.IntegerQueryProgramPeak.queryPeakBound H)
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) C
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) H
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) H)
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) C
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) H
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                    (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))))) := @Paper37.SpecifiedQueryBatch.standard_peak

theorem contract_0075 :
    ∀ (ρ : Paper37.BoundedLoop.Env) (H : Nat) (qs : List.{0} (List.{0} Bool)),
      @Eq.{1} Paper37.BoundedLoop.Value (ρ (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (Paper37.BoundedLoop.Value.nat H) →
        @Eq.{1} Paper37.BoundedLoop.Value (ρ (@OfNat.ofNat.{0} Nat (nat_lit 60) (instOfNatNat (nat_lit 60))))
            (Paper37.SpecifiedQueryBatch.wordsValue qs) →
          (∀ (y : List.{0} Bool),
              @Membership.mem.{0, 0} (List.{0} Bool) (List.{0} (List.{0} Bool)) (@List.instMembership.{0} (List.{0} Bool))
                  qs y →
                @LT.lt.{0} Nat instLTNat (@List.length.{0} Bool y) H) →
            @Eq.{1} Paper37.BoundedLoop.Value
              (Paper37.BoundedLoop.Expr.eval ρ
                (Paper37.SpecifiedQueryBatch.program Paper37.AdaptiveQueryProgram.conditionalProgram))
              (Paper37.BoundedLoop.Value.array
                (@List.map.{0, 0} (List.{0} Bool) Paper37.BoundedLoop.Value
                  (fun y => Paper37.WordProgram.pairValue (Paper37.AdaptiveIntegerOutput.conditionalPair H y)) qs)) := @Paper37.SpecifiedQueryBatch.adaptive_eval

theorem contract_0076 :
    ∀ (ρ : Paper37.BoundedLoop.Env) (H C : Nat) (qs : List.{0} (List.{0} Bool)),
      @Eq.{1} Paper37.BoundedLoop.Value (ρ (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (Paper37.BoundedLoop.Value.nat H) →
        @Eq.{1} Paper37.BoundedLoop.Value (ρ (@OfNat.ofNat.{0} Nat (nat_lit 60) (instOfNatNat (nat_lit 60))))
            (Paper37.SpecifiedQueryBatch.wordsValue qs) →
          (∀ (y : List.{0} Bool),
              @Membership.mem.{0, 0} (List.{0} Bool) (List.{0} (List.{0} Bool)) (@List.instMembership.{0} (List.{0} Bool))
                  qs y →
                @LT.lt.{0} Nat instLTNat (@List.length.{0} Bool y) H) →
            @LE.le.{0} Nat instLENat (@List.length.{0} (List.{0} Bool) qs)
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) C
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) H
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
              @LE.le.{0} Nat instLENat
                (Paper37.BoundedLoop.Expr.work ρ
                  (Paper37.SpecifiedQueryBatch.program Paper37.AdaptiveQueryProgram.conditionalProgram))
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 5107) (instOfNatNat (nat_lit 5107))) C)
                    (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@Monoid.toNatPow.{0} Nat Nat.instMonoid))
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) H
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                      (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))) := @Paper37.SpecifiedQueryBatch.adaptive_work

theorem contract_0077 :
    ∀ (ρ : Paper37.BoundedLoop.Env) (H C : Nat) (qs : List.{0} (List.{0} Bool)),
      @Eq.{1} Paper37.BoundedLoop.Value (ρ (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (Paper37.BoundedLoop.Value.nat H) →
        @Eq.{1} Paper37.BoundedLoop.Value (ρ (@OfNat.ofNat.{0} Nat (nat_lit 60) (instOfNatNat (nat_lit 60))))
            (Paper37.SpecifiedQueryBatch.wordsValue qs) →
          (∀ (y : List.{0} Bool),
              @Membership.mem.{0, 0} (List.{0} Bool) (List.{0} (List.{0} Bool)) (@List.instMembership.{0} (List.{0} Bool))
                  qs y →
                @LT.lt.{0} Nat instLTNat (@List.length.{0} Bool y) H) →
            @LE.le.{0} Nat instLENat (@List.length.{0} (List.{0} Bool) qs)
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) C
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) H
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
              @LE.le.{0} Nat instLENat
                (Paper37.BoundedLoop.Expr.peak ρ
                  (Paper37.SpecifiedQueryBatch.program Paper37.AdaptiveQueryProgram.conditionalProgram))
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) C
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) H
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (Paper37.AdaptiveQueryPeak.queryPeakBound H)
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) C
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) H
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) H)
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) C
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) H
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                    (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))))) := @Paper37.SpecifiedQueryBatch.adaptive_peak

theorem contract_0078 :
    Paper37.BoundedLoopMachine.BoundedLoopSimulationPrinciple →
      @Exists.{2}
        (@Turing.TM2ComputableInPolyTime Paper37.UniformBatchMachine.BatchQuery Paper37.BoundedLoop.Value
          Paper37.UniformBatchMachine.batchEncoding Paper37.BoundedLoopEncoding.valueEncoding
          (Paper37.UniformBatchMachine.batchRun Paper37.IntegerPredictorProgram.conditionalProgram))
        fun M =>
        And
          (∀
            (k :
              (@Turing.TM2ComputableAux.tm
                  (@Computability.Encoding.Γ.{0, 0} Paper37.UniformBatchMachine.BatchQuery
                    (@Computability.FinEncoding.toEncoding.{0} Paper37.UniformBatchMachine.BatchQuery
                      Paper37.UniformBatchMachine.batchEncoding))
                  (@Computability.Encoding.Γ.{0, 0} Paper37.BoundedLoop.Value
                    (@Computability.FinEncoding.toEncoding.{0} Paper37.BoundedLoop.Value
                      Paper37.BoundedLoopEncoding.valueEncoding))
                  (@Turing.TM2ComputableInPolyTime.toTM2ComputableAux Paper37.UniformBatchMachine.BatchQuery
                    Paper37.BoundedLoop.Value Paper37.UniformBatchMachine.batchEncoding
                    Paper37.BoundedLoopEncoding.valueEncoding
                    (Paper37.UniformBatchMachine.batchRun Paper37.IntegerPredictorProgram.conditionalProgram) M)).K),
            Finite.{1}
              ((@Turing.TM2ComputableAux.tm
                    (@Computability.Encoding.Γ.{0, 0} Paper37.UniformBatchMachine.BatchQuery
                      (@Computability.FinEncoding.toEncoding.{0} Paper37.UniformBatchMachine.BatchQuery
                        Paper37.UniformBatchMachine.batchEncoding))
                    (@Computability.Encoding.Γ.{0, 0} Paper37.BoundedLoop.Value
                      (@Computability.FinEncoding.toEncoding.{0} Paper37.BoundedLoop.Value
                        Paper37.BoundedLoopEncoding.valueEncoding))
                    (@Turing.TM2ComputableInPolyTime.toTM2ComputableAux Paper37.UniformBatchMachine.BatchQuery
                      Paper37.BoundedLoop.Value Paper37.UniformBatchMachine.batchEncoding
                      Paper37.BoundedLoopEncoding.valueEncoding
                      (Paper37.UniformBatchMachine.batchRun Paper37.IntegerPredictorProgram.conditionalProgram) M)).Γ
                k))
          (∀ (q : Paper37.UniformBatchMachine.BatchQuery),
            @Eq.{1} Paper37.BoundedLoop.Value
              (Paper37.UniformBatchMachine.batchRun Paper37.IntegerPredictorProgram.conditionalProgram q)
              (Paper37.BoundedLoop.Value.array
                (@List.map.{0, 0} (List.{0} Bool) Paper37.BoundedLoop.Value
                  (fun y => Paper37.WordProgram.pairValue (Paper37.IntegerPredictor.conditionalPair q.horizon y))
                  q.queries))) := @Paper37.UniformBatchMachine.actualSpecifiedBatch_polytime

theorem contract_0079 :
    Paper37.BoundedLoopMachine.BoundedLoopSimulationPrinciple →
      @Exists.{2}
        (@Turing.TM2ComputableInPolyTime Paper37.UniformBatchMachine.BatchQuery Paper37.BoundedLoop.Value
          Paper37.UniformBatchMachine.batchEncoding Paper37.BoundedLoopEncoding.valueEncoding
          (Paper37.UniformBatchMachine.batchRun Paper37.AdaptiveQueryProgram.conditionalProgram))
        fun M =>
        And
          (∀
            (k :
              (@Turing.TM2ComputableAux.tm
                  (@Computability.Encoding.Γ.{0, 0} Paper37.UniformBatchMachine.BatchQuery
                    (@Computability.FinEncoding.toEncoding.{0} Paper37.UniformBatchMachine.BatchQuery
                      Paper37.UniformBatchMachine.batchEncoding))
                  (@Computability.Encoding.Γ.{0, 0} Paper37.BoundedLoop.Value
                    (@Computability.FinEncoding.toEncoding.{0} Paper37.BoundedLoop.Value
                      Paper37.BoundedLoopEncoding.valueEncoding))
                  (@Turing.TM2ComputableInPolyTime.toTM2ComputableAux Paper37.UniformBatchMachine.BatchQuery
                    Paper37.BoundedLoop.Value Paper37.UniformBatchMachine.batchEncoding
                    Paper37.BoundedLoopEncoding.valueEncoding
                    (Paper37.UniformBatchMachine.batchRun Paper37.AdaptiveQueryProgram.conditionalProgram) M)).K),
            Finite.{1}
              ((@Turing.TM2ComputableAux.tm
                    (@Computability.Encoding.Γ.{0, 0} Paper37.UniformBatchMachine.BatchQuery
                      (@Computability.FinEncoding.toEncoding.{0} Paper37.UniformBatchMachine.BatchQuery
                        Paper37.UniformBatchMachine.batchEncoding))
                    (@Computability.Encoding.Γ.{0, 0} Paper37.BoundedLoop.Value
                      (@Computability.FinEncoding.toEncoding.{0} Paper37.BoundedLoop.Value
                        Paper37.BoundedLoopEncoding.valueEncoding))
                    (@Turing.TM2ComputableInPolyTime.toTM2ComputableAux Paper37.UniformBatchMachine.BatchQuery
                      Paper37.BoundedLoop.Value Paper37.UniformBatchMachine.batchEncoding
                      Paper37.BoundedLoopEncoding.valueEncoding
                      (Paper37.UniformBatchMachine.batchRun Paper37.AdaptiveQueryProgram.conditionalProgram) M)).Γ
                k))
          (∀ (q : Paper37.UniformBatchMachine.BatchQuery),
            @Eq.{1} Paper37.BoundedLoop.Value
              (Paper37.UniformBatchMachine.batchRun Paper37.AdaptiveQueryProgram.conditionalProgram q)
              (Paper37.BoundedLoop.Value.array
                (@List.map.{0, 0} (List.{0} Bool) Paper37.BoundedLoop.Value
                  (fun y => Paper37.WordProgram.pairValue (Paper37.AdaptiveIntegerOutput.conditionalPair q.horizon y))
                  q.queries))) := @Paper37.UniformBatchMachine.actualAdaptiveSpecifiedBatch_polytime

theorem contract_0080 :
    ∀ (q : Paper37.UniformBatchMachine.BatchQuery) (i : Nat)
      (hi : @LT.lt.{0} Nat instLTNat i (@List.length.{0} (List.{0} Bool) q.queries)),
      And
        (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
          (Paper37.UniformBatchMachine.denominatorValue
            (Paper37.UniformBatchMachine.itemAt
              (Paper37.UniformBatchMachine.batchRun Paper37.IntegerPredictorProgram.conditionalProgram q) i)))
        (@Eq.{1} Rat
          (Paper37.UniformBatchMachine.rationalValue
            (Paper37.UniformBatchMachine.itemAt
              (Paper37.UniformBatchMachine.batchRun Paper37.IntegerPredictorProgram.conditionalProgram q) i))
          (Paper37.Prediction.blockConditional q.horizon
            (@GetElem.getElem.{0, 0, 0} (List.{0} (List.{0} Bool)) Nat (List.{0} Bool)
              (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} (List.{0} Bool) as))
              (@List.instGetElemNatLtLength.{0} (List.{0} Bool)) q.queries i hi))) := @Paper37.UniformBatchMachine.standard_item_correct

theorem contract_0081 :
    ∀ (q : Paper37.UniformBatchMachine.BatchQuery) (i : Nat)
      (hi : @LT.lt.{0} Nat instLTNat i (@List.length.{0} (List.{0} Bool) q.queries)),
      And
        (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
          (Paper37.UniformBatchMachine.denominatorValue
            (Paper37.UniformBatchMachine.itemAt
              (Paper37.UniformBatchMachine.batchRun Paper37.AdaptiveQueryProgram.conditionalProgram q) i)))
        (@Eq.{1} Rat
          (Paper37.UniformBatchMachine.rationalValue
            (Paper37.UniformBatchMachine.itemAt
              (Paper37.UniformBatchMachine.batchRun Paper37.AdaptiveQueryProgram.conditionalProgram q) i))
          (Paper37.Adaptive.adaptiveConditional q.horizon
            (@GetElem.getElem.{0, 0, 0} (List.{0} (List.{0} Bool)) Nat (List.{0} Bool)
              (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} (List.{0} Bool) as))
              (@List.instGetElemNatLtLength.{0} (List.{0} Bool)) q.queries i hi))) := @Paper37.UniformBatchMachine.adaptive_item_correct

theorem contract_0082 :
    Paper37.BoundedLoopMachine.BoundedLoopSimulationPrinciple →
      @Exists.{2}
        (@Turing.TM2ComputableInPolyTime (List.{0} Bool) Paper37.BoundedLoop.Value
          Paper37.UniformPredictionMachine.sourceEncoding Paper37.BoundedLoopEncoding.valueEncoding
          Paper37.AnytimeMachine.sourceRun)
        fun M =>
        And
          (∀
            (k :
              (@Turing.TM2ComputableAux.tm
                  (@Computability.Encoding.Γ.{0, 0} (List.{0} Bool)
                    (@Computability.FinEncoding.toEncoding.{0} (List.{0} Bool)
                      Paper37.UniformPredictionMachine.sourceEncoding))
                  (@Computability.Encoding.Γ.{0, 0} Paper37.BoundedLoop.Value
                    (@Computability.FinEncoding.toEncoding.{0} Paper37.BoundedLoop.Value
                      Paper37.BoundedLoopEncoding.valueEncoding))
                  (@Turing.TM2ComputableInPolyTime.toTM2ComputableAux (List.{0} Bool) Paper37.BoundedLoop.Value
                    Paper37.UniformPredictionMachine.sourceEncoding Paper37.BoundedLoopEncoding.valueEncoding
                    Paper37.AnytimeMachine.sourceRun M)).K),
            Finite.{1}
              ((@Turing.TM2ComputableAux.tm
                    (@Computability.Encoding.Γ.{0, 0} (List.{0} Bool)
                      (@Computability.FinEncoding.toEncoding.{0} (List.{0} Bool)
                        Paper37.UniformPredictionMachine.sourceEncoding))
                    (@Computability.Encoding.Γ.{0, 0} Paper37.BoundedLoop.Value
                      (@Computability.FinEncoding.toEncoding.{0} Paper37.BoundedLoop.Value
                        Paper37.BoundedLoopEncoding.valueEncoding))
                    (@Turing.TM2ComputableInPolyTime.toTM2ComputableAux (List.{0} Bool) Paper37.BoundedLoop.Value
                      Paper37.UniformPredictionMachine.sourceEncoding Paper37.BoundedLoopEncoding.valueEncoding
                      Paper37.AnytimeMachine.sourceRun M)).Γ
                k))
          (And
            (∀ (x : List.{0} Bool),
              @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                (@Option.getD.{0} Paper37.BoundedLoop.Value
                    (@GetElem?.getElem?.{0, 0, 0} (List.{0} Paper37.BoundedLoop.Value) Nat Paper37.BoundedLoop.Value
                      (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Paper37.BoundedLoop.Value as))
                      (@List.instGetElem?NatLtLength.{0} Paper37.BoundedLoop.Value)
                      (Paper37.AnytimeMachine.sourceRun x).arrayVal
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                    (Paper37.BoundedLoop.Value.nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))).natVal)
            (∀ (x : List.{0} Bool),
              @Eq.{1} Real
                (@HDiv.hDiv.{0, 0, 0} Real Real Real
                  (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                  (@Nat.cast.{0} Real Real.instNatCast
                    (@Option.getD.{0} Paper37.BoundedLoop.Value
                        (@GetElem?.getElem?.{0, 0, 0} (List.{0} Paper37.BoundedLoop.Value) Nat Paper37.BoundedLoop.Value
                          (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Paper37.BoundedLoop.Value as))
                          (@List.instGetElem?NatLtLength.{0} Paper37.BoundedLoop.Value)
                          (Paper37.AnytimeMachine.sourceRun x).arrayVal
                          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                        (Paper37.BoundedLoop.Value.nat
                          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))).natVal)
                  (@Nat.cast.{0} Real Real.instNatCast
                    (@Option.getD.{0} Paper37.BoundedLoop.Value
                        (@GetElem?.getElem?.{0, 0, 0} (List.{0} Paper37.BoundedLoop.Value) Nat Paper37.BoundedLoop.Value
                          (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Paper37.BoundedLoop.Value as))
                          (@List.instGetElem?NatLtLength.{0} Paper37.BoundedLoop.Value)
                          (Paper37.AnytimeMachine.sourceRun x).arrayVal
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                        (Paper37.BoundedLoop.Value.nat
                          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))).natVal))
                (@Paper37.Compression.Distribution.mass.{0} Bool Bool.fintype (Paper37.AnytimePrediction.onlineKernel x)
                  Bool.true))) := @Paper37.AnytimeMachine.sourceTM_exists

theorem contract_0083 :
    ∀ (x : List.{0} Bool) (N : Nat),
      @LE.le.{0} Nat instLENat
        (@Finset.sum.{0, 0} Nat Nat Nat.instAddCommMonoid (Finset.range N) fun t =>
          Paper37.BoundedLoop.Expr.work
            (Paper37.BoundedLoopEncoding.inputEnv (Paper37.UniformPredictionMachine.sourceInputs (@List.take.{0} Bool t x)))
            Paper37.AnytimeProgram.program)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 3000) (instOfNatNat (nat_lit 3000)))
          (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@Monoid.toNatPow.{0} Nat Nat.instMonoid))
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) N
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))) := @Paper37.AnytimeMachine.cumulative_arithmetic

theorem contract_0084 :
    Paper37.EquilibriumCycle.EquilibriumCyclePrinciple →
      Paper37.BoundedLoopMachine.BoundedLoopSimulationPrinciple →
        @Exists.{2}
          (@Turing.TM2ComputableInPolyTime (List.{0} Bool) Paper37.BoundedLoop.Value
            Paper37.UniformPredictionMachine.sourceEncoding Paper37.BoundedLoopEncoding.valueEncoding
            Paper37.UniformPredictionMachine.sourceRun)
          fun M =>
          And
            (∀
              (k :
                (@Turing.TM2ComputableAux.tm
                    (@Computability.Encoding.Γ.{0, 0} (List.{0} Bool)
                      (@Computability.FinEncoding.toEncoding.{0} (List.{0} Bool)
                        Paper37.UniformPredictionMachine.sourceEncoding))
                    (@Computability.Encoding.Γ.{0, 0} Paper37.BoundedLoop.Value
                      (@Computability.FinEncoding.toEncoding.{0} Paper37.BoundedLoop.Value
                        Paper37.BoundedLoopEncoding.valueEncoding))
                    (@Turing.TM2ComputableInPolyTime.toTM2ComputableAux (List.{0} Bool) Paper37.BoundedLoop.Value
                      Paper37.UniformPredictionMachine.sourceEncoding Paper37.BoundedLoopEncoding.valueEncoding
                      Paper37.UniformPredictionMachine.sourceRun M)).K),
              Finite.{1}
                ((@Turing.TM2ComputableAux.tm
                      (@Computability.Encoding.Γ.{0, 0} (List.{0} Bool)
                        (@Computability.FinEncoding.toEncoding.{0} (List.{0} Bool)
                          Paper37.UniformPredictionMachine.sourceEncoding))
                      (@Computability.Encoding.Γ.{0, 0} Paper37.BoundedLoop.Value
                        (@Computability.FinEncoding.toEncoding.{0} Paper37.BoundedLoop.Value
                          Paper37.BoundedLoopEncoding.valueEncoding))
                      (@Turing.TM2ComputableInPolyTime.toTM2ComputableAux (List.{0} Bool) Paper37.BoundedLoop.Value
                        Paper37.UniformPredictionMachine.sourceEncoding Paper37.BoundedLoopEncoding.valueEncoding
                        Paper37.UniformPredictionMachine.sourceRun M)).Γ
                  k))
            (And
              (∀ (x : List.{0} Bool),
                @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                    (@List.length.{0} Bool x) →
                  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                    (@Option.getD.{0} Paper37.BoundedLoop.Value
                        (@GetElem?.getElem?.{0, 0, 0} (List.{0} Paper37.BoundedLoop.Value) Nat Paper37.BoundedLoop.Value
                          (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Paper37.BoundedLoop.Value as))
                          (@List.instGetElem?NatLtLength.{0} Paper37.BoundedLoop.Value)
                          (Paper37.UniformPredictionMachine.sourceRun x).arrayVal
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                        (Paper37.BoundedLoop.Value.nat
                          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))).natVal)
              (And
                (∀ (x : List.{0} Bool),
                  @Eq.{1} Rat
                    (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
                      (@Nat.cast.{0} Rat Rat.instNatCast
                        (@Option.getD.{0} Paper37.BoundedLoop.Value
                            (@GetElem?.getElem?.{0, 0, 0} (List.{0} Paper37.BoundedLoop.Value) Nat Paper37.BoundedLoop.Value
                              (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Paper37.BoundedLoop.Value as))
                              (@List.instGetElem?NatLtLength.{0} Paper37.BoundedLoop.Value)
                              (Paper37.UniformPredictionMachine.sourceRun x).arrayVal
                              (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                            (Paper37.BoundedLoop.Value.nat
                              (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))).natVal)
                      (@Nat.cast.{0} Rat Rat.instNatCast
                        (@Option.getD.{0} Paper37.BoundedLoop.Value
                            (@GetElem?.getElem?.{0, 0, 0} (List.{0} Paper37.BoundedLoop.Value) Nat Paper37.BoundedLoop.Value
                              (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Paper37.BoundedLoop.Value as))
                              (@List.instGetElem?NatLtLength.{0} Paper37.BoundedLoop.Value)
                              (Paper37.UniformPredictionMachine.sourceRun x).arrayVal
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                            (Paper37.BoundedLoop.Value.nat
                              (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))).natVal))
                    (Paper37.Prediction.predict (@List.length.{0} Bool x) x))
                (∀ (n : Nat)
                  (hn : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 600) (instOfNatNat (nat_lit 600))) n),
                  And
                    (@LE.le.{0} ENNReal
                      (@Preorder.toLE.{0} ENNReal (@PartialOrder.toPreorder.{0} ENNReal ENNReal.instPartialOrder))
                      (ENNReal.ofReal
                        (@HDiv.hDiv.{0, 0, 0} Real Real Real
                          (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                            (@OfNat.ofNat.{0} Real (nat_lit 11)
                              (@instOfNatAtLeastTwo.{0} Real (nat_lit 11) Real.instNatCast
                                (@Nat.instAtLeastTwoHAddOfNat
                                  (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10)))
                                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9)))))))
                            (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                              (Real.log
                                (@OfNat.ofNat.{0} Real (nat_lit 2)
                                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                                    (@Nat.instAtLeastTwoHAddOfNat
                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                      (@Nat.instNeZeroSucc
                                        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
                              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                                (@OfNat.ofNat.{0} Real (nat_lit 2)
                                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                                    (@Nat.instAtLeastTwoHAddOfNat
                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                      (@Nat.instNeZeroSucc
                                        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))))
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                            (@OfNat.ofNat.{0} Real (nat_lit 40600)
                              (@instOfNatAtLeastTwo.{0} Real (nat_lit 40600) Real.instNatCast
                                (@Nat.instAtLeastTwoHAddOfNat
                                  (@OfNat.ofNat.{0} Nat (nat_lit 40599) (instOfNatNat (nat_lit 40599)))
                                  (@Nat.instNeZeroSucc
                                    (@OfNat.ofNat.{0} Nat (nat_lit 40598) (instOfNatNat (nat_lit 40598)))))))
                            (@Nat.cast.{0} Real Real.instNatCast n).sqrt)))
                      (Paper37.Prediction.minimaxRisk n))
                    (And
                      (@LE.le.{0} ENNReal
                        (@Preorder.toLE.{0} ENNReal (@PartialOrder.toPreorder.{0} ENNReal ENNReal.instPartialOrder))
                        (Paper37.Prediction.minimaxRisk n)
                        (@iSup.{0, 1} ENNReal Paper37.Renewal.Law
                          (@ConditionallyCompleteLattice.toSupSet.{0} ENNReal
                            (@ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal
                              (@ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal
                                (@CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal
                                  ENNReal.instCompleteLinearOrder))))
                          fun μ =>
                          Paper37.Prediction.risk n
                            (Paper37.CompressionPrediction.sourcePredictor n
                              (@Decidable.byContradiction
                                (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n)
                                (Nat.decLt (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n) fun a =>
                                Paper37.CompleteResults.fixed_time_rate_attainment._proof_1 n hn a))
                            μ))
                      (@LE.le.{0} ENNReal
                        (@Preorder.toLE.{0} ENNReal (@PartialOrder.toPreorder.{0} ENNReal ENNReal.instPartialOrder))
                        (@iSup.{0, 1} ENNReal Paper37.Renewal.Law
                          (@ConditionallyCompleteLattice.toSupSet.{0} ENNReal
                            (@ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal
                              (@ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal
                                (@CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal
                                  ENNReal.instCompleteLinearOrder))))
                          fun μ =>
                          Paper37.Prediction.risk n
                            (Paper37.CompressionPrediction.sourcePredictor n
                              (@Decidable.byContradiction
                                (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n)
                                (Nat.decLt (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n) fun a =>
                                Paper37.CompleteResults.fixed_time_rate_attainment._proof_1 n hn a))
                            μ)
                        (ENNReal.ofReal
                          (@HDiv.hDiv.{0, 0, 0} Real Real Real
                            (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                  (@OfNat.ofNat.{0} Real (nat_lit 2)
                                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                                      (@Nat.instAtLeastTwoHAddOfNat
                                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                        (@Nat.instNeZeroSucc
                                          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                                  Real.pi)
                                (Real.sqrt
                                  (@OfNat.ofNat.{0} Real (nat_lit 3)
                                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
                                      (@Nat.instAtLeastTwoHAddOfNat
                                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                        (@Nat.instNeZeroSucc
                                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))))
                              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                (@OfNat.ofNat.{0} Real (nat_lit 3)
                                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
                                    (@Nat.instAtLeastTwoHAddOfNat
                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
                                (Real.sqrt
                                  (@OfNat.ofNat.{0} Real (nat_lit 2)
                                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                                      (@Nat.instAtLeastTwoHAddOfNat
                                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                        (@Nat.instNeZeroSucc
                                          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))))
                            (@Nat.cast.{0} Real Real.instNatCast n).sqrt))))))) := @Paper37.CompleteResults.fixed_time_rate_attainment

theorem contract_0085 :
    Paper37.BoundedLoopMachine.BoundedLoopSimulationPrinciple →
      @Exists.{2}
        (@Turing.TM2ComputableInPolyTime (List.{0} Bool) Paper37.BoundedLoop.Value
          Paper37.UniformPredictionMachine.sourceEncoding Paper37.BoundedLoopEncoding.valueEncoding
          Paper37.UniformAdaptivePredictionMachine.sourceRun)
        fun M =>
        And
          (∀
            (k :
              (@Turing.TM2ComputableAux.tm
                  (@Computability.Encoding.Γ.{0, 0} (List.{0} Bool)
                    (@Computability.FinEncoding.toEncoding.{0} (List.{0} Bool)
                      Paper37.UniformPredictionMachine.sourceEncoding))
                  (@Computability.Encoding.Γ.{0, 0} Paper37.BoundedLoop.Value
                    (@Computability.FinEncoding.toEncoding.{0} Paper37.BoundedLoop.Value
                      Paper37.BoundedLoopEncoding.valueEncoding))
                  (@Turing.TM2ComputableInPolyTime.toTM2ComputableAux (List.{0} Bool) Paper37.BoundedLoop.Value
                    Paper37.UniformPredictionMachine.sourceEncoding Paper37.BoundedLoopEncoding.valueEncoding
                    Paper37.UniformAdaptivePredictionMachine.sourceRun M)).K),
            Finite.{1}
              ((@Turing.TM2ComputableAux.tm
                    (@Computability.Encoding.Γ.{0, 0} (List.{0} Bool)
                      (@Computability.FinEncoding.toEncoding.{0} (List.{0} Bool)
                        Paper37.UniformPredictionMachine.sourceEncoding))
                    (@Computability.Encoding.Γ.{0, 0} Paper37.BoundedLoop.Value
                      (@Computability.FinEncoding.toEncoding.{0} Paper37.BoundedLoop.Value
                        Paper37.BoundedLoopEncoding.valueEncoding))
                    (@Turing.TM2ComputableInPolyTime.toTM2ComputableAux (List.{0} Bool) Paper37.BoundedLoop.Value
                      Paper37.UniformPredictionMachine.sourceEncoding Paper37.BoundedLoopEncoding.valueEncoding
                      Paper37.UniformAdaptivePredictionMachine.sourceRun M)).Γ
                k))
          (And
            (∀ (x : List.{0} Bool),
              @Eq.{1} Rat
                (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
                  (@Nat.cast.{0} Rat Rat.instNatCast
                    (@Option.getD.{0} Paper37.BoundedLoop.Value
                        (@GetElem?.getElem?.{0, 0, 0} (List.{0} Paper37.BoundedLoop.Value) Nat Paper37.BoundedLoop.Value
                          (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Paper37.BoundedLoop.Value as))
                          (@List.instGetElem?NatLtLength.{0} Paper37.BoundedLoop.Value)
                          (Paper37.UniformAdaptivePredictionMachine.sourceRun x).arrayVal
                          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                        (Paper37.BoundedLoop.Value.nat
                          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))).natVal)
                  (@Nat.cast.{0} Rat Rat.instNatCast
                    (@Option.getD.{0} Paper37.BoundedLoop.Value
                        (@GetElem?.getElem?.{0, 0, 0} (List.{0} Paper37.BoundedLoop.Value) Nat Paper37.BoundedLoop.Value
                          (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Paper37.BoundedLoop.Value as))
                          (@List.instGetElem?NatLtLength.{0} Paper37.BoundedLoop.Value)
                          (Paper37.UniformAdaptivePredictionMachine.sourceRun x).arrayVal
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                        (Paper37.BoundedLoop.Value.nat
                          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))).natVal))
                (Paper37.Adaptive.adaptivePredict (@List.length.{0} Bool x) x))
            (∀ (μ : Paper37.Renewal.Law) (n : Nat)
              (hn : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n),
              @LE.le.{0} ENNReal
                (@Preorder.toLE.{0} ENNReal (@PartialOrder.toPreorder.{0} ENNReal ENNReal.instPartialOrder))
                (Paper37.Prediction.risk n (Paper37.AdaptivePrediction.sourcePredictor n hn) μ)
                (ENNReal.ofReal
                  (@HDiv.hDiv.{0, 0, 0} Real Real Real
                    (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                        (Real.log
                          (@OfNat.ofNat.{0} Real (nat_lit 2)
                            (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
                        (@Min.min.{0} Real Real.instMin
                          (Paper37.AnalyticBounds.redundancyBound
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                (@OfNat.ofNat.{0} Real (nat_lit 2)
                                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                                    (@Nat.instAtLeastTwoHAddOfNat
                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                                (Paper37.AnalyticBounds.occupiedComplexity
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                  (fun d =>
                                    μ.mass
                                      (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) d
                                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                  (Paper37.Renewal.mean μ)))
                              (@OfNat.ofNat.{0} Real (nat_lit 6)
                                (@instOfNatAtLeastTwo.{0} Real (nat_lit 6) Real.instNatCast
                                  (@Nat.instAtLeastTwoHAddOfNat
                                    (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
                                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))))
                            (Real.log
                              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                (@Nat.cast.{0} Real Real.instNatCast n)
                                (@OfNat.ofNat.{0} Real (nat_lit 2)
                                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                                    (@Nat.instAtLeastTwoHAddOfNat
                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                      (@Nat.instNeZeroSucc
                                        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))))))
                      (Real.log
                        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                          (@Nat.cast.{0} Real Real.instNatCast n)
                          (@OfNat.ofNat.{0} Real (nat_lit 2)
                            (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))))
                    (@Nat.cast.{0} Real Real.instNatCast n))))) := @Paper37.CompleteResults.adaptive_rate_attainment

theorem contract_0086 :
    Paper37.EquilibriumCycle.EquilibriumCyclePrinciple →
      Paper37.BoundedLoopMachine.BoundedLoopSimulationPrinciple →
        @Exists.{2}
          (@Turing.TM2ComputableInPolyTime (List.{0} Bool) Paper37.BoundedLoop.Value
            Paper37.UniformPredictionMachine.sourceEncoding Paper37.BoundedLoopEncoding.valueEncoding
            Paper37.AnytimeMachine.sourceRun)
          fun M =>
          And
            (∀
              (k :
                (@Turing.TM2ComputableAux.tm
                    (@Computability.Encoding.Γ.{0, 0} (List.{0} Bool)
                      (@Computability.FinEncoding.toEncoding.{0} (List.{0} Bool)
                        Paper37.UniformPredictionMachine.sourceEncoding))
                    (@Computability.Encoding.Γ.{0, 0} Paper37.BoundedLoop.Value
                      (@Computability.FinEncoding.toEncoding.{0} Paper37.BoundedLoop.Value
                        Paper37.BoundedLoopEncoding.valueEncoding))
                    (@Turing.TM2ComputableInPolyTime.toTM2ComputableAux (List.{0} Bool) Paper37.BoundedLoop.Value
                      Paper37.UniformPredictionMachine.sourceEncoding Paper37.BoundedLoopEncoding.valueEncoding
                      Paper37.AnytimeMachine.sourceRun M)).K),
              Finite.{1}
                ((@Turing.TM2ComputableAux.tm
                      (@Computability.Encoding.Γ.{0, 0} (List.{0} Bool)
                        (@Computability.FinEncoding.toEncoding.{0} (List.{0} Bool)
                          Paper37.UniformPredictionMachine.sourceEncoding))
                      (@Computability.Encoding.Γ.{0, 0} Paper37.BoundedLoop.Value
                        (@Computability.FinEncoding.toEncoding.{0} Paper37.BoundedLoop.Value
                          Paper37.BoundedLoopEncoding.valueEncoding))
                      (@Turing.TM2ComputableInPolyTime.toTM2ComputableAux (List.{0} Bool) Paper37.BoundedLoop.Value
                        Paper37.UniformPredictionMachine.sourceEncoding Paper37.BoundedLoopEncoding.valueEncoding
                        Paper37.AnytimeMachine.sourceRun M)).Γ
                  k))
            (And
              (∀ (x : List.{0} Bool),
                @Eq.{1} Real
                  (@HDiv.hDiv.{0, 0, 0} Real Real Real
                    (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                    (@Nat.cast.{0} Real Real.instNatCast
                      (@Option.getD.{0} Paper37.BoundedLoop.Value
                          (@GetElem?.getElem?.{0, 0, 0} (List.{0} Paper37.BoundedLoop.Value) Nat Paper37.BoundedLoop.Value
                            (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Paper37.BoundedLoop.Value as))
                            (@List.instGetElem?NatLtLength.{0} Paper37.BoundedLoop.Value)
                            (Paper37.AnytimeMachine.sourceRun x).arrayVal
                            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                          (Paper37.BoundedLoop.Value.nat
                            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))).natVal)
                    (@Nat.cast.{0} Real Real.instNatCast
                      (@Option.getD.{0} Paper37.BoundedLoop.Value
                          (@GetElem?.getElem?.{0, 0, 0} (List.{0} Paper37.BoundedLoop.Value) Nat Paper37.BoundedLoop.Value
                            (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Paper37.BoundedLoop.Value as))
                            (@List.instGetElem?NatLtLength.{0} Paper37.BoundedLoop.Value)
                            (Paper37.AnytimeMachine.sourceRun x).arrayVal
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                          (Paper37.BoundedLoop.Value.nat
                            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))).natVal))
                  (@Paper37.Compression.Distribution.mass.{0} Bool Bool.fintype (Paper37.AnytimePrediction.onlineKernel x)
                    Bool.true))
              (∀ (N : Nat),
                @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2500) (instOfNatNat (nat_lit 2500))) N →
                  And
                    (@LE.le.{0} ENNReal
                      (@Preorder.toLE.{0} ENNReal (@PartialOrder.toPreorder.{0} ENNReal ENNReal.instPartialOrder))
                      (ENNReal.ofReal
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                          Paper37.CumulativeLower.cumulativeConstant (@Nat.cast.{0} Real Real.instNatCast N).sqrt))
                      (Paper37.CumulativeLower.minimaxCumulativeRisk N))
                    (And
                      (@LE.le.{0} ENNReal
                        (@Preorder.toLE.{0} ENNReal (@PartialOrder.toPreorder.{0} ENNReal ENNReal.instPartialOrder))
                        (Paper37.CumulativeLower.minimaxCumulativeRisk N)
                        (@iSup.{0, 1} ENNReal Paper37.Renewal.Law
                          (@ConditionallyCompleteLattice.toSupSet.{0} ENNReal
                            (@ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal
                              (@ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal
                                (@CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal
                                  ENNReal.instCompleteLinearOrder))))
                          fun μ => Paper37.AnytimePrediction.cumulativeRisk μ N))
                      (@LE.le.{0} ENNReal
                        (@Preorder.toLE.{0} ENNReal (@PartialOrder.toPreorder.{0} ENNReal ENNReal.instPartialOrder))
                        (@iSup.{0, 1} ENNReal Paper37.Renewal.Law
                          (@ConditionallyCompleteLattice.toSupSet.{0} ENNReal
                            (@ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal
                              (@ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal
                                (@CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal
                                  ENNReal.instCompleteLinearOrder))))
                          fun μ => Paper37.AnytimePrediction.cumulativeRisk μ N)
                        (ENNReal.ofReal
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                            Paper37.CumulativeLower.cumulativeUpperConstant
                            (@Nat.cast.{0} Real Real.instNatCast N).sqrt)))))) := @Paper37.CompleteResults.anytime_rate_attainment

theorem contract_0087 :
    Paper37.BoundedLoopMachine.BoundedLoopSimulationPrinciple →
      @Exists.{2}
        (@Turing.TM2ComputableInPolyTime (List.{0} Bool) Paper37.BoundedLoop.Value
          Paper37.UniformPredictionMachine.sourceEncoding Paper37.BoundedLoopEncoding.valueEncoding
          Paper37.FullBlockProgram.sourceRun)
        fun M =>
        And
          (∀
            (k :
              (@Turing.TM2ComputableAux.tm
                  (@Computability.Encoding.Γ.{0, 0} (List.{0} Bool)
                    (@Computability.FinEncoding.toEncoding.{0} (List.{0} Bool)
                      Paper37.UniformPredictionMachine.sourceEncoding))
                  (@Computability.Encoding.Γ.{0, 0} Paper37.BoundedLoop.Value
                    (@Computability.FinEncoding.toEncoding.{0} Paper37.BoundedLoop.Value
                      Paper37.BoundedLoopEncoding.valueEncoding))
                  (@Turing.TM2ComputableInPolyTime.toTM2ComputableAux (List.{0} Bool) Paper37.BoundedLoop.Value
                    Paper37.UniformPredictionMachine.sourceEncoding Paper37.BoundedLoopEncoding.valueEncoding
                    Paper37.FullBlockProgram.sourceRun M)).K),
            Finite.{1}
              ((@Turing.TM2ComputableAux.tm
                    (@Computability.Encoding.Γ.{0, 0} (List.{0} Bool)
                      (@Computability.FinEncoding.toEncoding.{0} (List.{0} Bool)
                        Paper37.UniformPredictionMachine.sourceEncoding))
                    (@Computability.Encoding.Γ.{0, 0} Paper37.BoundedLoop.Value
                      (@Computability.FinEncoding.toEncoding.{0} Paper37.BoundedLoop.Value
                        Paper37.BoundedLoopEncoding.valueEncoding))
                    (@Turing.TM2ComputableInPolyTime.toTM2ComputableAux (List.{0} Bool) Paper37.BoundedLoop.Value
                      Paper37.UniformPredictionMachine.sourceEncoding Paper37.BoundedLoopEncoding.valueEncoding
                      Paper37.FullBlockProgram.sourceRun M)).Γ
                k))
          (And
            (∀ (x : List.{0} Bool),
              @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                (@Option.getD.{0} Paper37.BoundedLoop.Value
                    (@GetElem?.getElem?.{0, 0, 0} (List.{0} Paper37.BoundedLoop.Value) Nat Paper37.BoundedLoop.Value
                      (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Paper37.BoundedLoop.Value as))
                      (@List.instGetElem?NatLtLength.{0} Paper37.BoundedLoop.Value)
                      (Paper37.FullBlockProgram.sourceRun x).arrayVal
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                    (Paper37.BoundedLoop.Value.nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))).natVal)
            (∀ (x : List.{0} Bool),
              @Eq.{1} Rat
                (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
                  (@Nat.cast.{0} Rat Rat.instNatCast
                    (@Option.getD.{0} Paper37.BoundedLoop.Value
                        (@GetElem?.getElem?.{0, 0, 0} (List.{0} Paper37.BoundedLoop.Value) Nat Paper37.BoundedLoop.Value
                          (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Paper37.BoundedLoop.Value as))
                          (@List.instGetElem?NatLtLength.{0} Paper37.BoundedLoop.Value)
                          (Paper37.FullBlockProgram.sourceRun x).arrayVal
                          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                        (Paper37.BoundedLoop.Value.nat
                          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))).natVal)
                  (@Nat.cast.{0} Rat Rat.instNatCast
                    (@Option.getD.{0} Paper37.BoundedLoop.Value
                        (@GetElem?.getElem?.{0, 0, 0} (List.{0} Paper37.BoundedLoop.Value) Nat Paper37.BoundedLoop.Value
                          (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Paper37.BoundedLoop.Value as))
                          (@List.instGetElem?NatLtLength.{0} Paper37.BoundedLoop.Value)
                          (Paper37.FullBlockProgram.sourceRun x).arrayVal
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                        (Paper37.BoundedLoop.Value.nat
                          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))).natVal))
                (Paper37.Prediction.blockAssignment x))) := @Paper37.FullBlockProgram.actualBlockAssignment_polytime

theorem contract_0088 :
    ∀ (x : List.{0} Bool),
      And
        (@Eq.{1} Paper37.BoundedLoop.Value (Paper37.FullBlockProgram.sourceRun x)
          (Paper37.WordProgram.pairValue (Paper37.FullBlockProgram.blockPair x)))
        (And
          (@LE.le.{0} Nat instLENat
            (Paper37.BoundedLoop.Expr.work
              (Paper37.BoundedLoopEncoding.inputEnv (Paper37.UniformPredictionMachine.sourceInputs x))
              Paper37.FullBlockProgram.program)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 3000) (instOfNatNat (nat_lit 3000)))
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@Monoid.toNatPow.{0} Nat Nat.instMonoid))
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@List.length.{0} Bool x)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))
          (@LE.le.{0} Nat instLENat
            (Paper37.BoundedLoop.Expr.peak
              (Paper37.BoundedLoopEncoding.inputEnv (Paper37.UniformPredictionMachine.sourceInputs x))
              Paper37.FullBlockProgram.program)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 1000000000000000) (instOfNatNat (nat_lit 1000000000000000)))
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@Monoid.toNatPow.{0} Nat Nat.instMonoid))
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@List.length.{0} Bool x)
                  (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))))))) := @Paper37.FullBlockProgram.source_algorithm_certificate

theorem contract_0089 :
    ∀ (μ : Paper37.Renewal.Law) (x : List.{0} Bool),
      @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
          (Paper37.Renewal.blockMass μ x) →
        have q :=
          @HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
            (@Nat.cast.{0} Rat Rat.instNatCast
              (@Option.getD.{0} Paper37.BoundedLoop.Value
                  (@GetElem?.getElem?.{0, 0, 0} (List.{0} Paper37.BoundedLoop.Value) Nat Paper37.BoundedLoop.Value
                    (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Paper37.BoundedLoop.Value as))
                    (@List.instGetElem?NatLtLength.{0} Paper37.BoundedLoop.Value)
                    (Paper37.FullBlockProgram.sourceRun x).arrayVal
                    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                  (Paper37.BoundedLoop.Value.nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))).natVal)
            (@Nat.cast.{0} Rat Rat.instNatCast
              (@Option.getD.{0} Paper37.BoundedLoop.Value
                  (@GetElem?.getElem?.{0, 0, 0} (List.{0} Paper37.BoundedLoop.Value) Nat Paper37.BoundedLoop.Value
                    (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Paper37.BoundedLoop.Value as))
                    (@List.instGetElem?NatLtLength.{0} Paper37.BoundedLoop.Value)
                    (Paper37.FullBlockProgram.sourceRun x).arrayVal
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  (Paper37.BoundedLoop.Value.nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))).natVal);
        @LE.le.{0} Real Real.instLE
          (Real.log
            (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (Paper37.Renewal.blockMass μ x) (@Rat.cast.{0} Real Real.instRatCast q)))
          (Paper37.AnalyticBounds.redundancyBound (@List.length.{0} Bool x)) := @Paper37.FullBlockProgram.source_log_regret

end Verification
