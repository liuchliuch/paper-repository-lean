import Paper32.Avoidance
import Paper32.BorelSelection
import Paper32.ClarkeBridge
import Paper32.Counterexample
import Paper32.DDJBridge
import Paper32.Dynamics
import Paper32.EmbeddingCalculus
import Paper32.EmbeddingClass
import Paper32.EmbeddingCoordinates
import Paper32.EmbeddingMain
import Paper32.Epigraph
import Paper32.Extensions
import Paper32.FirstStep
import Paper32.FunctionClass
import Paper32.Geometry
import Paper32.IidRecursion
import Paper32.LimitEvents
import Paper32.Main
import Paper32.MarginalCounterexample
import Paper32.MeasureExtensions
import Paper32.NoiseConsequences
import Paper32.OracleConsequences
import Paper32.ParameterizedGradient
import Paper32.RandomInitialization
import Paper32.ScalingCalculus
import Paper32.ScalingClass
import Paper32.ScalingMain
import Paper32.Selection
import Paper32.SelectionAlgebraic
import Paper32.SourceResults
import Paper32.Steps
import Paper32.Strata
import Paper32.Subdifferential
import Paper32.TiltMeasure
import Paper32.Translation
import Paper32.VariationalBridge

/-! Fixed fully explicit literal theorem contracts. No theorem-type aliases or definition holes.
Readable forms and original-source correspondence are recorded separately for semantic review.
Verification is deferred by user. -/

set_option autoImplicit false
set_option linter.unusedVariables false
universe u_1 u_2 u_3

namespace Verification.Contract

theorem c_Paper32_attracting_sign_step :
    False → (
    ∀ {u a δ α e : Real},
      @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) u →
        @LT.lt.{0} Real Real.instLT δ a →
          @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) δ →
            @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) α →
              @LE.le.{0} Real Real.instLE (@abs.{0} Real Real.lattice Real.instAddGroup e) δ →
                @LE.le.{0} Real Real.instLE
                  (@abs.{0} Real Real.lattice Real.instAddGroup
                    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) u
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) α
                        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) a e))))
                  (@Max.max.{0} Real Real.instMax
                    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) u
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) a δ) α))
                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) a δ) α))) :=
  fun _ => @Paper32.attracting_sign_step
end Verification.Contract
