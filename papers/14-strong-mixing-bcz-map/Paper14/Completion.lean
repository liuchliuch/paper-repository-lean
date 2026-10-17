import Paper14.BCZErgodic
import Paper14.BCZWeakMixingFromErgodic
import Paper14.EigenSectionBound
import Paper14.MixingL2
import Paper14.MixingComplexL2

open MeasureTheory Filter Topology Set
namespace Paper14
noncomputable section

/-- Proposition 3: the actual BCZ map is weakly mixing. -/
theorem Proposition3 : Proposition3Statement := bcz_weak_mixing_of_ergodic ergodic_B

/-- Theorem 1: the actual BCZ map is strongly mixing. -/
theorem Theorem1 : Theorem1Statement := bcz_strong_mixing_of_ergodic ergodic_B

/-- The equivalent original L2 correlation conclusion of Theorem 1. -/
theorem Theorem1L2 : StrongMixingL2 B m := (strongMixing_iff_L2 measurePreserving_B).mp Theorem1

/-- The original correlation conclusion also holds for complex-valued L2 functions. -/
theorem Theorem1ComplexL2 : StrongMixingComplexL2 B m :=
  strongMixing_complexL2 measurePreserving_B Theorem1

/-- The original positive-proportion exactly-one-extra-return assertion (22). -/
theorem exactly_one_extra : ExactlyOneExtraStatement := exactly_one_extra_of_ergodic ergodic_B

/-- The original Appendix A exclusion of every nontrivial L2 eigenvalue. -/
theorem noNontrivialEigen : NoNontrivialEigen := noNontrivialEigen_of_ergodic ergodic_B

/-- Source equation (4) for the actual moving sections. -/
theorem changing_roof_probability_unconditional (r : ℕ → ℝ)
    (hr : ∀ᶠ n : ℕ in atTop,0<r n ∧ r n<1) (hlim : Tendsto r atTop (𝓝 1))
    (ε : ℝ) (hε : 0<ε) :
    Tendsto (fun n : ℕ => mr (r n) {y | ε≤|Hr (r n) n y/n-Real.pi^2/3|}) atTop (𝓝 0) :=
  changing_roof_probability ergodic_B r hr hlim ε hε

end
end Paper14
