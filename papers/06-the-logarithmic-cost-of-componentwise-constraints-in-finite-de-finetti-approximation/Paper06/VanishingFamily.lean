import Paper06.Results
import Paper06.Asymptotics
import Mathlib.FieldTheory.Finite.Basic

open Real Filter Asymptotics
open scoped Topology

namespace Paper06

instance paperPrime_primeFact (θ : ℝ) (n : ℕ) : Fact (Nat.Prime (paperPrime θ n)) :=
  ⟨polynomialPrime_prime _ _ _⟩

/-- The paper's explicit family: one matching extension over the selected
prime field, chosen before specifying a marginal or mixing measure. -/
noncomputable def paperMatchingAdmissible (θ : ℝ) (n : ℕ) (hEven : Even n) :
    Admissible (ZMod (paperPrime θ n) × ZMod (paperPrime θ n)) n :=
  matchingAdmissible (ZMod (paperPrime θ n)) n hEven

/-- Equation (18) for the actual polynomial-alphabet matching family.
Every sufficiently large even extension has the exact floor sample size,
and its optimum over all Borel feasible mixtures lies in the stated chain. -/
theorem equation18 {θ : ℝ} (hθ : 0 < θ) (hθhalf : θ < 1 / 2) :
    ∀ᶠ n : ℕ in atTop, ∀ hEven : Even n,
      ∃ hk : asymptoticSampleSize n ≤ n,
        (((3 * θ / 32) * asymptoticScale (paperAlphabet θ) n : ℝ) : EReal) ≤
          constrainedError (paperMatchingAdmissible θ n hEven).law
            (paperMatchingAdmissible θ n hEven).slice (asymptoticSampleSize n) hk ∧
        constrainedError (paperMatchingAdmissible θ n hEven).law
            (paperMatchingAdmissible θ n hEven).slice (asymptoticSampleSize n) hk ≤
          worstConstrainedError (paperAlphabet θ n) n (asymptoticSampleSize n) hk ∧
        worstConstrainedError (paperAlphabet θ n) n (asymptoticSampleSize n) hk ≤
          ((asymptoticScale (paperAlphabet θ) n / 2 : ℝ) : EReal) := by
  filter_upwards [eventually_ge_atTop 6,
    asymptoticSampleSize_tendsto.eventually_ge_atTop 2] with n hn hk2
  intro hEven
  have hkk := asymptoticSampleSize_sq_le (n := n) (by omega)
  have hk : asymptoticSampleSize n ≤ n := by nlinarith
  refine ⟨hk, ?_⟩
  have hparam := paperPrime_parameter hθhalf (n := n) (by omega)
  have hs := matching_error_sandwich (F := ZMod (paperPrime θ n))
    n (asymptoticSampleSize n) hEven hn hk2 hkk θ hθ hθhalf
    (by simpa only [ZMod.card] using hparam)
  simp only [paperMatchingAdmissible, matchingAdmissible_slice]
  simpa only [matchingAdmissible,
    ZMod.card, paperAlphabet, polynomialAlphabet, paperPrime,
    Nat.cast_pow, asymptoticScale] using hs

/-- The concrete family highlighted in the abstract and introduction:
`d_n = Θ(n^8)` and the matching scale is `Θ(log n / √n) → 0`.
Its full error chain is `equation18` with `θ = 1/4`, whose lower constant is `3/128`. -/
theorem concrete_eighth_power_family :
    (fun n : ℕ => (paperAlphabet (1 / 4) n : ℝ)) =Θ[atTop]
        (fun n : ℕ => (n : ℝ) ^ (8 : ℝ)) ∧
      asymptoticScale (paperAlphabet (1 / 4)) =Θ[atTop]
        (fun n : ℕ => Real.log n / Real.sqrt n) ∧
      Tendsto (asymptoticScale (paperAlphabet (1 / 4))) atTop (𝓝 0) := by
  refine ⟨?_, equation17 (by norm_num)⟩
  convert (equation16 (θ := (1 / 4 : ℝ)) (by norm_num) (by norm_num)).2 using 1 <;> norm_num

end Paper06
