import Paper29.BernoulliInformation
import Paper29.PoolResponse

noncomputable section
open scoped BigOperators
namespace Paper29.Transcript.Law

/-- A channel factorization of actual joint masses gives the posterior
Bernoulli information bound, without assuming an information certificate. -/
theorem local_biased_bit_information_le {Ω S H : Type} [Fintype Ω] [Fintype S] [Fintype H]
    (P : Law Ω) (source : Ω → S) (response : Ω → Bool) (history : Ω → H)
    (h : H) (hh : 0 < P.mass history h) (σ : S → Bool)
    (β : ℝ) (hβ : 0 ≤ β) (hβhi : β ≤ 1/4)
    (hc : ∀ s b, P.mass (fun ω => ((source ω,response ω),history ω)) ((s,b),h) =
      HardDistribution.bitMass (1/2+β*HardDistribution.sign (σ s)) b *
        P.mass (fun ω => (source ω,history ω)) (s,h)) :
    P.localInformation source response history h ≤ 16*β^2 := by
  rw [P.localInformation_eq_condition_information source response history h hh]
  apply Law.biased_bit_information_le (P.condition history h hh) source response σ β hβ hβhi
  intro s b
  rw [P.mass_condition,P.mass_condition,hc]
  ring

theorem local_information_const {Ω S H R : Type} [Fintype Ω] [Fintype S] [Fintype H] [Fintype R]
    (P : Law Ω) (source : Ω → S) (history : Ω → H) (h : H)
    (hh : 0 < P.mass history h) (b : R) :
    P.localInformation source (fun _ => b) history h = 0 := by
  rw [P.localInformation_eq_condition_information source (fun _ => b) history h hh]
  exact (P.condition history h hh).information_const source b

end Paper29.Transcript.Law
