import Paper29.PosteriorChannel
import Paper29.FiniteQueryLower
import Paper29.HardDistribution

noncomputable section
open scoped BigOperators Classical
namespace Paper29.HardDistribution
open Transcript

/-- Actual finite hard law with an arbitrary independent finite private seed. -/
def hardSeedLaw {E : Type} [Fintype E] {r N : ℕ} (q : E → ℝ)
    (hq : ∀ e,0 ≤ q e) (hsq : ∑ e,q e=1) (β : ℝ) (hβ : 0 ≤ β) (hβhi : β ≤ 1/2) :
    Law (Signs r × (Bits r N × E)) :=
  productObservationLaw (signMass r) (by intro s; unfold signMass; positivity) (signMass_total r)
    q hq hsq (fun s a b => bitMass (1/2+β*sign (s a.1)) b)
    (by intro s a b; apply bitMass_nonneg <;> cases hs : s a.1 <;> simp [sign,hs] <;> linarith)
    (by intro s a; exact bitMass_total _)

/-- The actual adaptive transcript information bound for the hard Bernoulli
law. Freshness and product structure derive every local posterior bound. -/
theorem hard_transcript_information_bound {E : Type} [Fintype E] {r N : ℕ}
    (q : E → ℝ) (hq : ∀ e,0 ≤ q e) (hsq : ∑ e,q e=1)
    (β : ℝ) (hβ : 0 ≤ β) (hβhi : β ≤ 1/4)
    (policy : Policy E (Fin r × Fin N) Bool) (n : ℕ) :
    let P := hardSeedLaw (r:=r) (N:=N) q hq hsq β hβ (hβhi.trans (by norm_num))
    P.information Prod.fst (historyRV policy (fun ω => ω.2.2) (fun ω => ω.2.1) n) ≤
      16*β^2*expectedQueries P policy (fun ω => ω.2.2) (fun ω => ω.2.1) n := by
  apply finite_adaptive_transcript_bound
  · exact ProductObservation.independent_seed _ _ _ _ _ _ _ _ _
  · intro t _ h hh j hj
    exact ProductObservation.local_fresh_information_bound _ _ _ _ _ _ _ _ _
      policy t h j hj hh (fun s => s j.1) β hβ hβhi (fun _ _ => rfl)

/-- Finite-seed long-regime lower bound with no assumed channel/information
certificate: only actual expected Hamming error and a causal transcript decoder. -/
theorem hard_finite_query_lower {E : Type} [Fintype E] {r N : ℕ}
    (q : E → ℝ) (hq : ∀ e,0 ≤ q e) (hsq : ∑ e,q e=1)
    (β : ℝ) (hβ : 0 ≤ β) (hβhi : β ≤ 1/4)
    (policy : Policy E (Fin r × Fin N) Bool) (n : ℕ)
    (decoder : History E (Fin r × Fin N) Bool n → Signs r)
    (herror : let P := hardSeedLaw (r:=r) (N:=N) q hq hsq β hβ (hβhi.trans (by norm_num));
      (∑ ω,P.weight ω*RateDistortion.hamming ω.1
        (decoder (historyRV policy (fun ω => ω.2.2) (fun ω => ω.2.1) n ω))) < (1/25:ℝ)*r) :
    let P := hardSeedLaw (r:=r) (N:=N) q hq hsq β hβ (hβhi.trans (by norm_num))
    RateDistortion.cRD*r ≤ 16*β^2*expectedQueries P policy (fun ω => ω.2.2) (fun ω => ω.2.1) n := by
  let P := hardSeedLaw (r:=r) (N:=N) q hq hsq β hβ (hβhi.trans (by norm_num))
  have hu : ∀ s,P.mass Prod.fst s=((2:ℝ)^r)⁻¹ := by
    intro s
    exact ProductObservation.mass_source _ _ _ _ _ _ _ _ _ s
  let estimate : (Signs r × (Bits r N × E)) → Signs r := fun ω => decoder (historyRV policy (fun ω => ω.2.2) (fun ω => ω.2.1) n ω)
  have hrd := RateDistortion.lemma4_2 (cubeJoint P Prod.fst estimate) (by
    intro s; rw [cubeJoint_source]; exact hu s) (by
      rw [expectedHamming_cubeJoint]
      convert herror using 1 <;> norm_num [estimate])
  have hd := P.information_data_processing Prod.fst
    (historyRV policy (fun ω => ω.2.2) (fun ω => ω.2.1) n) decoder
  change P.information Prod.fst estimate ≤ _ at hd
  rw [information_eq_cubeJoint] at hd
  exact hrd.1.trans (hd.trans (hard_transcript_information_bound q hq hsq β hβ hβhi policy n))

end Paper29.HardDistribution
