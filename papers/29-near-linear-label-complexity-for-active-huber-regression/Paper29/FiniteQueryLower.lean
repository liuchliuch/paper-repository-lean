import Paper29.DataProcessing
import Paper29.RateDistortion

noncomputable section
open scoped BigOperators
namespace Paper29.Transcript

/-- Finite adaptive information-to-query lower bound, using the true uniform
source, true expected Hamming error, actual history decoder and proved chain rule. -/
theorem finite_query_lower {Ω : Type} [Fintype Ω] {r : ℕ} {E I R : Type}
    [Fintype E] [Fintype I] [Fintype R]
    (P : Law Ω) (source : Ω → RateDistortion.Cube r) (policy : Policy E I R)
    (seed : Ω → E) (responses : Ω → I → R) (n : ℕ)
    (decoder : History E I R n → RateDistortion.Cube r)
    (huniform : ∀ s, P.mass source s = ((2:ℝ)^r)⁻¹)
    (herror : (∑ ω,P.weight ω*RateDistortion.hamming (source ω) (decoder (historyRV policy seed responses n ω))) < (1/25:ℝ)*r)
    (κ : ℝ) (hind : P.Independent (fun ω => (source ω,responses ω)) seed)
    (hlocal : ∀ t ∈ Finset.range n,∀ h : History E I R t,
      0 < P.mass (historyRV policy seed responses t) h → ∀ j,
      policy.choose t h=some j → P.localInformation source (fun ω => responses ω j)
        (historyRV policy seed responses t) h ≤ κ) :
    RateDistortion.cRD*r ≤ κ*expectedQueries P policy seed responses n := by
  let estimate := fun ω => decoder (historyRV policy seed responses n ω)
  have hrd := RateDistortion.lemma4_2 (cubeJoint P source estimate) (by
    intro s
    rw [cubeJoint_source]
    exact huniform s) (by
      rw [expectedHamming_cubeJoint]
      convert herror using 1 <;> norm_num [estimate])
  have hdata := P.information_data_processing source (historyRV policy seed responses n) decoder
  change P.information source estimate ≤ _ at hdata
  rw [information_eq_cubeJoint P source estimate] at hdata
  have hquery := finite_adaptive_transcript_bound P source policy seed responses n κ hind hlocal
  exact hrd.1.trans (hdata.trans hquery)

end Paper29.Transcript
