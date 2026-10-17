import Paper29.BernoulliChannel
import Paper29.Transcript

noncomputable section
open scoped BigOperators Classical
namespace Paper29.Transcript
open InformationAlgebra HardDistribution

/-- The actual finite mutual information equals the channel expression whenever
the selected fresh bit has the original Bernoulli law conditional on the source.
Zero-probability source symbols are handled explicitly. -/
theorem Law.information_eq_biasedChannel {Ω S : Type*} [Fintype Ω] [Fintype S]
    (P : Law Ω) (source : Ω → S) (Y : Ω → Bool) (σ : S → Bool) (β : ℝ)
    (hβ : 0 ≤ β) (hβhi : β ≤ 1/4)
    (hchannel : ∀ s b, P.mass (fun ω => (source ω,Y ω)) (s,b) =
      P.mass source s * bitMass (1/2+β*sign (σ s)) b) :
    P.information source Y = biasedChannelInformation (P.mass source) σ β := by
  let p := fun s => 1/2+β*sign (σ s)
  let q := ∑ s,P.mass source s*p s
  have hp (s) : 0 < p s := by dsimp [p,sign]; split_ifs <;> linarith
  have hp1 (s) : p s < 1 := by dsimp [p,sign]; split_ifs <;> linarith
  have hmtrue : P.mass Y true = q := by
    rw [← P.sum_pair_mass_left source Y true]
    simp only [hchannel,bitMass,↓reduceIte]
    rfl
  have hmfalse : P.mass Y false = 1-q := by
    have ht := P.mass_total Y
    simp only [Fintype.sum_bool,hmtrue] at ht
    linarith
  have hq : 0 < q := by
    have hs : (∑ s,P.mass source s) ≠ 0 := by rw [P.mass_total]; norm_num
    obtain ⟨s,_,hs⟩ := Finset.exists_ne_zero_of_sum_ne_zero hs
    have hspos : 0 < P.mass source s := lt_of_le_of_ne (P.mass_nonneg source s) (Ne.symm hs)
    exact Finset.sum_pos' (fun s _ => mul_nonneg (P.mass_nonneg source s) (hp s).le)
      ⟨s,Finset.mem_univ _,mul_pos hspos (hp s)⟩
  have hq1 : q < 1 := by
    have hs : (∑ s,P.mass source s) ≠ 0 := by rw [P.mass_total]; norm_num
    obtain ⟨s,_,hs⟩ := Finset.exists_ne_zero_of_sum_ne_zero hs
    have hspos : 0 < P.mass source s := lt_of_le_of_ne (P.mass_nonneg source s) (Ne.symm hs)
    have hpos : 0 < ∑ s,P.mass source s*(1-p s) := Finset.sum_pos'
      (fun s _ => mul_nonneg (P.mass_nonneg source s) (sub_pos.mpr (hp1 s)).le)
      ⟨s,Finset.mem_univ _,mul_pos hspos (sub_pos.mpr (hp1 s))⟩
    simp only [mul_sub,mul_one,Finset.sum_sub_distrib,P.mass_total] at hpos
    exact sub_pos.mp hpos
  rw [P.information_eq_joint_sum]
  unfold biasedChannelInformation
  apply Finset.sum_congr rfl
  intro s _
  by_cases hs : P.mass source s = 0
  · simp [hchannel,hs]
  · have hspos := lt_of_le_of_ne (P.mass_nonneg source s) (Ne.symm hs)
    simp only [Fintype.sum_bool,hchannel,bitMass,Bool.false_eq_true,↓reduceIte,hmtrue,hmfalse]
    rw [Real.log_mul hspos.ne' (hp s).ne',
      Real.log_mul hspos.ne' (sub_pos.mpr (hp1 s)).ne',bernoulliKL_log (hp s) (hp1 s) hq hq1]
    change _ = P.mass source s*(p s*(Real.log (p s)-Real.log q)+
      (1-p s)*(Real.log (1-p s)-Real.log (1-q)))
    ring

/-- The finite local information budget in (4.9), now attached to literal
Shannon information rather than a standalone KL estimate. -/
theorem Law.biased_bit_information_le {Ω S : Type*} [Fintype Ω] [Fintype S]
    (P : Law Ω) (source : Ω → S) (Y : Ω → Bool) (σ : S → Bool) (β : ℝ)
    (hβ : 0 ≤ β) (hβhi : β ≤ 1/4)
    (hchannel : ∀ s b, P.mass (fun ω => (source ω,Y ω)) (s,b) =
      P.mass source s * bitMass (1/2+β*sign (σ s)) b) :
    P.information source Y ≤ 16*β^2 := by
  rw [P.information_eq_biasedChannel source Y σ β hβ hβhi hchannel]
  exact biasedChannelInformation_le (P.mass source) σ (P.mass_nonneg source) (P.mass_total source) β hβ hβhi

end Paper29.Transcript
