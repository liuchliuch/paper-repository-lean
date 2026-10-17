import Paper29.InformationAlgebra
import Paper29.HardDefs
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

noncomputable section
open scoped BigOperators Classical
namespace Paper29.InformationAlgebra

theorem bernoulliKL_log {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) (hq1 : q < 1) :
    bernoulliKL p q = p*(Real.log p-Real.log q)+(1-p)*(Real.log (1-p)-Real.log (1-q)) := by
  unfold bernoulliKL
  rw [Real.log_div hp.ne' hq.ne',Real.log_div (by linarith : 1-p≠0) (by linarith : 1-q≠0)]

/-- Convexity in the second Bernoulli argument, proved by finite concave-log
Jensen for an arbitrary posterior distribution. -/
theorem bernoulliKL_mixture {S : Type*} [Fintype S] (θ q : S → ℝ)
    (hθ : ∀ s, 0 ≤ θ s) (hsum : ∑ s,θ s = 1) (hq : ∀ s, 0 < q s) (hq1 : ∀ s, q s < 1)
    (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    bernoulliKL p (∑ s,θ s*q s) ≤ ∑ s,θ s*bernoulliKL p (q s) := by
  have hqmix : 0 < ∑ s,θ s*q s := by
    haveI : Nonempty S := by
      by_contra h
      haveI : IsEmpty S := not_nonempty_iff.mp h
      simpa using hsum
    have hsumne : (∑ s,θ s) ≠ 0 := by rw [hsum]; norm_num
    obtain ⟨s,_,hs⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsumne
    have hs0 : 0 < θ s := lt_of_le_of_ne (hθ s) (Ne.symm hs)
    exact Finset.sum_pos' (fun s _ => mul_nonneg (hθ s) (hq s).le)
      ⟨s,Finset.mem_univ _,mul_pos hs0 (hq s)⟩
  have hcomp : (∑ s,θ s*(1-q s)) = 1-∑ s,θ s*q s := by
    simp only [mul_sub,mul_one,Finset.sum_sub_distrib,hsum]
  have hqmix1 : (∑ s,θ s*q s) < 1 := by
    haveI : Nonempty S := by
      by_contra h
      haveI : IsEmpty S := not_nonempty_iff.mp h
      simpa using hsum
    have hsumne : (∑ s,θ s) ≠ 0 := by rw [hsum]; norm_num
    obtain ⟨s,_,hs⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsumne
    have hs0 : 0 < θ s := lt_of_le_of_ne (hθ s) (Ne.symm hs)
    have hpos : 0 < ∑ s,θ s*(1-q s) := Finset.sum_pos'
      (fun s _ => mul_nonneg (hθ s) (by linarith [hq1 s]))
      ⟨s,Finset.mem_univ _,mul_pos hs0 (by linarith [hq1 s])⟩
    rw [hcomp] at hpos
    linarith
  have hj₁ := strictConcaveOn_log_Ioi.concaveOn.le_map_sum (t:=Finset.univ)
    (fun s _ => hθ s) hsum (fun s _ => hq s)
  have hj₂ := strictConcaveOn_log_Ioi.concaveOn.le_map_sum (t:=Finset.univ)
    (fun s _ => hθ s) hsum (fun s _ => show (1-q s)∈Set.Ioi (0:ℝ) by exact sub_pos.mpr (hq1 s))
  simp only [smul_eq_mul] at hj₁ hj₂
  rw [hcomp] at hj₂
  rw [bernoulliKL_log hp hp1 hqmix hqmix1]
  have he : (∑ s,θ s*bernoulliKL p (q s)) =
      p*Real.log p+(1-p)*Real.log (1-p)-
        p*(∑ s,θ s*Real.log (q s))-(1-p)*(∑ s,θ s*Real.log (1-q s)) := by
    simp_rw [bernoulliKL_log hp hp1 (hq _) (hq1 _)]
    simp only [mul_add,mul_sub,Finset.sum_add_distrib,Finset.sum_sub_distrib]
    have hconst (c : ℝ) : (∑ s,θ s*c) = c := by rw [← Finset.sum_mul,hsum,one_mul]
    rw [hconst,hconst]
    have hfactor (c : ℝ) (f : S → ℝ) : (∑ s,θ s*(c*f s)) = c*(∑ s,θ s*f s) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      ring
    rw [hfactor p (fun s => Real.log (q s)),hfactor (1-p) (fun s => Real.log (1-q s))]
    ring
  rw [he]
  have h₁ := mul_le_mul_of_nonneg_left hj₁ hp.le
  have h₂ := mul_le_mul_of_nonneg_left hj₂ (by linarith : 0 ≤ 1-p)
  nlinarith only [h₁,h₂]

/-- Information of a binary observation under an arbitrary finite posterior. -/
def biasedChannelInformation {S : Type*} [Fintype S] (θ : S → ℝ) (σ : S → Bool) (β : ℝ) : ℝ :=
  ∑ s,θ s*bernoulliKL (1/2+β*HardDistribution.sign (σ s))
    (∑ t,θ t*(1/2+β*HardDistribution.sign (σ t)))

/-- The <=16 beta² step in (4.9), uniformly over every possible posterior. -/
theorem biasedChannelInformation_le {S : Type*} [Fintype S] (θ : S → ℝ) (σ : S → Bool)
    (hθ : ∀ s, 0 ≤ θ s) (hsum : ∑ s,θ s = 1) (β : ℝ) (hβ : 0 ≤ β) (hβhi : β ≤ 1/4) :
    biasedChannelInformation θ σ β ≤ 16*β^2 := by
  let p := fun s => 1/2+β*HardDistribution.sign (σ s)
  have hp (s) : 0 < p s := by dsimp [p,HardDistribution.sign]; split_ifs <;> linarith
  have hp1 (s) : p s < 1 := by dsimp [p,HardDistribution.sign]; split_ifs <;> linarith
  have hself (s) : bernoulliKL (p s) (p s) = 0 := by
    rw [bernoulliKL_log (hp s) (hp1 s) (hp s) (hp1 s)]
    ring
  have hpair (s t) : bernoulliKL (p s) (p t) ≤ 16*β^2 := by
    by_cases he : σ s = σ t
    · have he' : p s = p t := by simp only [p,he]
      rw [← he',hself]
      positivity
    · cases hs : σ s <;> cases ht : σ t
      · exact False.elim (he (by rw [hs,ht]))
      · have hh : bernoulliKL (1/2-β) (1/2+β) ≤ 16*β^2 := by
          rw [biased_bernoulli_reverse_kl β hβ hβhi]
          exact biased_bernoulli_kl_bound β hβ hβhi
        simpa [p,hs,ht,HardDistribution.sign] using hh
      · simpa [p,hs,ht,HardDistribution.sign] using biased_bernoulli_kl_bound β hβ hβhi
      · exact False.elim (he (by rw [hs,ht]))
  unfold biasedChannelInformation
  calc
    _ ≤ ∑ s,θ s*(∑ t,θ t*bernoulliKL (p s) (p t)) := by
      apply Finset.sum_le_sum
      intro s _
      exact mul_le_mul_of_nonneg_left (bernoulliKL_mixture θ p hθ hsum hp hp1 (p s) (hp s) (hp1 s)) (hθ s)
    _ ≤ ∑ s,θ s*(∑ t,θ t*(16*β^2)) := by
      apply Finset.sum_le_sum
      intro s _
      apply mul_le_mul_of_nonneg_left _ (hθ s)
      apply Finset.sum_le_sum
      intro t _
      exact mul_le_mul_of_nonneg_left (hpair s t) (hθ t)
    _ = _ := by simp only [← Finset.sum_mul,hsum,one_mul]

end Paper29.InformationAlgebra
