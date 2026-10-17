import Paper29.DataProcessing
import Paper29.RateDistortion

noncomputable section
open scoped BigOperators Classical
namespace Paper29.Transcript.Law

variable {Ω A B : Type} [Fintype Ω] [Fintype A] [Fintype B]

theorem information_le_entropy_right (P : Law Ω) (X : Ω → A) (Y : Ω → B) :
    P.information X Y ≤ P.entropy Y := by
  have hpoint (ω : Ω) :
      P.weight ω*(Real.log (P.mass (fun η => (X η,Y η)) (X ω,Y ω))-Real.log (P.mass X (X ω))) ≤ 0 := by
    by_cases hz : P.weight ω=0
    · simp [hz]
    have hp : 0 < P.weight ω := lt_of_le_of_ne (P.nonneg ω) (Ne.symm hz)
    have hj : 0 < P.mass (fun η => (X η,Y η)) (X ω,Y ω) :=
      hp.trans_le (P.weight_le_observed_mass _ ω)
    have hle : P.mass (fun η => (X η,Y η)) (X ω,Y ω) ≤ P.mass X (X ω) := by
      have h := Finset.single_le_sum (s:=Finset.univ)
        (fun b _ => P.mass_nonneg (fun η => (X η,Y η)) (X ω,b)) (Finset.mem_univ (Y ω))
      rwa [P.sum_pair_mass_right] at h
    exact mul_nonpos_of_nonneg_of_nonpos hp.le (sub_nonpos.mpr (Real.log_le_log hj hle))
  have hs := Finset.sum_le_sum (s:=Finset.univ) (fun ω _ => hpoint ω)
  simp only [Finset.sum_const_zero] at hs
  unfold information entropy
  simp only [mul_sub,Finset.sum_sub_distrib] at hs ⊢
  linarith

theorem entropy_le_log_card (P : Law Ω) (Y : Ω → B) [Nonempty B] :
    P.entropy Y ≤ Real.log (Fintype.card B) := by
  have hcard : (0:ℝ) < Fintype.card B := by exact_mod_cast Fintype.card_pos
  have hsum := Finset.sum_le_sum (s:=Finset.univ) (fun b _ =>
    RateDistortion.gibbs_term (P.mass Y b) 1 ((Fintype.card B:ℝ)⁻¹)
      (P.mass_nonneg _ _) (by
        have h := Finset.single_le_sum (s:=Finset.univ) (fun c _ => P.mass_nonneg Y c) (Finset.mem_univ b)
        rwa [P.mass_total] at h) (inv_pos.mpr hcard))
  simp only [Real.log_inv,Real.log_one,sub_zero,mul_one,one_mul,
    Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.sum_mul,P.mass_total,
    Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hsum
  rw [mul_inv_cancel₀ hcard.ne'] at hsum
  rw [P.entropy_eq_sum]
  linarith

theorem information_le_log_card (P : Law Ω) (X : Ω → A) (Y : Ω → B) [Nonempty B] :
    P.information X Y ≤ Real.log (Fintype.card B) :=
  (P.information_le_entropy_right X Y).trans (P.entropy_le_log_card Y)

end Paper29.Transcript.Law
