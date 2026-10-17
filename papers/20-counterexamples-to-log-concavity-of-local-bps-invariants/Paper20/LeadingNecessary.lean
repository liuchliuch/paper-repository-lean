import Paper20.RelativeConsequences
import Mathlib.Analysis.Polynomial.Basic

namespace Paper20.Relative
open Polynomial Filter
open scoped Topology
noncomputable section
set_option maxHeartbeats 5000000
set_option maxRecDepth 10000

lemma Q_natDegree (r h : ℕ) : (listPolynomial (Qcoeff r h)).natDegree ≤ h :=
  natDegree_le_iff_coeff_eq_zero.mpr (by
    intro i hi
    simpa only [coeff_listPolynomial] using Qcoeff_degree r h i hi)

/-- An eventually nonnegative polynomial has a nonnegative coefficient
at any upper bound for its degree, including a vanishing top coefficient. -/
lemma bounded_coeff_nonneg (p : ℚ[X]) (m : ℕ) (hd : p.natDegree ≤ m)
    (he : ∀ᶠ u in atTop, 0 ≤ p.eval u) : 0 ≤ p.coeff m := by
  by_cases hm : p.natDegree=m
  · by_cases hz : m=0
    · have hp : p=C (p.coeff 0) := eq_C_of_natDegree_eq_zero (hm.trans hz)
      obtain ⟨u,hu⟩ := he.exists
      rw [hp,eval_C] at hu
      simpa only [hz] using hu
    · by_contra hn
      have hl : p.leadingCoeff < 0 := by
        rw [leadingCoeff,hm]
        exact lt_of_not_ge hn
      have ht := p.tendsto_atBot_of_leadingCoeff_nonpos
        (natDegree_pos_iff_degree_pos.mp (by omega)) hl.le
      have hneg : ∀ᶠ u in atTop, p.eval u < 0 :=
        ht.eventually (eventually_lt_atBot 0)
      obtain ⟨u,hu,hn⟩ := (he.and hneg).exists
      linarith
  · rw [coeff_eq_zero_of_natDegree_lt (by omega)]

/-- The top-coefficient obstruction is proved for the same Q; this is
the mathematical necessity behind equation (23), not merely its definition. -/
theorem leading_necessary (mathas : ExternalInput.MathasInputs) (r h : ℕ)
    (hr : 2 ≤ r) (hh : 1 ≤ h)
    (he : ∀ᶠ u : ℚ in atTop,
      peval (Qcoeff r (h-1)) u*peval (Qcoeff r (h+1)) u ≤ peval (Qcoeff r h) u^2) :
    ((P20Objects.transpositionReturns r (h-1):ℚ)/((2*(h-1)).factorial:ℚ))*
      ((P20Objects.transpositionReturns r (h+1):ℚ)/((2*(h+1)).factorial:ℚ)) ≤
      ((P20Objects.transpositionReturns r h:ℚ)/((2*h).factorial:ℚ))^2 := by
  let p := listPolynomial (Qcoeff r h)^2-
    listPolynomial (Qcoeff r (h-1))*listPolynomial (Qcoeff r (h+1))
  have hd : p.natDegree ≤ 2*h := by
    dsimp only [p]
    apply (natDegree_sub_le _ _).trans
    apply max_le
    · exact (natDegree_pow_le ..).trans (Nat.mul_le_mul_left 2 (Q_natDegree r h))
    · apply natDegree_mul_le.trans
      have hp := Q_natDegree r (h-1)
      have hn := Q_natDegree r (h+1)
      omega
  have hp : ∀ᶠ u in atTop, 0 ≤ p.eval u := by
    filter_upwards [he] with u hu
    simpa only [p,eval_sub,eval_pow,eval_mul,eval_listPolynomial,sub_nonneg] using hu
  have hc := bounded_coeff_nonneg p (2*h) hd hp
  dsimp only [p] at hc
  rw [coeff_sub,coeff_pow_of_natDegree_le (Q_natDegree r h)] at hc
  have hs : h-1+(h+1)=2*h := by omega
  rw [← hs,coeff_mul_add_eq_of_natDegree_le (Q_natDegree r (h-1))
    (Q_natDegree r (h+1))] at hc
  simp only [coeff_listPolynomial] at hc
  rw [Q_top_returns mathas r h hr,Q_top_returns mathas r (h-1) hr,
    Q_top_returns mathas r (h+1) hr] at hc
  exact sub_nonneg.mp hc

lemma factorial_pair (h : ℕ) :
    ((2*(h+1)).factorial:ℚ)=((2*h+2:ℕ):ℚ)*((2*h+1:ℕ):ℚ)*((2*h).factorial:ℚ) := by
  rw [show 2*(h+1)=(2*h+1)+1 by omega,Nat.factorial_succ,Nat.factorial_succ]
  push_cast
  ring

/-- Equation (23) with genuine transposition returns and its full
eventual-nonnegativity hypothesis. -/
theorem actual_leading_test (mathas : ExternalInput.MathasInputs) (r h : ℕ)
    (hr : 2 ≤ r) (hh : 1 ≤ h)
    (he : ∀ᶠ u : ℚ in atTop,
      peval (Qcoeff r (h-1)) u*peval (Qcoeff r (h+1)) u ≤ peval (Qcoeff r h) u^2) :
    ((2*h+2:ℕ):ℚ)*((2*h+1:ℕ):ℚ)*(P20Objects.transpositionReturns r h:ℚ)^2 ≥
      ((2*h:ℕ):ℚ)*((2*h-1:ℕ):ℚ)*(P20Objects.transpositionReturns r (h-1):ℚ)*
        (P20Objects.transpositionReturns r (h+1):ℚ) := by
  have hi := leading_necessary mathas r h hr hh he
  have hn := factorial_pair h
  have hp := factorial_pair (h-1)
  rw [show h-1+1=h by omega] at hp
  have ha : (0:ℚ) < ((2*h+2:ℕ):ℚ)*((2*h+1:ℕ):ℚ) := by positivity
  have hb : (0:ℚ) < ((2*h:ℕ):ℚ)*((2*h-1:ℕ):ℚ) := by
    have hx : 0 < 2*h-1 := by omega
    positivity
  have hf : (0:ℚ) < ((2*h).factorial:ℚ) := by positivity
  have hprev : ((2*(h-1)).factorial:ℚ)=
      ((2*h).factorial:ℚ)/(((2*h:ℕ):ℚ)*((2*h-1:ℕ):ℚ)) := by
    symm
    rw [div_eq_iff hb.ne']
    rw [show 2*(h-1)+2=2*h by omega,show 2*(h-1)+1=2*h-1 by omega] at hp
    rw [hp]
    ring
  rw [hn,hprev] at hi
  let A : ℚ := ((2*h+2:ℕ):ℚ)*((2*h+1:ℕ):ℚ)
  let B : ℚ := ((2*h:ℕ):ℚ)*((2*h-1:ℕ):ℚ)
  let F : ℚ := ((2*h).factorial:ℚ)
  let t : ℚ := (P20Objects.transpositionReturns r h:ℚ)
  let tp : ℚ := (P20Objects.transpositionReturns r (h-1):ℚ)
  let tn : ℚ := (P20Objects.transpositionReturns r (h+1):ℚ)
  change tp/(F/B)*(tn/(A*F)) ≤ (t/F)^2 at hi
  have hc : (t/F)^2-(tp/(F/B))*(tn/(A*F))=(A*t^2-B*tp*tn)/(A*F^2) := by
    field_simp [show A≠0 from ha.ne',show B≠0 from hb.ne',show F≠0 from hf.ne']
    <;> ring
  have hs := sub_nonneg.mpr hi
  rw [hc] at hs
  have hden : 0 < A*F^2 := mul_pos ha (sq_pos_of_pos hf)
  have hs' := mul_nonneg hs hden.le
  rw [div_mul_cancel₀ _ hden.ne'] at hs'
  exact sub_nonneg.mp hs'

end
end Paper20.Relative
