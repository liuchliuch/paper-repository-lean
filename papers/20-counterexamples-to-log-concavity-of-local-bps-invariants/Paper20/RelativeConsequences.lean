import Paper20.MathasInput
import Paper20.QNormalization
import Paper20.InfinitesimalReturns

namespace Paper20.Relative
open Polynomial Paper20.ExternalInput Paper20.HilbertHeckeBridge
open Paper20.HeckeTraceAlgebra Paper20.HeckeParameterPolynomial Paper20.HeckeWalkExpansion
open Paper20.BraidWalk
noncomputable section
set_option maxHeartbeats 5000000
set_option maxRecDepth 10000

theorem bps_walk (input : MathasInputs) (r k h : ℕ) (hr : 2 ≤ r) (hh : h ≤ deg r k) :
    bpsCoeff r k h=walkCount r k h :=
  bpsCoeff_eq_walk_of_character r k (by omega) (character_origin input r k hr) h hh

theorem bps_bounds (input : MathasInputs) (r k h : ℕ) (hr : 2 ≤ r) (hh : h ≤ deg r k) :
    1 ≤ bpsCoeff r k h ∧ bpsCoeff r k h ≤ Nat.choose (2*deg r k) (2*h) ∧
      bpsCoeff r k 0=1 ∧ bpsCoeff r k (deg r k)=1 := by
  exact ⟨(bps_bounds_of_character r k h (by omega) (character_origin input r k hr) hh).1,
    (bps_bounds_of_character r k h (by omega) (character_origin input r k hr) hh).2,
    bps_endpoints_of_character r k (by omega) (character_origin input r k hr)⟩

theorem bps_Q (input : MathasInputs) (r k h : ℕ) (hr : 2 ≤ r) (hh : h ≤ deg r k) :
    (bpsCoeff r k h:ℚ)=peval (Qcoeff r h) ((k:ℚ)*(k+1)) :=
  bps_Q_evaluation_of_character r k h (by omega) (character_origin input r k hr)
    (character_unit input r k hr) hh

/-- The complete Q coefficient identity, including coefficients beyond
the finite BPS polynomial. This also handles the auxiliary value k=0. -/
theorem Q_walk_all (input : MathasInputs) (r k h : ℕ) (hr : 2 ≤ r) :
    peval (Qcoeff r h) ((k:ℚ)*(k+1))=
      if h ≤ deg r k then (walkCount r k h:ℚ) else 0 := by
  rw [Qcoeff_eq_normalizedPartitionSeries,
    normalized_series_of_character r k (by omega) (character_unit input r k hr),
    Polynomial.coeff_coe,Polynomial.coeff_map,walkBPSPolynomial_coeff]
  split_ifs <;> rfl

theorem Q_at_zero (input : MathasInputs) (r h : ℕ) (hr : 2 ≤ r) :
    peval (Qcoeff r h) 0=if h=0 then 1 else 0 := by
  have he := Q_walk_all input r 0 h hr
  by_cases hh : h=0
  · subst h
    exact (Qcoeff_zero_order_at_zero r).trans (by simp)
  · simpa only [Nat.cast_zero,zero_mul,deg,Nat.zero_mul,
      Nat.le_zero,if_neg hh] using he

lemma choose_two_pos (r : ℕ) (hr : 2 ≤ r) : 1 ≤ Nat.choose r 2 :=
  Nat.one_le_iff_ne_zero.mpr (Nat.choose_ne_zero_iff.mpr hr)

/-- Equality of two independently constructed polynomials follows from
their actual evaluations for all sufficiently large contacts. -/
theorem same_Q_exponent (input : MathasInputs) (r h : ℕ) (hr : 2 ≤ r) :
    (listPolynomial (Qcoeff r h)).comp (X*(X+1))=
      (exponentPolynomial r (2*h)).comp (X+1) := by
  apply Polynomial.eq_of_infinite_eval_eq
  have hi : Function.Injective (fun n : ℕ => (n:ℚ)+(h:ℚ)+1) := by
    intro n m he
    have hn : (n:ℚ)=(m:ℚ) := by linarith
    exact_mod_cast hn
  apply (Set.infinite_range_of_injective hi).mono
  rintro x ⟨n,rfl⟩
  change _=_
  simp only [eval_comp,eval_mul,eval_X,eval_add,eval_one,eval_listPolynomial]
  have hh : h ≤ deg r (n+h+1) := by
    have hc := choose_two_pos r hr
    unfold deg
    nlinarith
  have he := Q_evaluation_of_character r (n+h+1) h (by omega)
    (character_unit input r (n+h+1) hr) hh
  have hw := walkCount_exponent_polynomial r h (n+h+1) (by omega)
  simp only [Nat.cast_add,Nat.cast_one] at he hw
  exact he.trans hw.symm

lemma coeff_comp_monic_bound (p q : ℚ[X]) (h : ℕ) (hp : p.natDegree ≤ h)
    (hq : q.Monic) (hd : q.natDegree≠0) :
    (p.comp q).coeff (h*q.natDegree)=p.coeff h := by
  by_cases he : p.natDegree=h
  · rw [← he,coeff_comp_degree_mul_degree hd,hq.leadingCoeff,one_pow,mul_one]
    rfl
  · have ht : p.natDegree < h := by omega
    rw [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt natDegree_comp_le
      (Nat.mul_lt_mul_of_pos_right ht (Nat.pos_of_ne_zero hd))),
      coeff_eq_zero_of_natDegree_lt ht]

/-- Full Proposition 3.2, for the SAME constructed Q and the independently
defined actual transposition return words. No ordinary character moment
identity is an additional external input. -/
theorem Q_top_returns (input : MathasInputs) (r h : ℕ) (hr : 2 ≤ r) :
    cget (Qcoeff r h) h=(P20Objects.transpositionReturns r h:ℚ)/
      ((2*h).factorial:ℚ) := by
  have hd : (listPolynomial (Qcoeff r h)).natDegree ≤ h :=
    natDegree_le_iff_coeff_eq_zero.mpr (by
      intro i hi
      simpa only [coeff_listPolynomial] using Qcoeff_degree r h i hi)
  have hq : (X*(X+1):ℚ[X]).Monic := monic_X.mul (monic_X_add_C 1)
  have hqdeg : (X*(X+1):ℚ[X]).natDegree=2 := by compute_degree <;> norm_num
  have ht : (X+1:ℚ[X]).Monic := monic_X_add_C 1
  have htdeg : (X+1:ℚ[X]).natDegree=1 := by compute_degree <;> norm_num
  have he := congrArg (fun p : ℚ[X] => p.coeff (2*h)) (same_Q_exponent input r h hr)
  dsimp only at he
  have hl := coeff_comp_monic_bound (listPolynomial (Qcoeff r h)) (X*(X+1)) h hd hq
    (by rw [hqdeg]; decide)
  have hh := coeff_comp_monic_bound (exponentPolynomial r (2*h)) (X+1) (2*h)
    (exponentPolynomial_natDegree r (2*h)) ht (by rw [htdeg]; decide)
  rw [hqdeg,Nat.mul_comm h 2,coeff_listPolynomial] at hl
  rw [htdeg,Nat.mul_one] at hh
  rw [hl,hh] at he
  exact he.trans (exponentPolynomial_top_actual_returns r h (by omega))

/-- Equation (22): the actual partition content moment is the genuine
permutation return cardinal. This follows from the independent polynomial
comparison, without a further ordinary-character external assumption. -/
theorem moment_returns (input : MathasInputs) (r h : ℕ) (hr : 2 ≤ r) :
    transpositionMoment r h=(P20Objects.transpositionReturns r h:ℚ) := by
  have he := (Paper20.prop_3_2 r h).symm.trans (Q_top_returns input r h hr)
  have hm := congrArg (fun x : ℚ => x*((2*h).factorial:ℚ)) he
  dsimp only at hm
  have hf : ((2*h).factorial:ℚ)≠0 := by positivity
  rw [div_mul_cancel₀ _ hf,div_mul_cancel₀ _ hf] at hm
  exact hm

end
end Paper20.Relative
