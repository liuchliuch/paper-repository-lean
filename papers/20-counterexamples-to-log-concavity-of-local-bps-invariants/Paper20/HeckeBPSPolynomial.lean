import Paper20.BraidParity

namespace Paper20.HeckeWalkExpansion
open Polynomial Paper20.BraidWalk
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

lemma wordAction_coeff_zero {I S : Type*} (move : I → S → S) (allowed : I → S → Prop)
    (word : List I) (top : S) (n : ℕ)
    (hn : ∀ w : Walks.Walk word.length,
      admissible move allowed top word w → Walks.nStays w ≠ n) :
    (wordAction move allowed (X:ℤ[X]) word (delta top) top).coeff n=0 := by
  classical
  rw [wordAction_closed,finset_sum_coeff]
  apply Finset.sum_eq_zero
  intro w hw
  by_cases ha : admissible move allowed top word w
  · simp [ha,coeff_X_pow,Ne.symm (hn w ha)]
  · simp [ha]

theorem closedHeckePolynomial_odd (r k n : ℕ) (hn : ¬2 ∣ n) :
    (closedHeckePolynomial r k).coeff n=0 := by
  unfold closedHeckePolynomial
  apply wordAction_coeff_zero
  intro w hw hstay
  have he := admissible_even_stays (halfWord r k++(halfWord r k).reverse)
    Fin.revPerm w (by simp [List.length_append,List.length_reverse,even_two_mul]) hw
  rw [hstay] at he
  exact hn (even_iff_two_dvd.mp he)

theorem closedHeckePolynomial_above (r k n : ℕ) (hn : 2*deg r k < n) :
    (closedHeckePolynomial r k).coeff n=0 := by
  unfold closedHeckePolynomial
  apply wordAction_coeff_zero
  intro w hw hstay
  have he := Walks.nStays_le w
  have he' : Walks.nStays w ≤ 2*deg r k := by
    simpa only [List.length_append,List.length_reverse,halfWord_length,two_mul] using he
  omega

/-- The polynomial in w obtained from all actual admissible adjacent
permutation walks. Its construction is independent of the Hilbert program. -/
def walkBPSPolynomial (r k : ℕ) : ℤ[X] :=
  ∑ h ∈ Finset.range (deg r k+1), monomial h (walkCount r k h:ℤ)

lemma walkBPSPolynomial_coeff (r k i : ℕ) :
    (walkBPSPolynomial r k).coeff i = if i ≤ deg r k then (walkCount r k i:ℤ) else 0 := by
  classical
  simp only [walkBPSPolynomial,finset_sum_coeff,coeff_monomial]
  by_cases hi : i ≤ deg r k
  · rw [if_pos hi]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j hj hji; simp [hji,Ne.symm hji]
    · intro hnot; exact False.elim (hnot (Finset.mem_range.mpr (by omega)))
  · rw [if_neg hi]
    apply Finset.sum_eq_zero
    intro j hj
    have hj' := Finset.mem_range.mp hj
    simp [show j ≠ i by omega]

/-- The actual closed Hecke polynomial is exactly the w-polynomial after
w=z². Odd powers vanish by the proved permutation-parity argument. -/
theorem closedHeckePolynomial_eq_comp (r k : ℕ) :
    closedHeckePolynomial r k = (walkBPSPolynomial r k).comp (X^2) := by
  ext n
  rw [← expand_eq_comp_X_pow,coeff_expand (by decide : 0 < 2)]
  by_cases hn : 2 ∣ n
  · rw [if_pos hn]
    obtain ⟨j,rfl⟩ := hn
    rw [walkBPSPolynomial_coeff,Nat.mul_div_right j (by decide)]
    split_ifs with hj
    · exact closedHeckePolynomial_coeff r k j
    · rw [closedHeckePolynomial_above r k (2*j) (by omega)]
  · rw [if_neg hn]
    exact closedHeckePolynomial_odd r k n hn

theorem walkBPSPolynomial_bounds (r k h : ℕ) (hh : h ≤ deg r k) :
    1 ≤ (walkBPSPolynomial r k).coeff h ∧
      (walkBPSPolynomial r k).coeff h ≤ (Nat.choose (2*deg r k) (2*h):ℤ) := by
  rw [walkBPSPolynomial_coeff,if_pos hh]
  exact_mod_cast walk_bounds r k h hh

theorem walkBPSPolynomial_endpoints (r k : ℕ) :
    (walkBPSPolynomial r k).coeff 0=1 ∧
      (walkBPSPolynomial r k).coeff (deg r k)=1 := by
  rw [walkBPSPolynomial_coeff,if_pos (Nat.zero_le _),
    walkBPSPolynomial_coeff,if_pos le_rfl]
  exact_mod_cast walk_endpoints r k

end
end Paper20.HeckeWalkExpansion
