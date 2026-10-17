import PsgEst.Ergodicity

/-!
# Uniqueness of the source stationary law

For a finite irreducible matrix, two given positive stationary probability laws
coincide. The finite maximum-ratio proof below is independent of any unproved
stationary-distribution existence theorem.
-/

open Matrix BigOperators Real Finset Classical

namespace PsgEst

variable {d : ℕ}

/-- A finite irreducible chain has at most one positive stationary probability law. -/
theorem stationary_mu_unique_of_irreducible (S : Stoch d) (hi : MatrixIrreducible S)
    (st st' : Stationary S) : st.mu = st'.mu := by
  have hd : d ≠ 0 := by
    intro hz
    subst d
    have h := st.sum_one
    simp at h
  letI : NeZero d := ⟨hd⟩
  obtain ⟨i0, -, hmax⟩ := Finset.exists_max_image
    (s := (Finset.univ : Finset (Fin d)))
    (f := fun i => st'.mu i / st.mu i) Finset.univ_nonempty
  let c : ℝ := st'.mu i0 / st.mu i0
  let w : Fin d → ℝ := fun i => c * st.mu i - st'.mu i
  have hw : ∀ i, 0 ≤ w i := by
    intro i
    have h := hmax i (Finset.mem_univ i)
    have h' : st'.mu i ≤ c * st.mu i := by
      exact (div_le_iff₀ (st.pos i)).mp h
    exact sub_nonneg.mpr h'
  have hw0 : w i0 = 0 := by
    dsimp [w, c]
    rw [div_mul_cancel₀ _ (ne_of_gt (st.pos i0)), sub_self]
  have hwstat (j : Fin d) : ∑ i, w i * S.P i j = w j := by
    simp only [w, sub_mul, mul_assoc, Finset.sum_sub_distrib,
      ← Finset.mul_sum, st.station, st'.station]
  have hwzero : ∀ i, w i = 0 := by
    intro i
    obtain ⟨n, hn, hpath⟩ := hi i i0
    have hle : w i * (S.P ^ n) i i0 ≤ ∑ j, w j * (S.P ^ n) j i0 :=
      Finset.single_le_sum (fun j _ => mul_nonneg (hw j) (S.pow_nonneg n j i0))
        (Finset.mem_univ i)
    rw [invariant_weights_pow S w hwstat n i0, hw0] at hle
    nlinarith [hw i]
  have hsum : (∑ i, w i) = c - 1 := by
    simp only [w, Finset.sum_sub_distrib, ← Finset.mul_sum,
      st.sum_one, st'.sum_one, mul_one]
  simp only [hwzero, Finset.sum_const_zero] at hsum
  have hc : c = 1 := by linarith
  funext i
  have h := hwzero i
  dsimp only [w] at h
  rw [hc, one_mul] at h
  linarith

/-- The complete stationary structures coincide as well, since the remaining
fields are proofs. -/
theorem stationary_unique_of_irreducible (S : Stoch d) (hi : MatrixIrreducible S)
    (st st' : Stationary S) : st = st' := by
  have h := stationary_mu_unique_of_irreducible S hi st st'
  cases st with
  | mk mu pos sum_one station =>
    cases st' with
    | mk mu' pos' sum_one' station' =>
      change mu = mu' at h
      cases h
      rfl

/-- Positive pseudo-spectral gap makes the given stationary law intrinsically unique. -/
theorem stationary_unique_of_positive_gap (S : Stoch d) (st st' : Stationary S)
    (hgap : 0 < gammaPS S st) : st = st' :=
  stationary_unique_of_irreducible S (positive_gap_standard_properties S st hgap).1 st st'

/-- In particular the gap value is independent of the stationary-law witness. -/
theorem gammaPS_stationary_unique (S : Stoch d) (st st' : Stationary S)
    (hgap : 0 < gammaPS S st) : gammaPS S st = gammaPS S st' := by
  rw [stationary_unique_of_positive_gap S st st' hgap]

end PsgEst
