import Paper25.PhaseEstCore

/-!
# Appendix B: integer-lattice counting of bad phase-estimation labels

The finite grid of phase labels lifts injectively to an integer lattice around
any fixed eigenphase. This makes the two-sided tail argument independent of a
chosen representative of the eigenphase.
-/

noncomputable section

namespace Paper25

/-- One side of a translated integer lattice is bounded by the complete
positive tail starting at `a`. -/
lemma integer_lattice_one_sided_tail (s : Finset ℤ) (x a : ℝ) (ha : 0 < a)
    (hs : ∀ z ∈ s, a < x - z) :
    (∑ z ∈ s, 1 / (x - z) ^ 2) ≤ ∑' r : ℕ, 1 / (a + (r : ℝ)) ^ 2 := by
  classical
  let rank : ℤ → ℕ := fun z => Int.toNat (⌊x - a⌋ - z)
  have hrank : ∀ z ∈ s, (rank z : ℤ) = ⌊x - a⌋ - z := by
    intro z hz
    have hzle : z ≤ ⌊x - a⌋ := Int.le_floor.mpr (by linarith [hs z hz])
    exact Int.toNat_of_nonneg (sub_nonneg.mpr hzle)
  have hle : ∀ z ∈ s, a + (rank z : ℝ) ≤ x - z := by
    intro z hz
    have hc : (rank z : ℝ) = (⌊x - a⌋ : ℝ) - z := by
      exact_mod_cast hrank z hz
    rw [hc]
    linarith [Int.floor_le (x - a)]
  have hinj : ∀ z ∈ s, ∀ w ∈ s, rank z = rank w → z = w := by
    intro z hz w hw heq
    have hc : (rank z : ℤ) = (rank w : ℤ) := congrArg (fun t : ℕ => (t : ℤ)) heq
    rw [hrank z hz, hrank w hw] at hc
    omega
  calc
    (∑ z ∈ s, 1 / (x - z) ^ 2) ≤ ∑ z ∈ s, 1 / (a + (rank z : ℝ)) ^ 2 := by
      apply Finset.sum_le_sum
      intro z hz
      have hpos : 0 < a + (rank z : ℝ) := by positivity
      apply one_div_le_one_div_of_le (sq_pos_of_pos hpos)
      nlinarith [hle z hz, hs z hz]
    _ = ∑ r ∈ s.image rank, 1 / (a + (r : ℝ)) ^ 2 :=
      by rw [Finset.sum_image hinj]
    _ ≤ ∑' r : ℕ, 1 / (a + (r : ℝ)) ^ 2 :=
      (summable_one_div_add_sq a ha).sum_le_tsum _ (fun _ _ => by positivity)

/-- Two-sided inverse-square tail of any finite subset of the integer lattice.
The factor `1/4` is the phase-estimation geometric-sum factor. -/
theorem integer_lattice_two_sided_tail (s : Finset ℤ) (x a : ℝ) (ha : 1 ≤ a)
    (hs : ∀ z ∈ s, a < |x - z|) :
    (∑ z ∈ s, 1 / (4 * (x - z) ^ 2)) ≤ 1 / a := by
  classical
  have ha0 : 0 < a := lt_of_lt_of_le (by norm_num) ha
  let left : Finset ℤ := s.filter (fun z : ℤ => 0 ≤ x - z)
  let right : Finset ℤ := s.filter (fun z : ℤ => ¬0 ≤ x - z)
  have hleft : ∀ z ∈ left, a < x - z := by
    intro z hz
    have hz' := Finset.mem_filter.mp hz
    simpa only [abs_of_nonneg hz'.2] using hs z hz'.1
  have hright : ∀ z ∈ right, a < -x - (-z : ℤ) := by
    intro z hz
    have hz' := Finset.mem_filter.mp hz
    have h := hs z hz'.1
    rw [abs_of_neg (lt_of_not_ge hz'.2)] at h
    push_cast
    linarith
  have hL := integer_lattice_one_sided_tail left x a ha0 hleft
  have hR0 := integer_lattice_one_sided_tail (right.image Neg.neg) (-x) a ha0 (by
    intro z hz
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
    exact hright w hw)
  have hR : (∑ z ∈ right, 1 / (x - z) ^ 2) ≤ ∑' r : ℕ, 1 / (a + (r : ℝ)) ^ 2 := by
    convert hR0 using 1
    rw [Finset.sum_image (fun _ _ _ _ h => neg_injective h)]
    apply Finset.sum_congr rfl
    intro z _
    push_cast
    congr 1
    ring
  have hsplit : (∑ z ∈ s, 1 / (x - z) ^ 2)
      = (∑ z ∈ left, 1 / (x - z) ^ 2) + (∑ z ∈ right, 1 / (x - z) ^ 2) := by
    exact (Finset.sum_filter_add_sum_filter_not s (fun z => 0 ≤ x - z) _).symm
  have hquarter : (∑ z ∈ s, 1 / (4 * (x - z) ^ 2))
      = (1 / 4) * ∑ z ∈ s, 1 / (x - z) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z _
    simp only [one_div, mul_inv_rev]
    ring
  rw [hquarter, hsplit]
  have htail := failure_prob_bound a ha
  linarith

/-- The phase-estimation amplitude at label `j`, exactly as in Appendix B. -/
def phaseEstAmplitude (M : ℕ) (φ : ℝ) (j : Fin M) : ℂ :=
  (M : ℂ)⁻¹ * ∑ r ∈ Finset.range M,
    Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) * (φ - (j : ℝ) / M))

/-- The probability of a phase-estimation label. -/
def phaseEstProb (M : ℕ) (φ : ℝ) (j : Fin M) : ℝ :=
  ‖phaseEstAmplitude M φ j‖ ^ 2

lemma phaseEstProb_nonneg (M : ℕ) (φ : ℝ) (j : Fin M) :
    0 ≤ phaseEstProb M φ j := sq_nonneg _

/-- Lift a phase label to its nearest translate around `M φ`. -/
def phaseEstOffset (M : ℕ) (φ : ℝ) (j : Fin M) : ℤ :=
  (j.val : ℤ) + (M : ℤ) * round (φ - (j : ℝ) / M)

lemma phaseEstOffset_injective (M : ℕ) (φ : ℝ) :
    Function.Injective (phaseEstOffset M φ) := by
  intro j k h
  have hm := congrArg (fun z : ℤ => z % (M : ℤ)) h
  simp only [phaseEstOffset, Int.add_mul_emod_self_left] at hm
  rw [Int.emod_eq_of_lt (by omega) (by exact_mod_cast j.isLt),
    Int.emod_eq_of_lt (by omega) (by exact_mod_cast k.isLt)] at hm
  exact Fin.ext (by exact_mod_cast hm)

/-- Multiplying circular distance by `M` gives distance to the lifted label. -/
lemma phaseEstOffset_dist (M : ℕ) (φ : ℝ) (hM : 0 < M) (j : Fin M) :
    |(M : ℝ) * φ - phaseEstOffset M φ j| =
      (M : ℝ) * circDist (φ - (j : ℝ) / M) := by
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have hid : (M : ℝ) * (φ - (j : ℝ) / M - round (φ - (j : ℝ) / M))
      = (M : ℝ) * φ - phaseEstOffset M φ j := by
    simp only [phaseEstOffset, Int.cast_add, Int.cast_mul, Int.cast_natCast]
    field_simp
    <;> ring
  rw [← hid, abs_mul, abs_of_pos hMpos]
  rfl

/-- The individual probability bound expressed on the lifted integer lattice. -/
lemma phaseEstProb_le_lattice (M : ℕ) (φ : ℝ) (hM : 0 < M) (j : Fin M)
    (hΔ : 0 < circDist (φ - (j : ℝ) / M)) :
    phaseEstProb M φ j ≤ 1 / (4 * ((M : ℝ) * φ - phaseEstOffset M φ j) ^ 2) := by
  have h := geometric_sum_bound_circDist M (φ - (j : ℝ) / M)
    (circDist (φ - (j : ℝ) / M)) hM hΔ (circDist_le_half _) rfl
  have heq : 4 * (M : ℝ) ^ 2 * circDist (φ - (j : ℝ) / M) ^ 2
      = 4 * ((M : ℝ) * φ - phaseEstOffset M φ j) ^ 2 := by
    rw [← sq_abs ((M : ℝ) * φ - phaseEstOffset M φ j),
      phaseEstOffset_dist M φ hM j]
    ring
  rw [heq] at h
  simpa only [phaseEstProb, phaseEstAmplitude, Complex.ofReal_sub, Complex.ofReal_div,
    Complex.ofReal_natCast] using h

/-- Appendix B's failure-probability bound for the actual amplitudes.
It holds for every eigenphase, with no assumption on its representative. -/
theorem phaseEst_failure_probability (M : ℕ) (φ ζ : ℝ) (hM : 0 < M)
    (hζ : 0 < ζ) (hMζ : 1 ≤ (M : ℝ) * ζ) :
    (∑ j : Fin M, phaseEstProb M φ j *
      (if ζ < circDist (φ - (j : ℝ) / M) then 1 else 0)) ≤ 1 / ((M : ℝ) * ζ) := by
  classical
  let bad : Finset (Fin M) := Finset.univ.filter
    (fun j => ζ < circDist (φ - (j : ℝ) / M))
  let lifted : Finset ℤ := bad.image (phaseEstOffset M φ)
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have hbad : ∀ z ∈ lifted, (M : ℝ) * ζ < |(M : ℝ) * φ - z| := by
    intro z hz
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hz
    have hj' := (Finset.mem_filter.mp hj).2
    rw [phaseEstOffset_dist M φ hM j]
    exact mul_lt_mul_of_pos_left hj' hMpos
  have htail := integer_lattice_two_sided_tail lifted ((M : ℝ) * φ)
    ((M : ℝ) * ζ) hMζ hbad
  have hsum : (∑ j ∈ bad, phaseEstProb M φ j)
      ≤ ∑ z ∈ lifted, 1 / (4 * ((M : ℝ) * φ - z) ^ 2) := by
    rw [Finset.sum_image (fun _ _ _ _ h => phaseEstOffset_injective M φ h)]
    apply Finset.sum_le_sum
    intro j hj
    exact phaseEstProb_le_lattice M φ hM j (hζ.trans (Finset.mem_filter.mp hj).2)
  have hid : (∑ j : Fin M, phaseEstProb M φ j *
      (if ζ < circDist (φ - (j : ℝ) / M) then 1 else 0))
      = ∑ j ∈ bad, phaseEstProb M φ j := by
    simp only [bad, Finset.sum_filter, mul_ite, mul_one, mul_zero]
  rw [hid]
  exact hsum.trans htail

/-- Lipschitz continuity on the circle, rather than on an arbitrary chosen
real representative of the phase. -/
lemma filterG_circular_change (δ φ ψ : ℝ) (hδ : 0 < δ) :
    |filterG δ (2 * Real.pi * φ) - filterG δ (2 * Real.pi * ψ)|
      ≤ 2 * Real.pi * circDist (φ - ψ) / δ := by
  have hperiod : filterG δ
      (2 * Real.pi * φ - (round (φ - ψ) : ℝ) * (2 * Real.pi))
      = filterG δ (2 * Real.pi * φ) := by
    simp only [filterG, Real.cos_sub_int_mul_two_pi]
  have h := filterG_abs_sub_le δ
    (2 * Real.pi * φ - (round (φ - ψ) : ℝ) * (2 * Real.pi))
    (2 * Real.pi * ψ) hδ
  rw [hperiod] at h
  have hid : |2 * Real.pi * φ - (round (φ - ψ) : ℝ) * (2 * Real.pi)
      - 2 * Real.pi * ψ| = 2 * Real.pi * circDist (φ - ψ) := by
    rw [show 2 * Real.pi * φ - (round (φ - ψ) : ℝ) * (2 * Real.pi)
        - 2 * Real.pi * ψ = 2 * Real.pi * (φ - ψ - round (φ - ψ)) by ring,
      abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
    rfl
  rwa [hid] at h

/-- The analytic phase-average estimate from Appendix B, using the actual
amplitudes. The normalization hypothesis is precisely the remaining Parseval
identity for the phase-estimation transform. -/
theorem phaseEst_filter_average_error_of_normalized
    (M : ℕ) (δ ε φ : ℝ) (hδ : 0 < δ) (hδle : δ ≤ 1)
    (hε : 0 < ε) (hεle : ε ≤ 1)
    (hMdef : 4096 / (δ * ε ^ 2) ≤ (M : ℝ))
    (hnormalized : ∑ j : Fin M, phaseEstProb M φ j = 1) :
    |(∑ j : Fin M, phaseEstProb M φ j * filterG δ (2 * Real.pi * ((j : ℝ) / M)))
      - filterG δ (2 * Real.pi * φ)| ≤ ε / 8 := by
  classical
  let ζ : ℝ := ε * δ / (32 * Real.pi)
  have hbudget := phase_est_error_bound δ ε ζ M hδ hδle hε hεle rfl hMdef
  have hM : 0 < M := by
    have : 0 < (M : ℝ) := lt_of_lt_of_le (by positivity) hMdef
    exact_mod_cast this
  let bad : Fin M → Prop := fun j => ζ < circDist (φ - (j : ℝ) / M)
  let d : Fin M → ℝ := fun j =>
    |filterG δ (2 * Real.pi * ((j : ℝ) / M)) - filterG δ (2 * Real.pi * φ)|
  have hgood : ∀ j, ¬bad j → d j ≤ ε / 16 := by
    intro j hj
    have hdist : circDist (φ - (j : ℝ) / M) ≤ ζ := le_of_not_gt hj
    have hcircle := filterG_circular_change δ φ ((j : ℝ) / M) hδ
    have hsmall : 2 * Real.pi * circDist (φ - (j : ℝ) / M) / δ
        ≤ 2 * Real.pi * ζ / δ := by gcongr
    change |filterG δ (2 * Real.pi * ((j : ℝ) / M)) - filterG δ (2 * Real.pi * φ)| ≤ _
    rw [abs_sub_comm]
    exact hcircle.trans (hsmall.trans_eq hbudget.2.2.1)
  have hbad : ∀ j, bad j → d j ≤ 1 := by
    intro j _
    have htriangle := abs_sub (filterG δ (2 * Real.pi * ((j : ℝ) / M)))
      (filterG δ (2 * Real.pi * φ))
    have h₁ := filterG_range_bound δ (2 * Real.pi * ((j : ℝ) / M)) hδ
    have h₂ := filterG_range_bound δ (2 * Real.pi * φ) hδ
    change |_ - _| ≤ _
    linarith
  have hprob : ∑ j, phaseEstProb M φ j * (if bad j then 1 else 0)
      ≤ Real.pi * ε / 128 :=
    (phaseEst_failure_probability M φ ζ hM hbudget.1.1 hbudget.2.1.1).trans hbudget.2.1.2
  have havg := phase_est_average_error_eps ε hε.le (phaseEstProb M φ) d bad
    (phaseEstProb_nonneg M φ) hnormalized hgood hbad hprob
  have hid : (∑ j : Fin M, phaseEstProb M φ j * filterG δ (2 * Real.pi * ((j : ℝ) / M)))
      - filterG δ (2 * Real.pi * φ)
      = ∑ j : Fin M, phaseEstProb M φ j *
        (filterG δ (2 * Real.pi * ((j : ℝ) / M)) - filterG δ (2 * Real.pi * φ)) := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hnormalized, one_mul]
  rw [hid]
  calc
    |∑ j : Fin M, phaseEstProb M φ j *
        (filterG δ (2 * Real.pi * ((j : ℝ) / M)) - filterG δ (2 * Real.pi * φ))|
      ≤ ∑ j : Fin M, |phaseEstProb M φ j *
        (filterG δ (2 * Real.pi * ((j : ℝ) / M)) - filterG δ (2 * Real.pi * φ))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j : Fin M, phaseEstProb M φ j * d j := by
      apply Finset.sum_congr rfl
      intro j _
      rw [abs_mul, abs_of_nonneg (phaseEstProb_nonneg M φ j)]
    _ ≤ ε / 8 := havg

end Paper25
