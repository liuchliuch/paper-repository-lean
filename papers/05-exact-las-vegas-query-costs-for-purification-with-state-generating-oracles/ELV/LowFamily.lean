import ELV.BoundaryOracle

/-! Infinitely many distinct legal low instances used in Proposition 4.2. -/
noncomputable section
namespace ELV.Model
variable {n : ℕ} [NeZero n]

/-- Prescribe any probability in [0,1], retaining an actual unitary completion. -/
theorem exists_oracle_probability (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ∃ O : Oracle n, O.phi = twoAmplitudes (Real.sqrt (1-p)) (Real.sqrt p) ∧ O.p = p := by
  let v : Mspace n := twoAmplitudes (Real.sqrt (1-p)) (Real.sqrt p)
  have hv : ‖v‖ = 1 := by
    have hn : ‖v‖ ^ 2 = 1 := by
      rw [twoAmplitudes_norm_sq,Real.sq_sqrt (sub_nonneg.mpr hp1),Real.sq_sqrt hp0]
      ring
    nlinarith [norm_nonneg v]
  obtain ⟨O,hO⟩ := exists_oracle_of_unit v hv
  refine ⟨O,hO,?_⟩
  change Rescale.mass O.phi = _
  rw [hO,twoAmplitudes_probability,Real.sq_sqrt hp0]

def lowProbability (gap : Gap) (j : ℕ) : ℝ := gap.ell / ((j : ℝ)+2)

lemma lowProbability_pos (gap : Gap) (j : ℕ) : 0 < lowProbability gap j := by
  unfold lowProbability
  exact div_pos gap.ell_pos (by positivity)

lemma lowProbability_lt_ell (gap : Gap) (j : ℕ) : lowProbability gap j < gap.ell := by
  unfold lowProbability
  apply (div_lt_iff₀ (by positivity : 0 < (j : ℝ)+2)).2
  have hmul := mul_nonneg gap.ell_nonneg (Nat.cast_nonneg (α := ℝ) j)
  nlinarith [gap.ell_pos]

lemma lowProbability_lt_one (gap : Gap) (j : ℕ) : lowProbability gap j < 1 :=
  (lowProbability_lt_ell gap j).trans (gap.ell_lt_high.trans gap.high_lt_one)

lemma lowProbability_injective (gap : Gap) : Function.Injective (lowProbability gap) := by
  intro i j h
  have hi : (i : ℝ)+2 ≠ 0 := by positivity
  have hj : (j : ℝ)+2 ≠ 0 := by positivity
  have hh := (div_eq_div_iff hi hj).1 h
  have he : (i : ℝ) = (j : ℝ) := by nlinarith [gap.ell_pos]
  exact_mod_cast he

def lowOracle (gap : Gap) (j : ℕ) : Oracle n :=
  (exists_oracle_probability (n := n) (lowProbability gap j)
    (lowProbability_pos gap j).le (lowProbability_lt_one gap j).le).choose

lemma lowOracle_probability (gap : Gap) (j : ℕ) : (lowOracle (n := n) gap j).p = lowProbability gap j :=
  (exists_oracle_probability (n := n) (lowProbability gap j)
    (lowProbability_pos gap j).le (lowProbability_lt_one gap j).le).choose_spec.2

def lowInstance (gap : Gap) (j : ℕ) : Costs.promisedFamily n gap.δ :=
  ⟨lowOracle gap j,Or.inl (by
    rw [lowOracle_probability]
    exact (lowProbability_lt_ell gap j).le)⟩

lemma lowInstance_label (gap : Gap) (j : ℕ) : Costs.label gap.δ (lowInstance (n := n) gap j) = 0 := by
  change (if (lowOracle gap j).p ≤ (1/2 : ℝ) then (0 : Fin 2) else 1) = 0
  apply if_pos
  rw [lowOracle_probability]
  have he : gap.ell < 1/2 := by unfold Gap.ell; linarith [gap.δ_pos]
  exact (lowProbability_lt_ell gap j).le.trans he.le

lemma lowInstance_phi_injective (gap : Gap) :
    Function.Injective (fun j => (lowInstance (n := n) gap j).val.phi) := by
  intro i j h
  apply lowProbability_injective gap
  rw [← lowOracle_probability (n := n) gap i,← lowOracle_probability (n := n) gap j]
  exact congrArg Rescale.mass h

/-- Distinct low instances have nonzero same-label filters. -/
theorem lowInstance_filter_ne_zero (gap : Gap) (i j : ℕ) (hij : i ≠ j) :
    1 - inner ℂ (lowInstance (n := n) gap i).val.phi (lowInstance gap j).val.phi ≠ 0 := by
  intro hz
  have hi : inner ℂ (lowInstance (n := n) gap i).val.phi (lowInstance gap j).val.phi = 1 := by
    linear_combination -hz
  have hn : ‖(lowInstance (n := n) gap i).val.phi - (lowInstance gap j).val.phi‖ ^ 2 = 0 := by
    rw [@norm_sub_sq ℂ,(lowInstance gap i).val.phi_norm,(lowInstance gap j).val.phi_norm,hi]
    norm_num
  have he := sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hn))
  exact hij (lowInstance_phi_injective gap he)

end ELV.Model
