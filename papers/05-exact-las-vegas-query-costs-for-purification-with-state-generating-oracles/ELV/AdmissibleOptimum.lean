import ELV.BoundaryOracle

/-! The exact operational restricted optimum: Theorem 1.1, equation (1.2).
The lower bound uses legal boundary oracles and actual executed circuit costs. -/
noncomputable section
namespace ELV.Costs
open ELV.Model
variable {n : ℕ} [NeZero n]

/-- The boundary pair forces at least one witness cost to reach the target. -/
theorem signedGram_boundary_lower (gap : Gap) {K : Type*} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] (f g : promisedFamily n gap.δ → K)
    (hf : AdmissibleWitness gap.δ f g) :
    ∃ O, 1 / (1 - gap.mu) ≤ ‖f O‖ ^ 2 + ‖g O‖ ^ 2 := by
  obtain ⟨Om,Op,hrm,hrp,hoverlap⟩ := boundary_pair (n := n) gap
  have hh := hf Om Op
  change (if label gap.δ Om = label gap.δ Op then (0 : ℂ) else 1) =
    (1 - inner ℂ Om.val.phi Op.val.phi) *
      (inner ℂ (f Om) (f Op) - inner ℂ (g Om) (g Op)) at hh
  rw [hrm,hrp,hoverlap] at hh
  rw [if_neg (show (0 : Fin 2) ≠ 1 by decide)] at hh
  have hn : ‖inner ℂ (f Om) (f Op) - inner ℂ (g Om) (g Op)‖ = 1 / (1 - gap.mu) := by
    have hnorm := congrArg norm hh
    have hreal : ‖(1 : ℂ) - (gap.mu : ℂ)‖ = 1 - gap.mu := by
      rw [← Complex.ofReal_one,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,abs_of_pos gap.one_sub_mu_pos]
    rw [norm_one,norm_mul,hreal] at hnorm
    apply (eq_div_iff gap.one_sub_mu_ne_zero).2
    nlinarith
  have hcs := SignedGram.cs_lower (f Om) (g Om) (f Op) (g Op)
  rw [hn] at hcs
  have ha : 0 < 1 / (1 - gap.mu) := one_div_pos.mpr gap.one_sub_mu_pos
  by_cases hm : 1 / (1 - gap.mu) ≤ ‖f Om‖ ^ 2 + ‖g Om‖ ^ 2
  · exact ⟨Om,hm⟩
  · refine ⟨Op,?_⟩
    by_contra hp
    have hm' := lt_of_not_ge hm
    have hp' := lt_of_not_ge hp
    have hprod : (‖f Om‖ ^ 2 + ‖g Om‖ ^ 2) * (‖f Op‖ ^ 2 + ‖g Op‖ ^ 2) <
        (1 / (1 - gap.mu)) ^ 2 := by
      calc
        _ ≤ (1 / (1 - gap.mu)) * (‖f Op‖ ^ 2 + ‖g Op‖ ^ 2) :=
          mul_le_mul_of_nonneg_right hm'.le (by positivity)
        _ < (1 / (1 - gap.mu)) * (1 / (1 - gap.mu)) := mul_lt_mul_of_pos_left hp' ha
        _ = _ := by ring
    exact (not_lt_of_ge hcs) hprod

/-- Every actual admissible transducer has uniform cost at least the target. -/
theorem admissible_realization_lower (gap : Gap) (T : Realization gap n) (hT : T.Admissible) :
    ENNReal.ofReal (1 / (1 - gap.mu)) ≤ T.uniformCost := by
  obtain ⟨f,g,hfg,hcost⟩ := extract_signedGram T hT
  obtain ⟨O,hO⟩ := signedGram_boundary_lower gap f g hfg
  apply le_iSup_of_le O
  rw [hcost O]
  exact ENNReal.ofReal_le_ofReal hO

/-- The lower bound applies to the actual operational infimum. -/
theorem admissible_lower (gap : Gap) :
    ENNReal.ofReal (1 / (1 - gap.mu)) ≤ C_adm gap n := by
  apply le_sInf
  rintro c ⟨T,hT,rfl⟩
  exact admissible_realization_lower gap T hT

/-- The restricted minimax equality (1.2), with no feasibility or unitary
existence conclusion smuggled into the hypotheses. -/
theorem admissible_optimum (gap : Gap) :
    C_adm gap n = ENNReal.ofReal (1 / (1 - gap.mu)) :=
  le_antisymm (Rescale.admissible_upper gap) (admissible_lower gap)

/-- The infimum is achieved by one actual fixed admissible finite circuit. -/
theorem admissible_attained (gap : Gap) :
    ∃ T : Realization gap n, T.Admissible ∧ T.uniformCost = C_adm gap n := by
  obtain ⟨T,hT,hcost⟩ := Rescale.admissible_upper_realization (n := n) gap
  refine ⟨T,hT,?_⟩
  rw [admissible_optimum]
  exact le_antisymm (iSup_le hcost) (admissible_realization_lower gap T hT)

/-- The restricted infimum is attained with separable private space, as in Theorem 1.1. -/
theorem admissible_attained_separable (gap : Gap) :
    ∃ T : Realization gap n, T.Admissible ∧ T.uniformCost = C_adm gap n ∧
      TopologicalSpace.SeparableSpace T.Private := by
  obtain ⟨T,hT,hcost,hsep⟩ := Rescale.admissible_upper_realization_separable (n := n) gap
  refine ⟨T,hT,?_,hsep⟩
  rw [admissible_optimum]
  exact le_antisymm (iSup_le hcost) (admissible_realization_lower gap T hT)

/-- Both printed closed forms in (1.2) for the actual operational value. -/
theorem admissible_optimum_forms (gap : Gap) :
    C_adm gap n = ENNReal.ofReal (1 / (1 - Real.sqrt (1 - 4 * gap.δ ^ 2))) ∧
    C_adm gap n = ENNReal.ofReal ((1 + gap.mu) / (4 * gap.δ ^ 2)) := by
  constructor
  · exact admissible_optimum gap
  · rw [admissible_optimum]
    congr 1
    exact Cost.admValue_eq_alt gap

end ELV.Costs
