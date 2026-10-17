import ELV.BlockRescale

/-! Exact feasible signed-Gram Fock witnesses, with a uniform norm bound. -/
noncomputable section
namespace ELV.Rescale
open ELV.Costs ELV.Model
variable {n : ℕ} [NeZero n]

def fockState (gap : Gap) (O : promisedFamily n gap.δ) : Fock.Space (2*n) :=
  Fock.eta (contracted gap O) ((contracted_norm_sq_le gap O).trans_lt gap.mu_lt_one)

def halfCoefficient : ℝ := 1 / Real.sqrt 2

lemma halfCoefficient_sq : halfCoefficient ^ 2 = (1/2 : ℝ) := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hn := (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  unfold halfCoefficient
  field_simp
  nlinarith

def forwardWitness (gap : Gap) (O : promisedFamily n gap.δ) : Fock.Space (2*n) :=
  (halfCoefficient : ℂ) • fockState gap O

def inverseWitness (gap : Gap) (O : promisedFamily n gap.δ) : Fock.Space (2*n) :=
  if label gap.δ O = 0 then forwardWitness gap O else -forwardWitness gap O

lemma forward_inner (gap : Gap) (O O' : promisedFamily n gap.δ) :
    inner ℂ (forwardWitness gap O) (forwardWitness gap O') =
      (1/2 : ℂ) * inner ℂ (fockState gap O) (fockState gap O') := by
  simp only [forwardWitness, inner_smul_left, inner_smul_right, Complex.conj_ofReal]
  have hs : (halfCoefficient : ℂ) * (halfCoefficient : ℂ) = 1/2 := by
    rw [← pow_two, ← Complex.ofReal_pow, halfCoefficient_sq]
    norm_num
  rw [← mul_assoc,hs]

lemma fockState_inner_cross (gap : Gap) (O O' : promisedFamily n gap.δ)
    (hr : label gap.δ O ≠ label gap.δ O') :
    inner ℂ (fockState gap O) (fockState gap O') = 1 / (1 - inner ℂ O.val.phi O'.val.phi) := by
  rw [fockState,fockState,Fock.eta_inner,contracted_inner_cross gap O O' hr]

lemma cross_denominator_ne (gap : Gap) (O O' : promisedFamily n gap.δ)
    (hr : label gap.δ O ≠ label gap.δ O') : 1 - inner ℂ O.val.phi O'.val.phi ≠ 0 := by
  have hc : ‖contracted gap O‖ < 1 := by
    have h := (contracted_norm_sq_le gap O).trans_lt gap.mu_lt_one
    nlinarith [norm_nonneg (contracted gap O)]
  have he : ‖contracted gap O'‖ < 1 := by
    have h := (contracted_norm_sq_le gap O').trans_lt gap.mu_lt_one
    nlinarith [norm_nonneg (contracted gap O')]
  have hh : ‖inner ℂ (contracted gap O) (contracted gap O')‖ < 1 :=
    (norm_inner_le_norm _ _).trans_lt
      ((mul_le_mul_of_nonneg_left he.le (norm_nonneg _)).trans_lt (by simpa using hc))
  rw [contracted_inner_cross gap O O' hr] at hh
  intro hz
  have hi : inner ℂ O.val.phi O'.val.phi = 1 := by linear_combination -hz
  rw [hi, norm_one] at hh
  exact (lt_irrefl 1) hh

/-- The opposite signs cancel every same-label constraint and realize every
opposite-label reciprocal kernel, for the entire uncountable promised family. -/
theorem fock_signedGram (gap : Gap) :
    AdmissibleWitness gap.δ (forwardWitness (n := n) gap) (inverseWitness gap) := by
  intro O O'
  by_cases hr : label gap.δ O = label gap.δ O'
  · have hg : inner ℂ (inverseWitness gap O) (inverseWitness gap O') =
        inner ℂ (forwardWitness gap O) (forwardWitness gap O') := by
      unfold inverseWitness
      rw [hr]
      split_ifs <;> simp
    rw [if_pos hr,hg,sub_self,mul_zero]
  · have h0 : (label gap.δ O = 0) ↔ (label gap.δ O' ≠ 0) := by omega
    have hg : inner ℂ (inverseWitness gap O) (inverseWitness gap O') =
        -inner ℂ (forwardWitness gap O) (forwardWitness gap O') := by
      unfold inverseWitness
      by_cases hx : label gap.δ O = 0
      · have hy := h0.mp hx
        simp [hx,hy]
      · have hy : label gap.δ O' = 0 := by omega
        simp [hx,hy]
    rw [if_neg hr,hg,forward_inner,fockState_inner_cross gap O O' hr]
    change 1 = (1 - inner ℂ O.val.phi O'.val.phi) * _
    field_simp [cross_denominator_ne gap O O' hr]
    <;> ring

lemma forward_norm_sq (gap : Gap) (O : promisedFamily n gap.δ) :
    ‖forwardWitness gap O‖ ^ 2 = halfCoefficient ^ 2 * ‖fockState gap O‖ ^ 2 := by
  simp [forwardWitness,norm_smul,mul_pow,Complex.norm_real]

lemma inverse_norm (gap : Gap) (O : promisedFamily n gap.δ) :
    ‖inverseWitness gap O‖ = ‖forwardWitness gap O‖ := by
  unfold inverseWitness
  split_ifs <;> simp

/-- Exact norm cost of the actual witness vectors, equation (4.11). -/
theorem fock_witness_cost (gap : Gap) (O : promisedFamily n gap.δ) :
    ‖forwardWitness gap O‖ ^ 2 + ‖inverseWitness gap O‖ ^ 2 =
      1 / (1 - ‖contracted gap O‖ ^ 2) := by
  rw [inverse_norm,forward_norm_sq,halfCoefficient_sq]
  have hn : ‖fockState gap O‖ ^ 2 = 1 / (1 - ‖contracted gap O‖ ^ 2) := Fock.eta_norm_sq _ _
  rw [hn]
  ring

theorem fock_witness_cost_le (gap : Gap) (O : promisedFamily n gap.δ) :
    ‖forwardWitness gap O‖ ^ 2 + ‖inverseWitness gap O‖ ^ 2 ≤ 1 / (1 - gap.mu) := by
  rw [fock_witness_cost]
  exact one_div_le_one_div_of_le gap.one_sub_mu_pos
    (by linarith [contracted_norm_sq_le gap O])

/-- A fixed actual admissible circuit attains the stated upper bound at every instance. -/
theorem admissible_upper_realization (gap : Gap) :
    ∃ T : Realization gap n, T.Admissible ∧
      ∀ O, T.pointwiseCost O ≤ ENNReal.ofReal (1 / (1 - gap.mu)) := by
  obtain ⟨T,hT,hcost⟩ := realize_signedGram_hilbert
    (forwardWitness (n := n) gap) (inverseWitness gap) (fock_signedGram gap)
  exact ⟨T,hT,fun O => by rw [hcost O]; exact ENNReal.ofReal_le_ofReal (fock_witness_cost_le gap O)⟩

/-- The same upper bound is achieved with separable private space. -/
theorem admissible_upper_realization_separable (gap : Gap) :
    ∃ T : Realization gap n, T.Admissible ∧
      (∀ O, T.pointwiseCost O ≤ ENNReal.ofReal (1 / (1 - gap.mu))) ∧
      TopologicalSpace.SeparableSpace T.Private := by
  obtain ⟨T,hT,hcost,hsep⟩ := realize_signedGram_separable
    (forwardWitness (n := n) gap) (inverseWitness gap) (fock_signedGram gap)
  exact ⟨T,hT,(fun O => by rw [hcost O]; exact ENNReal.ofReal_le_ofReal (fock_witness_cost_le gap O)),hsep⟩

/-- The upper bound is on the actual operational C_adm. -/
theorem admissible_upper (gap : Gap) : C_adm gap n ≤ ENNReal.ofReal (1 / (1 - gap.mu)) := by
  obtain ⟨T,hT,hcost⟩ := admissible_upper_realization (n := n) gap
  have hinf : C_adm gap n ≤ T.uniformCost := sInf_le ⟨T,hT,rfl⟩
  exact hinf.trans (iSup_le hcost)

end ELV.Rescale
