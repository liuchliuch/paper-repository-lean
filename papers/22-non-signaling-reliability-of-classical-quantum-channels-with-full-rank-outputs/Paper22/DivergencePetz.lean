import Paper22.DivergenceExtended
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! # The Petz trace inequality and the zero-order limit -/
open scoped MatrixOrder ComplexOrder
open Matrix
noncomputable section
namespace Paper22
variable {n d : ℕ}

lemma divergence_trace_diagonal_conjugate (a b : Fin d → ℝ)
    (U : Matrix (Fin d) (Fin d) ℂ) :
    (diagonal (fun i => (a i : ℂ)) * U * diagonal (fun j => (b j : ℂ)) * Uᴴ).trace.re
      = ∑ i, ∑ j, a i * b j * Complex.normSq (U i j) := by
  classical
  change (∑ i, ∑ j, (diagonal (fun i => (a i : ℂ)) * U *
    diagonal (fun j => (b j : ℂ))) i j * Uᴴ j i).re = _
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply,
    Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have heq : (a i : ℂ) * U i j * (b j : ℂ) * star (U i j) =
      (a i : ℂ) * (b j : ℂ) * (U i j * star (U i j)) := by ring
  rw [heq]
  simp [Complex.mul_conj]

lemma divergence_unitary_row_sum (U : Matrix (Fin d) (Fin d) ℂ)
    (hU : U ∈ unitary _) (i : Fin d) : ∑ j, Complex.normSq (U i j) = 1 := by
  have h := congrArg (fun A : Matrix (Fin d) (Fin d) ℂ => (A i i).re)
    (unitary.mul_star_self_of_mem hU)
  simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.mul_conj] using h

lemma divergence_unitary_col_sum (U : Matrix (Fin d) (Fin d) ℂ)
    (hU : U ∈ unitary _) (j : Fin d) : ∑ i, Complex.normSq (U i j) = 1 := by
  have h := congrArg (fun A : Matrix (Fin d) (Fin d) ℂ => (A j j).re)
    (unitary.star_mul_self_of_mem hU)
  simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.mul_conj, mul_comm] using h

lemma divergence_rpow_eq_spectral {ρ : Matrix (Fin d) (Fin d) ℂ}
    (hρ : ρ.PosSemidef) (α : ℝ) :
    CFC.rpow ρ α =
      (hρ.isHermitian.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) *
        diagonal (fun i => ((hρ.isHermitian.eigenvalues i ^ α : ℝ) : ℂ)) *
        (hρ.isHermitian.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ)ᴴ := by
  rw [CFC.rpow, cfc_nnreal_eq_real (fun x => x ^ α) ρ hρ.nonneg,
    cfc_eq_spectral hρ.isHermitian]
  congr 2
  apply congrArg Matrix.diagonal
  funext i
  simp only [Function.comp_apply, NNReal.coe_rpow,
    Real.coe_toNNReal _ (hρ.eigenvalues_nonneg i)]
  rfl

lemma petzTrace_spectral_expansion {ρ σ : Matrix (Fin d) (Fin d) ℂ}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (α : ℝ) :
    petzTrace α ρ σ = ∑ i, ∑ j,
      hρ.isHermitian.eigenvalues i ^ α * hσ.isHermitian.eigenvalues j ^ (1 - α) *
      Complex.normSq (((hρ.isHermitian.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ)ᴴ *
        (hσ.isHermitian.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ)) i j) := by
  let U := (hρ.isHermitian.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ)
  let V := (hσ.isHermitian.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ)
  let A := diagonal (fun i => ((hρ.isHermitian.eigenvalues i ^ α : ℝ) : ℂ))
  let B := diagonal (fun j => ((hσ.isHermitian.eigenvalues j ^ (1 - α) : ℝ) : ℂ))
  have ht : (U * A * Uᴴ * (V * B * Vᴴ)).trace =
      (A * (Uᴴ * V) * B * (Uᴴ * V)ᴴ).trace := by
    calc (U * A * Uᴴ * (V * B * Vᴴ)).trace
        = (U * (A * Uᴴ * V * B * Vᴴ)).trace := by simp only [Matrix.mul_assoc]
      _ = ((A * Uᴴ * V * B * Vᴴ) * U).trace := Matrix.trace_mul_comm _ _
      _ = (A * (Uᴴ * V) * B * (Uᴴ * V)ᴴ).trace := by
        simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  unfold petzTrace
  rw [divergence_rpow_eq_spectral hρ, divergence_rpow_eq_spectral hσ]
  change (U * A * Uᴴ * (V * B * Vᴴ)).trace.re = _
  rw [ht, divergence_trace_diagonal_conjugate]

/-- The finite-dimensional Petz trace inequality, proved by spectral expansion
and scalar weighted arithmetic-geometric mean. -/
theorem petzTrace_le_one {ρ σ : Matrix (Fin d) (Fin d) ℂ}
    (hρ : IsDensity ρ) (hσ : IsDensity σ) {α : ℝ} (hα : α ∈ Set.Ioo 0 1) :
    petzTrace α ρ σ ≤ 1 := by
  classical
  let U := (hρ.isHermitian.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ)ᴴ *
    (hσ.isHermitian.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ)
  have hU : U ∈ unitary _ := (unitary (Matrix (Fin d) (Fin d) ℂ)).mul_mem
    (unitary.star_mem hρ.isHermitian.eigenvectorUnitary.2)
    hσ.isHermitian.eigenvectorUnitary.2
  have hρsum : ∑ i, hρ.isHermitian.eigenvalues i = 1 := by
    have h := congrArg Complex.re hρ.isHermitian.trace_eq_sum_eigenvalues
    simpa [hρ.trace_one] using h.symm
  have hσsum : ∑ j, hσ.isHermitian.eigenvalues j = 1 := by
    have h := congrArg Complex.re hσ.isHermitian.trace_eq_sum_eigenvalues
    simpa [hσ.trace_one] using h.symm
  rw [petzTrace_spectral_expansion hρ.posSemidef hσ.posSemidef]
  change (∑ i, ∑ j, hρ.isHermitian.eigenvalues i ^ α *
    hσ.isHermitian.eigenvalues j ^ (1 - α) * Complex.normSq (U i j)) ≤ 1
  calc (∑ i, ∑ j, hρ.isHermitian.eigenvalues i ^ α *
        hσ.isHermitian.eigenvalues j ^ (1 - α) * Complex.normSq (U i j))
      ≤ ∑ i, ∑ j, (α * hρ.isHermitian.eigenvalues i +
        (1 - α) * hσ.isHermitian.eigenvalues j) * Complex.normSq (U i j) := by
          apply Finset.sum_le_sum
          intro i _
          apply Finset.sum_le_sum
          intro j _
          exact mul_le_mul_of_nonneg_right (Real.geom_mean_le_arith_mean2_weighted
            hα.1.le (by linarith [hα.2]) (hρ.posSemidef.eigenvalues_nonneg i)
            (hσ.posSemidef.eigenvalues_nonneg j) (by ring)) (Complex.normSq_nonneg _)
    _ = α * ∑ i, hρ.isHermitian.eigenvalues i +
        (1 - α) * ∑ j, hσ.isHermitian.eigenvalues j := by
      simp_rw [add_mul, Finset.sum_add_distrib]
      congr 1
      · simp only [← Finset.mul_sum, divergence_unitary_row_sum U hU, mul_one]
      · rw [Finset.sum_comm]
        simp only [← Finset.mul_sum, divergence_unitary_col_sum U hU, mul_one]
    _ = 1 := by rw [hρsum, hσsum]; ring

lemma petzRenyiRe_nonneg {ρ σ : Matrix (Fin d) (Fin d) ℂ}
    (hρ : IsDensity ρ) (hσ : IsDensity σ) {α : ℝ} (hα : α ∈ Set.Ioo 0 1) :
    0 ≤ petzRenyiRe α ρ σ := by
  exact mul_nonneg_of_nonpos_of_nonpos
    (one_div_nonpos.mpr (sub_nonpos.mpr hα.2.le))
    (log2_nonpos (petzTrace_nonneg α) (petzTrace_le_one hρ hσ hα))

/-- Nonnegativity of the actual extended-real Petz divergence, including
orthogonal supports (where it is positive infinity). -/
theorem petzRenyi_nonneg {ρ σ : Matrix (Fin d) (Fin d) ℂ}
    (hρ : IsDensity ρ) (hσ : IsDensity σ) (α : ℝ) : 0 ≤ petzRenyi α ρ σ := by
  unfold petzRenyi
  split_ifs with hα ht
  · exact EReal.coe_nonneg.mpr (petzRenyiRe_nonneg hρ hσ hα)
  · exact le_top
  · exact le_refl 0

lemma orderAlphaInf_nonneg [NeZero d] (V : CQChannel n d)
    {α : ℝ} (hα : α ∈ Set.Ioo 0 1) {q : Fin n → ℝ} (hq : ∀ x, 0 ≤ q x) :
    0 ≤ orderAlphaInf α V q := by
  apply le_csInf (orderAlpha_values_nonempty V α q)
  rintro t ⟨σ, hσ, rfl⟩
  exact Finset.sum_nonneg fun x _ => mul_nonneg (hq x)
    (petzRenyiRe_nonneg (V.isDensity x) hσ hα)

lemma orderAlphaCapacity_nonneg [NeZero d] (V : CQChannel n d)
    {α : ℝ} (hα : α ∈ Set.Ioo 0 1) : 0 ≤ orderAlphaCapacity V α := by
  apply Real.sSup_nonneg
  rintro t ⟨q, hq0, hq1, rfl⟩
  exact orderAlphaInf_nonneg V hα hq0

/-- The additional assertion in S3.p2: for full-rank outputs, the order-alpha
capacity tends to zero as alpha decreases to zero. -/
theorem orderAlphaCapacity_tendsto_zero [NeZero n] [NeZero d]
    (V : CQChannel n d) (hV : V.FullRank) :
    Filter.Tendsto (orderAlphaCapacity V)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  obtain ⟨lam, hlam0, hlam⟩ := V.exists_uniform_spectral_lower_bound hV
  have hpos : ∀ᶠ α : ℝ in nhdsWithin 0 (Set.Ioi 0), 0 < α := self_mem_nhdsWithin
  have hlt : ∀ᶠ α : ℝ in nhdsWithin 0 (Set.Ioi 0), α < 1 :=
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds
  have hc : ContinuousAt (fun α : ℝ => -α / (1 - α) * log2 ((d : ℝ) * lam)) 0 := by
    exact (continuousAt_id.neg.div (continuousAt_const.sub continuousAt_id)
      (by norm_num)).mul continuousAt_const
  have hu : Filter.Tendsto (fun α : ℝ => -α / (1 - α) * log2 ((d : ℝ) * lam))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  apply squeeze_zero' _ _ hu
  · filter_upwards [hpos, hlt] with α hα0 hα1
    exact orderAlphaCapacity_nonneg V ⟨hα0, hα1⟩
  · filter_upwards [hpos, hlt] with α hα0 hα1
    exact orderAlphaCapacity_le V (NeZero.pos d) hV hlam hlam0 hα0 hα1

/-- The zero-order limit for the source's extended-real capacity. -/
theorem orderAlphaCapacityExtended_tendsto_zero [NeZero n] [NeZero d]
    (V : CQChannel n d) (hV : V.FullRank) :
    Filter.Tendsto (orderAlphaCapacityExtended V)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hu := continuous_coe_real_ereal.continuousAt.tendsto.comp
    (orderAlphaCapacity_tendsto_zero V hV)
  have heq : ∀ᶠ α : ℝ in nhdsWithin 0 (Set.Ioi 0),
      (orderAlphaCapacity V α : EReal) = orderAlphaCapacityExtended V α := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds]
      with α hα0 hα1
    exact (orderAlphaCapacityExtended_eq_coe V hV ⟨hα0, hα1⟩).symm
  simpa using hu.congr' heq

end Paper22
end
