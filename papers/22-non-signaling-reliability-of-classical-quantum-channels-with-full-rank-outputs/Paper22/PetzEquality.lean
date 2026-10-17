import Paper22.TensorPowerMoment

/-! Equality in the density Petz trace bound, used to identify the unique
optimizer in the moment representation of the capacity. -/
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Matrix
noncomputable section
namespace Paper22
variable {d : ℕ}

theorem weighted_amgm_two_equality {α x y : ℝ} (hα : α ∈ Set.Ioo 0 1)
    (hx : 0 ≤ x) (hy : 0 ≤ y)
    (heq : x^α*y^(1-α)=α*x+(1-α)*y) : x=y := by
  let w : Fin 2 → ℝ := ![α,1-α]
  let z : Fin 2 → ℝ := ![x,y]
  have hw : ∀ i ∈ (Finset.univ : Finset (Fin 2)), 0 < w i := by
    intro i _
    fin_cases i
    · exact hα.1
    · change 0 < 1-α
      linarith [hα.2]
  have hw1 : ∑ i ∈ (Finset.univ : Finset (Fin 2)), w i=1 := by
    simp [w,Fin.sum_univ_two]
  have hz : ∀ i ∈ (Finset.univ : Finset (Fin 2)), 0 ≤ z i := by
    intro i _
    fin_cases i
    · exact hx
    · exact hy
  have he : (∏ i ∈ (Finset.univ : Finset (Fin 2)), z i ^ w i) = ∑ i ∈ Finset.univ, w i*z i := by
    simpa [w,z,Fin.prod_univ_two,Fin.sum_univ_two] using heq
  have hc := (Real.geom_mean_eq_arith_mean_weighted_iff' Finset.univ w z hw hw1 hz).mp he
  have h := (hc 0 (Finset.mem_univ _)).trans (hc 1 (Finset.mem_univ _)).symm
  exact h

theorem petzTrace_eq_one_iff {ρ σ : Matrix (Fin d) (Fin d) ℂ}
    (hρ : IsDensity ρ) (hσ : IsDensity σ) {α : ℝ} (hα : α ∈ Set.Ioo 0 1) :
    petzTrace α ρ σ=1 ↔ ρ=σ := by
  constructor
  · intro heq
    let U := (hρ.isHermitian.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ)
    let V := (hσ.isHermitian.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ)
    let Q := Uᴴ*V
    let a := hρ.isHermitian.eigenvalues
    let b := hσ.isHermitian.eigenvalues
    have hQ : Q ∈ unitary _ := (unitary (Matrix (Fin d) (Fin d) ℂ)).mul_mem
      (unitary.star_mem hρ.isHermitian.eigenvectorUnitary.2) hσ.isHermitian.eigenvectorUnitary.2
    have ha : ∑ i, a i=1 := by
      have h := congrArg Complex.re hρ.isHermitian.trace_eq_sum_eigenvalues
      simpa [hρ.trace_one] using h.symm
    have hb : ∑ j, b j=1 := by
      have h := congrArg Complex.re hσ.isHermitian.trace_eq_sum_eigenvalues
      simpa [hσ.trace_one] using h.symm
    let gap (i j : Fin d) :=
      (α*a i+(1-α)*b j-a i^α*b j^(1-α))*Complex.normSq (Q i j)
    have hgap (i j : Fin d) : 0 ≤ gap i j := mul_nonneg
      (sub_nonneg.mpr (Real.geom_mean_le_arith_mean2_weighted
        (w₁ := α) (w₂ := 1-α) hα.1.le (by linarith [hα.2])
        (hρ.posSemidef.eigenvalues_nonneg i) (hσ.posSemidef.eigenvalues_nonneg j) (by ring)))
      (Complex.normSq_nonneg _)
    have harith : (∑ i, ∑ j, (α*a i+(1-α)*b j)*Complex.normSq (Q i j))=1 := by
      simp_rw [add_mul,Finset.sum_add_distrib]
      have hleft : (∑ i, ∑ j, α*a i*Complex.normSq (Q i j))=α := by
        simp only [← Finset.mul_sum,divergence_unitary_row_sum Q hQ,mul_one,ha]
      have hright : (∑ i, ∑ j, (1-α)*b j*Complex.normSq (Q i j))=1-α := by
        rw [Finset.sum_comm]
        simp only [← Finset.mul_sum,divergence_unitary_col_sum Q hQ,mul_one,hb]
      rw [hleft,hright]
      ring
    have hgapSum : (∑ i, ∑ j, gap i j)=0 := by
      simp only [gap,sub_mul,Finset.sum_sub_distrib]
      simp only [sub_mul] at harith
      rw [harith]
      have hs := petzTrace_spectral_expansion hρ.posSemidef hσ.posSemidef α
      change petzTrace α ρ σ = ∑ i, ∑ j, a i^α*b j^(1-α)*Complex.normSq (Q i j) at hs
      rw [← hs,heq,sub_self]
    have hgap0 (i j : Fin d) : gap i j=0 := by
      have hout := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => hgap i j))).mp hgapSum
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hgap i j)).mp (hout i (Finset.mem_univ _)) j (Finset.mem_univ _)
    have hentry (i j : Fin d) : (a i : ℂ)*Q i j=Q i j*(b j : ℂ) := by
      by_cases hz : Q i j=0
      · simp only [hz,mul_zero,zero_mul]
      · have hnorm : Complex.normSq (Q i j) ≠ 0 := fun h => hz (Complex.normSq_eq_zero.mp h)
        have hg := hgap0 i j
        change (α*a i+(1-α)*b j-a i^α*b j^(1-α))*Complex.normSq (Q i j)=0 at hg
        have hscalar := (mul_eq_zero.mp hg).resolve_right hnorm
        have hab := weighted_amgm_two_equality hα (hρ.posSemidef.eigenvalues_nonneg i)
          (hσ.posSemidef.eigenvalues_nonneg j) (sub_eq_zero.mp hscalar).symm
        change a i=b j at hab
        rw [hab,mul_comm]
    have hD : diagonal (fun i => (a i : ℂ))*Q=Q*diagonal (fun j => (b j : ℂ)) := by
      ext i j
      simpa only [Matrix.diagonal_mul,Matrix.mul_diagonal] using hentry i j
    have hU : U*Uᴴ=1 := unitary.mul_star_self_of_mem hρ.isHermitian.eigenvectorUnitary.2
    have hV : V*Vᴴ=1 := unitary.mul_star_self_of_mem hσ.isHermitian.eigenvectorUnitary.2
    have hρspec : U*diagonal (fun i => (a i : ℂ))*Uᴴ=ρ := hρ.isHermitian.spectral_theorem.symm
    have hσspec : V*diagonal (fun j => (b j : ℂ))*Vᴴ=σ := hσ.isHermitian.spectral_theorem.symm
    have hleft : U*(diagonal (fun i => (a i : ℂ))*Q)*Vᴴ=ρ := by
      calc _ = (U*diagonal (fun i => (a i : ℂ))*Uᴴ)*(V*Vᴴ) := by dsimp only [Q]; noncomm_ring
           _ = ρ := by rw [hV,Matrix.mul_one,hρspec]
    have hright : U*(Q*diagonal (fun j => (b j : ℂ)))*Vᴴ=σ := by
      calc _ = (U*Uᴴ)*(V*diagonal (fun j => (b j : ℂ))*Vᴴ) := by dsimp only [Q]; noncomm_ring
           _ = σ := by rw [hU,Matrix.one_mul,hσspec]
    rw [hD] at hleft
    exact hleft.symm.trans hright
  · rintro rfl
    unfold petzTrace
    rw [matrix_rpow_mul_complement hρ.nonneg hα,hρ.trace_one,Complex.one_re]

/-- A positive trace stays positive under a positive reciprocal power. -/
theorem trace_rpow_inv_pos {A : Matrix (Fin d) (Fin d) ℂ}
    (hA : 0 ≤ A) (ht : 0 < A.trace.re) {α : ℝ} (hα : 0 < α) :
    0 < (CFC.rpow A (1/α)).trace.re := by
  have hY : 0 ≤ CFC.rpow A (1/α) := CFC.rpow_nonneg
  by_contra hno
  have hz : (CFC.rpow A (1/α)).trace.re=0 :=
    le_antisymm (le_of_not_gt hno) hY.posSemidef.trace_nonneg.1
  have hYzero := matrix_eq_zero_of_trace_re_eq_zero hY hz
  have hinv := matrix_rpow_inverse_exponent hA hα
  rw [hYzero,CFC.zero_rpow hα.ne'] at hinv
  rw [← hinv,Matrix.trace_zero,Complex.zero_re] at ht
  exact lt_irrefl _ ht

/-- The moment optimizer is the normalized reciprocal power, and is unique. -/
theorem petzMoment_unique_optimizer {A : Matrix (Fin d) (Fin d) ℂ}
    (hA : 0 ≤ A) (ht : 0 < A.trace.re) {α : ℝ} (hα : α ∈ Set.Ioo 0 1) :
    let Y := CFC.rpow A (1/α)
    let τ := Y.trace.re⁻¹ • Y
    IsDensity τ ∧ ∀ σ, IsDensity σ →
      ((A*CFC.rpow σ (1-α)).trace.re=Y.trace.re^α ↔ σ=τ) := by
  dsimp only
  let Y := CFC.rpow A (1/α)
  let τ := Y.trace.re⁻¹ • Y
  have hY : 0 ≤ Y := CFC.rpow_nonneg
  have hYtrace : 0 < Y.trace.re := trace_rpow_inv_pos hA ht hα.1
  have hτ : IsDensity τ := normalize_positive_matrix hY hYtrace
  have hYτ : Y=Y.trace.re • τ := by
    simp only [τ,smul_smul,mul_inv_cancel₀ hYtrace.ne',one_smul]
  have hAτ : A=Y.trace.re^α • CFC.rpow τ α := by
    calc A = CFC.rpow Y α := (matrix_rpow_inverse_exponent hA hα.1).symm
         _ = CFC.rpow (Y.trace.re • τ) α := congrArg (fun Z => CFC.rpow Z α) hYτ
         _ = _ := matrix_rpow_smul hτ.nonneg hYtrace.le hα.1.le
  refine ⟨hτ,?_⟩
  intro σ hσ
  have htrace : (A*CFC.rpow σ (1-α)).trace.re=Y.trace.re^α*petzTrace α τ σ := by
    rw [hAτ,Matrix.smul_mul,Matrix.trace_smul,Complex.smul_re,smul_eq_mul]
    rfl
  change (A*CFC.rpow σ (1-α)).trace.re=Y.trace.re^α ↔ σ=τ
  rw [htrace]
  constructor
  · intro heq
    have he : petzTrace α τ σ=1 := by
      apply mul_left_cancel₀ (Real.rpow_pos_of_pos hYtrace α).ne'
      simpa only [mul_one] using heq
    exact ((petzTrace_eq_one_iff hτ hσ hα).mp he).symm
  · rintro rfl
    rw [(petzTrace_eq_one_iff hτ hτ hα).mpr rfl,mul_one]

/-- Every probability mixture of positive density powers has positive trace. -/
theorem petzPowerMixture_trace_pos {n : ℕ} (V : CQChannel n d) {q : Fin n → ℝ}
    (hq0 : ∀ x, 0 ≤ q x) (hq1 : ∑ x, q x=1) {α : ℝ} (hα : 0 < α) :
    0 < (petzPowerMixture V q α).trace.re := by
  have hex : ∃ x, 0 < q x := by
    by_contra hno
    push_neg at hno
    have hsum : (∑ x, q x) ≤ 0 := Finset.sum_nonpos (fun x _ => hno x)
    linarith
  obtain ⟨x,hx⟩ := hex
  simp only [petzPowerMixture,Matrix.trace_sum,Complex.re_sum,Matrix.trace_smul,
    Complex.smul_re,smul_eq_mul]
  exact (Finset.single_le_sum (fun y _ => mul_nonneg (hq0 y)
    (density_trace_rpow_pos (V.isDensity y) hα).le) (Finset.mem_univ x)).trans_lt'
    (mul_pos hx (density_trace_rpow_pos (V.isDensity x) hα))

end Paper22
end
