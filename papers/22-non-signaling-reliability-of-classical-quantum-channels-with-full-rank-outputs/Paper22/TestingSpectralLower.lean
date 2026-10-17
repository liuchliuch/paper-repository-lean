import Paper22.HypothesisTesting
import Paper22.DivergencePetz

/-! A classical spectral lower bound for actual quantum binary testing. -/
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Matrix
noncomputable section
namespace Paper22
variable {d : ℕ}

/-- The positive-spectrum test is an orthogonal projection. -/
theorem positiveTest_mul_self (D : Matrix (Fin d) (Fin d) ℂ) :
    positiveTest D * positiveTest D = positiveTest D := by
  have hf : ContinuousOn (fun t : ℝ => if 0 < t then (1 : ℝ) else 0) (spectrum ℝ D) :=
    D.finite_real_spectrum.continuousOn _
  unfold positiveTest
  rw [← cfc_mul _ _ D (hf := by exact hf) (hg := by exact hf)]
  apply cfc_congr
  intro t _
  dsimp only
  split_ifs <;> norm_num

theorem complex_normSq_add_le (z w : ℂ) :
    Complex.normSq (z+w) ≤ 2*Complex.normSq z+2*Complex.normSq w := by
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im]
  nlinarith [sq_nonneg (z.re-w.re),sq_nonneg (z.im-w.im)]

/-- Weighted squared row norms are a diagonal trace. -/
theorem weighted_row_normSq_trace (a : Fin d → ℝ) (X : Matrix (Fin d) (Fin d) ℂ) :
    (diagonal (fun i => (a i : ℂ))*X*Xᴴ).trace.re =
      ∑ i, ∑ j, a i*Complex.normSq (X i j) := by
  simpa only [Complex.ofReal_one, Matrix.diagonal_one, Matrix.mul_one, mul_one] using
    divergence_trace_diagonal_conjugate a (fun _ => 1) X

/-- Change from the two eigenbases to the original matrix trace. -/
theorem spectral_cross_row_trace {A : Matrix (Fin d) (Fin d) ℂ}
    (hA : A.IsHermitian) (V : Matrix (Fin d) (Fin d) ℂ) (hV : V ∈ unitary _)
    {P : Matrix (Fin d) (Fin d) ℂ} (hP : P.IsHermitian) :
    (∑ i, ∑ j, hA.eigenvalues i * Complex.normSq
      (((hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ)ᴴ*P*V) i j)) =
      (A*P*P).trace.re := by
  let U := (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ)
  let D := diagonal (fun i => (hA.eigenvalues i : ℂ))
  rw [← weighted_row_normSq_trace]
  change (D*(Uᴴ*P*V)*(Uᴴ*P*V)ᴴ).trace.re = _
  have heq : D*(Uᴴ*P*V)*(Uᴴ*P*V)ᴴ = D*Uᴴ*P*(V*Vᴴ)*P*U := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hP.eq,
      Matrix.conjTranspose_conjTranspose]
    noncomm_ring
  have hVV : V*Vᴴ=1 := unitary.mul_star_self_of_mem hV
  rw [heq,hVV,Matrix.mul_one]
  have htrace : (D*Uᴴ*P*P*U).trace = (U*D*Uᴴ*P*P).trace := by
    rw [Matrix.trace_mul_comm]
    congr 1
    noncomm_ring
  rw [htrace]
  have hspec : U*D*Uᴴ=A := hA.spectral_theorem.symm
  rw [hspec]

/-- Column-weighted version of the same change of basis. -/
theorem spectral_cross_col_trace (U : Matrix (Fin d) (Fin d) ℂ) (hU : U ∈ unitary _)
    {B : Matrix (Fin d) (Fin d) ℂ} (hB : B.IsHermitian)
    {P : Matrix (Fin d) (Fin d) ℂ} (hP : P.IsHermitian) :
    (∑ i, ∑ j, hB.eigenvalues j * Complex.normSq
      ((Uᴴ*P*(hB.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ)) i j)) =
      (B*P*P).trace.re := by
  rw [← spectral_cross_row_trace hB U hU hP,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  have heq : (Uᴴ*P*(hB.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ))ᴴ =
      (hB.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ)ᴴ*P*U := by
    simp only [Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose,hP.eq,
      Matrix.mul_assoc]
  have hentry := congrArg (fun X : Matrix (Fin d) (Fin d) ℂ => X i j) heq
  simp only [Matrix.conjTranspose_apply] at hentry
  rw [← hentry,Complex.star_def,Complex.normSq_conj]

/-- The classical binary-testing risk of the spectral overlap distributions. -/
def spectralTestingRisk {A B : Matrix (Fin d) (Fin d) ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) : ℝ :=
  ∑ i, ∑ j, min (hA.isHermitian.eigenvalues i) (hB.isHermitian.eigenvalues j) *
    Complex.normSq (((hA.isHermitian.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ)ᴴ*
      (hB.isHermitian.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ)) i j)

/-- The spectral classical risk is at most twice the quantum optimum.
The proof uses the actual Helstrom projection and squared matrix entries. -/
theorem spectralTestingRisk_le_twice_testingRisk {A B : Matrix (Fin d) (Fin d) ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    spectralTestingRisk hA hB ≤ 2*testingRisk A B := by
  let U := (hA.isHermitian.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ)
  let V := (hB.isHermitian.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ)
  let T := positiveTest (A-B)
  let P := 1-T
  have hT : T.IsHermitian := (positiveTest_isEffect _).1.posSemidef.isHermitian
  have hP : P.IsHermitian := Matrix.isHermitian_one.sub hT
  have hTT : T*T=T := positiveTest_mul_self _
  have hPP : P*P=P := by
    calc P*P = 1-T-T+T*T := by dsimp only [P]; noncomm_ring
         _ = P := by rw [hTT]; dsimp only [P]; abel
  have hsplit : Uᴴ*P*V+Uᴴ*T*V=Uᴴ*V := by
    dsimp only [P]
    noncomm_ring
  have hentry (i j : Fin d) :
      min (hA.isHermitian.eigenvalues i) (hB.isHermitian.eigenvalues j)*
        Complex.normSq ((Uᴴ*V) i j) ≤
      2*(hA.isHermitian.eigenvalues i*Complex.normSq ((Uᴴ*P*V) i j))+
      2*(hB.isHermitian.eigenvalues j*Complex.normSq ((Uᴴ*T*V) i j)) := by
    have hsum := congrArg (fun X : Matrix (Fin d) (Fin d) ℂ => X i j) hsplit
    simp only [Matrix.add_apply] at hsum
    have hab : 0 ≤ min (hA.isHermitian.eigenvalues i) (hB.isHermitian.eigenvalues j) :=
      le_min (hA.eigenvalues_nonneg i) (hB.eigenvalues_nonneg j)
    rw [← hsum]
    have hh := complex_normSq_add_le ((Uᴴ*P*V) i j) ((Uᴴ*T*V) i j)
    have h₁ := mul_le_mul_of_nonneg_left hh hab
    have h₂ := mul_le_mul_of_nonneg_right
      (min_le_left (hA.isHermitian.eigenvalues i) (hB.isHermitian.eigenvalues j))
      (Complex.normSq_nonneg ((Uᴴ*P*V) i j))
    have h₃ := mul_le_mul_of_nonneg_right
      (min_le_right (hA.isHermitian.eigenvalues i) (hB.isHermitian.eigenvalues j))
      (Complex.normSq_nonneg ((Uᴴ*T*V) i j))
    change _ ≤ _ at h₁
    nlinarith
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hentry i j))
  have hrow := spectral_cross_row_trace hA.isHermitian V hB.isHermitian.eigenvectorUnitary.2 hP
  have hcol := spectral_cross_col_trace U hA.isHermitian.eigenvectorUnitary.2 hB.isHermitian hT
  have hAPP : A*P*P=A*P := by rw [Matrix.mul_assoc,hPP]
  have hBTT : B*T*T=B*T := by rw [Matrix.mul_assoc,hTT]
  rw [hAPP] at hrow
  rw [hBTT] at hcol
  have hrhs : (∑ i, ∑ j, (2*(hA.isHermitian.eigenvalues i*Complex.normSq ((Uᴴ*P*V) i j))+
      2*(hB.isHermitian.eigenvalues j*Complex.normSq ((Uᴴ*T*V) i j)))) =
      2*((A*P).trace.re+(B*T).trace.re) := by
    simp only [Finset.sum_add_distrib,← Finset.mul_sum]
    simp only [← Finset.mul_sum] at hrow
    rw [hrow,hcol]
    ring
  rw [hrhs] at hsum
  change spectralTestingRisk hA hB ≤ _ at hsum
  have hopt := testError_positiveTest hA.nonneg hB.nonneg
  change (A*P).trace.re+(B*T).trace.re=testingRisk A B at hopt
  rwa [hopt] at hsum

end Paper22
end
