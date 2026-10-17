import Paper25.OneCleanQubit
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.Spectrum
import Mathlib.Tactic

/-!
# Gate synthesis error in the actual one-clean-qubit semantics

All matrix norms in this file are Euclidean operator norms, using Mathlib's
`Matrix.Norms.L2Operator` scoped instances. Gate-product errors telescope in
this norm. A PSD density matrix of trace one is expanded in its nonnegative
spectral weights to prove the Born probability perturbation bound. The final
corollaries apply to `OneCleanQubit.evolve`, `probZero`, and the actual
one-clean-qubit input density.
-/

noncomputable section
open scoped ComplexOrder ComplexConjugate InnerProductSpace Matrix.Norms.L2Operator
open Matrix Finset

namespace Paper25.Synthesis
open OneCleanQubit

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A legal unitary has Euclidean operator norm at most one, including empty
index types. This is derived from its actual matrix inverse identity. -/
lemma unitary_opNorm_le {U : Matrix ι ι ℂ} (hU : Unitary U) : ‖U‖ ≤ 1 := by
  have hs := Matrix.l2_opNorm_conjTranspose_mul_self U
  rw [hU.1] at hs
  have h1 : ‖(1 : Matrix ι ι ℂ)‖ ≤ 1 := by
    rw [Matrix.cstar_norm_def, map_one]
    exact ContinuousLinearMap.norm_id_le
  nlinarith [norm_nonneg U]

/-- Chronological gate product: the latest gate acts on the left. -/
def gateProduct (G : ℕ → Matrix ι ι ℂ) : ℕ → Matrix ι ι ℂ
  | 0 => 1
  | N+1 => G N * gateProduct G N

lemma gateProduct_unitary (G : ℕ → Matrix ι ι ℂ) (N : ℕ)
    (hG : ∀ k < N, Unitary (G k)) : Unitary (gateProduct G N) := by
  induction N with
  | zero => simp [gateProduct, Unitary]
  | succ N ih =>
    exact unitary_mul (hG N (by omega)) (ih (fun k hk => hG k (by omega)))

/-- Telescoping error of two actual unitary gate sequences. -/
theorem gateProduct_error (G H : ℕ → Matrix ι ι ℂ) (N : ℕ)
    (hG : ∀ k < N, Unitary (G k)) (hH : ∀ k < N, Unitary (H k)) :
    ‖gateProduct G N-gateProduct H N‖ ≤ ∑ k ∈ range N, ‖G k-H k‖ := by
  induction N with
  | zero => simp [gateProduct]
  | succ N ih =>
    have hGN := unitary_opNorm_le (hG N (by omega))
    have hHN := unitary_opNorm_le (gateProduct_unitary H N (fun k hk => hH k (by omega)))
    have hp := ih (fun k hk => hG k (by omega)) (fun k hk => hH k (by omega))
    have hdiff : gateProduct G (N+1)-gateProduct H (N+1) =
        G N*(gateProduct G N-gateProduct H N)+(G N-H N)*gateProduct H N := by
      simp only [gateProduct]
      noncomm_ring
    rw [hdiff, sum_range_succ]
    calc
      _ ≤ ‖G N*(gateProduct G N-gateProduct H N)‖+
          ‖(G N-H N)*gateProduct H N‖ := norm_add_le _ _
      _ ≤ ‖G N‖*‖gateProduct G N-gateProduct H N‖+
          ‖G N-H N‖*‖gateProduct H N‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ ≤ ‖gateProduct G N-gateProduct H N‖+‖G N-H N‖ := by
        apply add_le_add
        · simpa only [one_mul] using mul_le_mul_of_nonneg_right hGN
            (norm_nonneg (gateProduct G N-gateProduct H N))
        · simpa only [mul_one] using mul_le_mul_of_nonneg_left hHN (norm_nonneg (G N-H N))
      _ ≤ _ := add_le_add_right hp _

/-- Uniform per-gate precision `ξ/N` gives error at most `ξ` for the complete
unitary, with no assumptions about a measurement probability. -/
theorem gateProduct_error_uniform (G H : ℕ → Matrix ι ι ℂ) (N : ℕ) (hN : 0 < N)
    (ξ : ℝ) (hG : ∀ k < N, Unitary (G k)) (hH : ∀ k < N, Unitary (H k))
    (hgate : ∀ k < N, ‖G k-H k‖ ≤ ξ/(N : ℝ)) :
    ‖gateProduct G N-gateProduct H N‖ ≤ ξ := by
  calc
    _ ≤ ∑ k ∈ range N, ‖G k-H k‖ := gateProduct_error G H N hG hH
    _ ≤ ∑ _k ∈ range N, ξ/(N : ℝ) :=
      sum_le_sum (fun k hk => hgate k (mem_range.mp hk))
    _ = ξ := by
      simp only [sum_const, card_range, nsmul_eq_mul]
      have hNne : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
      field_simp [hNne]

/-- A Hermitian idempotent effect is an operator-norm contraction. -/
lemma projector_opNorm_le (E : Matrix ι ι ℂ) (hE : E.IsHermitian) (hEE : E*E=E) :
    ‖E‖ ≤ 1 := by
  have h := Matrix.l2_opNorm_conjTranspose_mul_self E
  rw [hE.eq, hEE] at h
  nlinarith [norm_nonneg E]

/-- A diagonal entry in an orthonormal eigenbasis is an expectation of a unit
vector, hence is bounded by the Euclidean operator norm. -/
lemma eigenbasis_diag_bound (A ρ : Matrix ι ι ℂ) (hρ : ρ.IsHermitian) (i : ι) :
    ‖((hρ.eigenvectorUnitary : Matrix ι ι ℂ).conjTranspose * A *
      (hρ.eigenvectorUnitary : Matrix ι ι ℂ)) i i‖ ≤ ‖A‖ := by
  let b := hρ.eigenvectorBasis
  let U : Matrix ι ι ℂ := hρ.eigenvectorUnitary
  have he : (U.conjTranspose*A*U) i i =
      ⟪b i, Matrix.toEuclideanCLM (n:=ι) (𝕜:=ℂ) A (b i)⟫_ℂ := by
    rw [Matrix.mul_assoc]
    change dotProduct (star (fun j => U j i)) (A *ᵥ (fun j => U j i)) =
      dotProduct (A *ᵥ ⇑(b i)) (star ⇑(b i))
    rw [dotProduct_comm]
    rfl
  change ‖(U.conjTranspose*A*U) i i‖ ≤ _
  rw [he]
  have hb : ‖b i‖=1 := b.norm_eq_one i
  have hop := (Matrix.toEuclideanCLM (n:=ι) (𝕜:=ℂ) A).le_opNorm (b i)
  rw [hb, mul_one, ← Matrix.cstar_norm_def] at hop
  exact (norm_inner_le_norm (b i) (Matrix.toEuclideanCLM (n:=ι) (𝕜:=ℂ) A (b i))).trans (by simpa [hb] using hop)

/-- Density matrices pair against an arbitrary observable with magnitude at
most its operator norm. PSD and trace one are the only state hypotheses. -/
theorem norm_trace_mul_density_le (A ρ : Matrix ι ι ℂ)
    (hρ : ρ.PosSemidef) (htrace : Matrix.trace ρ=1) :
    ‖Matrix.trace (A*ρ)‖ ≤ ‖A‖ := by
  let h := hρ.isHermitian
  let U : Matrix ι ι ℂ := h.eigenvectorUnitary
  let D : Matrix ι ι ℂ := Matrix.diagonal (fun i => (h.eigenvalues i : ℂ))
  have hspec : ρ=U*D*U.conjTranspose := h.spectral_theorem
  have htraceform : Matrix.trace (A*ρ) =
      ∑ i : ι, (U.conjTranspose*A*U) i i * (h.eigenvalues i : ℂ) := by
    calc
      Matrix.trace (A*ρ) = Matrix.trace (A*(U*D*U.conjTranspose)) :=
        congrArg (fun R => Matrix.trace (A*R)) hspec
      _ = Matrix.trace ((A*U*D)*U.conjTranspose) := by congr 1; simp only [Matrix.mul_assoc]
      _ = Matrix.trace (U.conjTranspose*(A*U*D)) := Matrix.trace_mul_comm _ _
      _ = Matrix.trace ((U.conjTranspose*A*U)*D) := by congr 1; simp only [Matrix.mul_assoc]
      _ = _ := by simp [Matrix.trace, D, Matrix.mul_diagonal]
  have hsum : (∑ i : ι, h.eigenvalues i)=1 := by
    have ht := congrArg Complex.re (h.trace_eq_sum_eigenvalues.symm.trans htrace)
    simpa using ht
  rw [htraceform]
  calc
    _ ≤ ∑ i : ι, ‖(U.conjTranspose*A*U) i i * (h.eigenvalues i : ℂ)‖ := norm_sum_le _ _
    _ = ∑ i : ι, ‖(U.conjTranspose*A*U) i i‖ * h.eigenvalues i := by
      apply sum_congr rfl
      intro i _
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hρ.eigenvalues_nonneg i)]
    _ ≤ ∑ i : ι, ‖A‖*h.eigenvalues i := sum_le_sum (fun i _ =>
      mul_le_mul_of_nonneg_right (eigenbasis_diag_bound A ρ h i) (hρ.eigenvalues_nonneg i))
    _ = ‖A‖ := by rw [← mul_sum, hsum, mul_one]

/-- Heisenberg observables for nearby unitaries differ by at most twice their
unitary error, for any effect of operator norm at most one. -/
theorem conjugated_effect_error (U V E : Matrix ι ι ℂ)
    (hU : Unitary U) (hV : Unitary V) (hE : ‖E‖ ≤ 1) :
    ‖U.conjTranspose*E*U-V.conjTranspose*E*V‖ ≤ 2*‖U-V‖ := by
  have hdiff : U.conjTranspose*E*U-V.conjTranspose*E*V =
      (U-V).conjTranspose*E*U+V.conjTranspose*E*(U-V) := by
    rw [Matrix.conjTranspose_sub]
    noncomm_ring
  rw [hdiff]
  calc
    _ ≤ ‖(U-V).conjTranspose*E*U‖+‖V.conjTranspose*E*(U-V)‖ := norm_add_le _ _
    _ ≤ (‖(U-V).conjTranspose‖*‖E‖)*‖U‖+(‖V.conjTranspose‖*‖E‖)*‖U-V‖ :=
      add_le_add ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
        (norm_mul_le _ _) (norm_nonneg U)))
        ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
        (norm_mul_le _ _) (norm_nonneg (U-V))))
    _ ≤ (‖U-V‖*1)*1+(1*1)*‖U-V‖ := by
      rw [Matrix.l2_opNorm_conjTranspose, Matrix.l2_opNorm_conjTranspose]
      gcongr
      · exact unitary_opNorm_le hU
      · exact unitary_opNorm_le hV
    _ = _ := by ring

lemma trace_effect_evolve (E U ρ : Matrix ι ι ℂ) :
    Matrix.trace (E*evolve U ρ) = Matrix.trace ((U.conjTranspose*E*U)*ρ) := by
  unfold evolve
  calc
    _ = Matrix.trace ((E*U*ρ)*U.conjTranspose) := by congr 1; simp only [Matrix.mul_assoc]
    _ = Matrix.trace (U.conjTranspose*(E*U*ρ)) := Matrix.trace_mul_comm _ _
    _ = _ := by congr 1; simp only [Matrix.mul_assoc]

/-- Born probability perturbation for an arbitrary density matrix and a
contractive effect, proved from actual unitary conjugation. -/
theorem born_probability_error (U V E ρ : Matrix ι ι ℂ)
    (hU : Unitary U) (hV : Unitary V) (hE : ‖E‖≤1)
    (hρ : ρ.PosSemidef) (htrace : Matrix.trace ρ=1) :
    |(Matrix.trace (E*evolve U ρ)).re-(Matrix.trace (E*evolve V ρ)).re| ≤ 2*‖U-V‖ := by
  rw [trace_effect_evolve, trace_effect_evolve, ← Complex.sub_re, ← Matrix.trace_sub,
    ← Matrix.sub_mul]
  exact (Complex.abs_re_le_norm _).trans
    ((norm_trace_mul_density_le _ ρ hρ htrace).trans (conjugated_effect_error U V E hU hV hE))

variable {n : Type*} [Fintype n] [DecidableEq n]

lemma zeroEffect_opNorm_le : ‖(zeroEffect : ProbeMatrix n)‖ ≤ 1 := by
  apply projector_opNorm_le
  · simp [zeroEffect, Matrix.fromBlocks_conjTranspose, Matrix.IsHermitian]
  · simp [zeroEffect, Matrix.fromBlocks_multiply]

/-- The operational `probZero` measurement satisfies the same error bound on
every legal density state. -/
theorem probZero_evolve_error (U V ρ : ProbeMatrix n)
    (hU : Unitary U) (hV : Unitary V) (hρ : ρ.PosSemidef) (htrace : Matrix.trace ρ=1) :
    |probZero (evolve U ρ)-probZero (evolve V ρ)| ≤ 2*‖U-V‖ := by
  rw [probZero_born, probZero_born]
  exact born_probability_error U V zeroEffect ρ hU hV zeroEffect_opNorm_le hρ htrace

/-- Synthesis changes the actual acceptance probability by at most `2ξ` when
every one of the `N` unitary gates is approximated within `ξ/N`. -/
theorem gate_synthesis_probability_budget [Nonempty n]
    (G H : ℕ → ProbeMatrix n) (N : ℕ) (hN : 0<N) (ξ : ℝ)
    (hG : ∀ k<N, Unitary (G k)) (hH : ∀ k<N, Unitary (H k))
    (hgate : ∀ k<N, ‖G k-H k‖ ≤ ξ/(N : ℝ)) :
    |probZero (evolve (gateProduct G N) input)-
      probZero (evolve (gateProduct H N) input)| ≤ 2*ξ := by
  exact (probZero_evolve_error _ _ _ (gateProduct_unitary G N hG)
    (gateProduct_unitary H N hH) input_posSemidef input_trace).trans
      (mul_le_mul_of_nonneg_left (gateProduct_error_uniform G H N hN ξ hG hH hgate) (by norm_num))

/-- A signed probability gap of size `γ` survives synthesis at a remaining
gap of at least `γ/2` whenever `2ξ≤γ/2`. -/
theorem synthesized_signed_gap [Nonempty n]
    (G H : ℕ → ProbeMatrix n) (N : ℕ) (hN : 0<N) (ξ γ : ℝ)
    (hG : ∀ k<N, Unitary (G k)) (hH : ∀ k<N, Unitary (H k))
    (hgate : ∀ k<N, ‖G k-H k‖ ≤ ξ/(N : ℝ)) (hbudget : 2*ξ≤γ/2) :
    ((1/2:ℝ)+γ ≤ probZero (evolve (gateProduct G N) input) →
      (1/2:ℝ)+γ/2 ≤ probZero (evolve (gateProduct H N) input)) ∧
    (probZero (evolve (gateProduct G N) input) ≤ (1/2:ℝ)-γ →
      probZero (evolve (gateProduct H N) input) ≤ (1/2:ℝ)-γ/2) := by
  have he := gate_synthesis_probability_budget G H N hN ξ hG hH hgate
  have he' := abs_le.mp he
  constructor <;> intro h <;> linarith

/-- The paper's stricter synthesis budget `2ξ≤γ/4` in the same actual
probability semantics; both signs retain a gap of `γ/2`. -/
theorem synthesized_original_gap [Nonempty n]
    (G H : ℕ → ProbeMatrix n) (N : ℕ) (hN : 0<N) (ξ γ : ℝ) (hγ : 0≤γ)
    (hG : ∀ k<N, Unitary (G k)) (hH : ∀ k<N, Unitary (H k))
    (hgate : ∀ k<N, ‖G k-H k‖ ≤ ξ/(N : ℝ)) (hbudget : 2*ξ≤γ/4) :
    ((1/2:ℝ)+γ ≤ probZero (evolve (gateProduct G N) input) →
      (1/2:ℝ)+γ/2 ≤ probZero (evolve (gateProduct H N) input)) ∧
    (probZero (evolve (gateProduct G N) input) ≤ (1/2:ℝ)-γ →
      probZero (evolve (gateProduct H N) input) ≤ (1/2:ℝ)-γ/2) :=
  synthesized_signed_gap G H N hN ξ γ hG hH hgate (by linarith)

/-- The paper's specified `ξ=λ/(2^(k+6) K)` satisfies its advertised
`2ξ≤γ/4` for `γ=λ/(2^(k+3)√K)`, since `K≥1`. -/
theorem paper_synthesis_budget (lam K : ℝ) (k : ℕ) (hlam : 0≤lam) (hK : 1≤K) :
    2*(lam/((2:ℝ)^(k+6)*K)) ≤
      (lam/((2:ℝ)^(k+3)*Real.sqrt K))/4 := by
  have hK0 : 0<K := by linarith
  have hs : 0<Real.sqrt K := Real.sqrt_pos.mpr hK0
  have hsK : Real.sqrt K≤K := by
    nlinarith [sq_nonneg (Real.sqrt K-1), Real.sq_sqrt (le_of_lt hK0), Real.sqrt_nonneg K]
  have hp : (2:ℝ)^(k+6)=8*(2:ℝ)^(k+3) := by
    rw [show k+6=(k+3)+3 by omega, pow_add]
    norm_num <;> ring
  have hL : 2*(lam/((2:ℝ)^(k+6)*K))=lam/(4*(2:ℝ)^(k+3)*K) := by
    rw [hp]
    field_simp [ne_of_gt hK0]
    <;> ring
  have hR : (lam/((2:ℝ)^(k+3)*Real.sqrt K))/4=
      lam/(4*(2:ℝ)^(k+3)*Real.sqrt K) := by
    field_simp [ne_of_gt hs]
  rw [hL,hR]
  apply div_le_div_of_nonneg_left hlam (by positivity)
  exact mul_le_mul_of_nonneg_left hsK (by positivity)

/-- The complete source synthesis paragraph with its actual parameter choice,
unitary gate products, one-clean-qubit input, and final Born measurement.
The scalar probability-error estimate is a consequence of these semantics. -/
theorem synthesized_paper_gap [Nonempty n]
    (G H : ℕ → ProbeMatrix n) (N : ℕ) (hN : 0<N) (lam K : ℝ) (k : ℕ)
    (hlam : 0≤lam) (hK : 1≤K)
    (hG : ∀ j<N, Unitary (G j)) (hH : ∀ j<N, Unitary (H j))
    (hgate : ∀ j<N, ‖G j-H j‖ ≤ (lam/((2:ℝ)^(k+6)*K))/(N : ℝ)) :
    let γ := lam/((2:ℝ)^(k+3)*Real.sqrt K)
    ((1/2:ℝ)+γ ≤ probZero (evolve (gateProduct G N) input) →
      (1/2:ℝ)+γ/2 ≤ probZero (evolve (gateProduct H N) input)) ∧
    (probZero (evolve (gateProduct G N) input) ≤ (1/2:ℝ)-γ →
      probZero (evolve (gateProduct H N) input) ≤ (1/2:ℝ)-γ/2) := by
  apply synthesized_original_gap G H N hN (lam/((2:ℝ)^(k+6)*K)) _ (by positivity)
    hG hH hgate
  exact paper_synthesis_budget lam K k hlam hK

end Paper25.Synthesis
