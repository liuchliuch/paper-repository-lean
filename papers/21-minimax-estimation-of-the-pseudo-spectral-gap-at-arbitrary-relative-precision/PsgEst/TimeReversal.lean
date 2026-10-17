import PsgEst.GapsOfPowers
import PsgEst.BipartiteSpectrum

/-! Time reversal and the multiplicative-reversiblization interpretation of (2).
The ordered spectrum below is defined directly from the characteristic
polynomial of `(P*)^k P^k`, independently of the singular-value definition. -/

open Matrix BigOperators Real

namespace PsgEst

variable {d : ℕ}

/-- Time reversal with respect to the given positive stationary law. -/
noncomputable def timeReversal (S : Stoch d) (st : Stationary S) : Stoch d where
  P := Matrix.diagonal (fun i => (st.mu i)⁻¹) * S.Pᵀ * Matrix.diagonal st.mu
  nonneg i j := by
    simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.transpose_apply]
    exact mul_nonneg (mul_nonneg (inv_nonneg.mpr (st.nonneg i)) (S.nonneg j i)) (st.nonneg j)
  row_stoch i := by
    simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.transpose_apply]
    calc (∑ j, (st.mu i)⁻¹ * S.P j i * st.mu j)
        = (st.mu i)⁻¹ * ∑ j, st.mu j * S.P j i := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          ring
      _ = 1 := by rw [st.station, inv_mul_cancel₀ (st.pos i).ne']

@[simp] theorem timeReversal_apply (S : Stoch d) (st : Stationary S) (i j : Fin d) :
    (timeReversal S st).P i j = (st.mu i)⁻¹ * S.P j i * st.mu j := by
  simp [timeReversal, Matrix.diagonal_mul, Matrix.mul_diagonal]

/-- The reversed chain has the same stationary law, with no reversibility assumption. -/
noncomputable def timeReversalStationary (S : Stoch d) (st : Stationary S) :
    Stationary (timeReversal S st) where
  mu := st.mu
  pos := st.pos
  sum_one := st.sum_one
  station j := by
    simp only [timeReversal_apply]
    have ht (i : Fin d) : st.mu i * ((st.mu i)⁻¹ * S.P j i * st.mu j) = S.P j i * st.mu j := by
      rw [← mul_assoc, ← mul_assoc, mul_inv_cancel₀ (st.pos i).ne', one_mul]
    simp_rw [ht]
    rw [← Finset.sum_mul, S.row_stoch, one_mul]

@[simp] theorem timeReversalStationary_mu (S : Stoch d) (st : Stationary S) :
    (timeReversalStationary S st).mu = st.mu := rfl

private theorem diagonal_inv_mul (μ : Fin d → ℝ) (hμ : ∀ i, 0 < μ i) :
    Matrix.diagonal (fun i => (μ i)⁻¹) * Matrix.diagonal μ = 1 := by
  rw [Matrix.diagonal_mul_diagonal]
  have h : (fun i => (μ i)⁻¹ * μ i) = (fun _ => (1 : ℝ)) := by
    funext i
    exact inv_mul_cancel₀ (hμ i).ne'
  rw [h, Matrix.diagonal_one]

private theorem diagonal_mul_inv (μ : Fin d → ℝ) (hμ : ∀ i, 0 < μ i) :
    Matrix.diagonal μ * Matrix.diagonal (fun i => (μ i)⁻¹) = 1 := by
  rw [Matrix.diagonal_mul_diagonal]
  have h : (fun i => μ i * (μ i)⁻¹) = (fun _ => (1 : ℝ)) := by
    funext i
    exact mul_inv_cancel₀ (hμ i).ne'
  rw [h, Matrix.diagonal_one]

/-- The matrix formula is precisely `Dπ⁻¹ Pᵀ Dπ`, using the actual matrix inverse. -/
theorem timeReversal_eq_dpi (S : Stoch d) (st : Stationary S) :
    (timeReversal S st).P = (dpi st.mu)⁻¹ * S.Pᵀ * dpi st.mu := by
  have hi : (dpi st.mu)⁻¹ = Matrix.diagonal (fun i => (st.mu i)⁻¹) := by
    apply Matrix.inv_eq_left_inv
    exact diagonal_inv_mul st.mu st.pos
  rw [hi]
  rfl

/-- Reversing twice recovers the original transition matrix. -/
theorem timeReversal_involutive (S : Stoch d) (st : Stationary S) :
    (timeReversal (timeReversal S st) (timeReversalStationary S st)).P = S.P := by
  ext i j
  simp only [timeReversal_apply, timeReversalStationary_mu]
  field_simp [(st.pos i).ne', (st.pos j).ne']

/-- Time reversal commutes with taking powers, at the level of the source matrices. -/
theorem timeReversal_pow (S : Stoch d) (st : Stationary S) (k : ℕ) :
    (timeReversal S st).P ^ k =
      Matrix.diagonal (fun i => (st.mu i)⁻¹) * (S.P ^ k)ᵀ * Matrix.diagonal st.mu := by
  induction k with
  | zero =>
      simp only [pow_zero, Matrix.transpose_one, Matrix.mul_one]
      exact (diagonal_inv_mul st.mu st.pos).symm
  | succ k ih =>
      rw [pow_succ, ih]
      change (Matrix.diagonal (fun i => (st.mu i)⁻¹) * (S.P ^ k)ᵀ * Matrix.diagonal st.mu) *
        (Matrix.diagonal (fun i => (st.mu i)⁻¹) * S.Pᵀ * Matrix.diagonal st.mu) = _
      rw [pow_succ' S.P k, Matrix.transpose_mul]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (Matrix.diagonal st.mu), diagonal_mul_inv st.mu st.pos]
      simp

private theorem half_mul_inv (x : ℝ) (hx : 0 < x) :
    x ^ (1/2 : ℝ) * x⁻¹ = x ^ (-(1/2 : ℝ)) := by
  rw [← Real.rpow_neg_one, ← Real.rpow_add hx]
  congr 1
  ring

/-- The normalized operator of the reversed chain is the transpose of `L_k`. -/
theorem Lk_timeReversal (S : Stoch d) (st : Stationary S) (k : ℕ) :
    Lk (timeReversal S st) (timeReversalStationary S st) k = (Lk S st k)ᵀ := by
  change simil st.mu ((timeReversal S st).P ^ k) = (simil st.mu (S.P ^ k))ᵀ
  rw [timeReversal_pow]
  ext i j
  simp only [simil, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.transpose_apply]
  calc st.mu i ^ (1/2 : ℝ) * ((st.mu i)⁻¹ * (S.P ^ k) j i * st.mu j) *
        st.mu j ^ (-(1/2 : ℝ))
      = (st.mu i ^ (1/2 : ℝ) * (st.mu i)⁻¹) * (S.P ^ k) j i *
        (st.mu j ^ (-(1/2 : ℝ)) * st.mu j) := by ring
    _ = st.mu i ^ (-(1/2 : ℝ)) * (S.P ^ k) j i * st.mu j ^ (1/2 : ℝ) := by
      rw [half_mul_inv _ (st.pos i), rpow_neg_half_mul _ (st.pos j)]
    _ = st.mu j ^ (1/2 : ℝ) * (S.P ^ k) j i * st.mu i ^ (-(1/2 : ℝ)) := by ring

/-- Positive diagonal normalization preserves multiplication. -/
theorem simil_mul_positive (μ : Fin d → ℝ) (hμ : ∀ i, 0 < μ i)
    (A B : Matrix (Fin d) (Fin d) ℝ) :
    simil μ A * simil μ B = simil μ (A * B) := by
  unfold simil
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (Matrix.diagonal (fun i => μ i ^ (-(1/2 : ℝ)))),
    dpi_half_inv_mul μ hμ]
  simp

/-- Similarity normalization preserves the whole characteristic polynomial. -/
theorem simil_charpoly_positive (μ : Fin d → ℝ) (hμ : ∀ i, 0 < μ i)
    (A : Matrix (Fin d) (Fin d) ℝ) : (simil μ A).charpoly = A.charpoly := by
  unfold simil
  rw [Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, dpi_half_inv_mul μ hμ, Matrix.one_mul]

/-- The actual multiplicative reversiblization of the `k`th transition power. -/
noncomputable def reversiblization (S : Stoch d) (st : Stationary S) (k : ℕ) :
    Matrix (Fin d) (Fin d) ℝ := (timeReversal S st).P ^ k * S.P ^ k

/-- The multiplicative reversiblization is itself a stochastic transition matrix. -/
noncomputable def reversiblizationStoch (S : Stoch d) (st : Stationary S) (k : ℕ) : Stoch d where
  P := reversiblization S st k
  nonneg i j := Stoch.entry_mul_nonneg
    ((timeReversal S st).pow_nonneg k) (S.pow_nonneg k) i j
  row_stoch i := by
    simp only [reversiblization, Matrix.mul_apply]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, S.pow_row_stoch, mul_one]
    exact (timeReversal S st).pow_row_stoch k i

/-- Its stationary law is the same known law. -/
noncomputable def reversiblizationStationary (S : Stoch d) (st : Stationary S) (k : ℕ) :
    Stationary (reversiblizationStoch S st k) where
  mu := st.mu
  pos := st.pos
  sum_one := st.sum_one
  station j := by
    change ∑ i, st.mu i * ((timeReversal S st).P ^ k * S.P ^ k) i j = st.mu j
    simp only [Matrix.mul_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    simp_rw [← mul_assoc, ← Finset.sum_mul]
    have hrev (a : Fin d) : ∑ i, st.mu i * ((timeReversal S st).P ^ k) i a = st.mu a :=
      (stationaryPow (timeReversal S st) (timeReversalStationary S st) k).station a
    simp_rw [hrev]
    exact (stationaryPow S st k).station j

/-- Detailed balance of `(P*)^k P^k`, proved from its actual transition entries. -/
theorem reversiblization_detailedBalance (S : Stoch d) (st : Stationary S) (k : ℕ)
    (i j : Fin d) :
    st.mu i * reversiblization S st k i j = st.mu j * reversiblization S st k j i := by
  have he (a b : Fin d) : st.mu a * reversiblization S st k a b =
      ∑ l, st.mu l * (S.P ^ k) l a * (S.P ^ k) l b := by
    unfold reversiblization
    rw [Matrix.mul_apply, timeReversal_pow]
    simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.transpose_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    calc st.mu a * ((st.mu a)⁻¹ * (S.P ^ k) l a * st.mu l * (S.P ^ k) l b)
        = (st.mu a * (st.mu a)⁻¹) * (S.P ^ k) l a * st.mu l * (S.P ^ k) l b := by ring
      _ = st.mu l * (S.P ^ k) l a * (S.P ^ k) l b := by
        rw [mul_inv_cancel₀ (st.pos a).ne', one_mul]
        ring
  rw [he i j, he j i]
  apply Finset.sum_congr rfl
  intro l _
  ring

/-- The Gram matrix is the positive diagonal similarity of `(P*)^k P^k`. -/
theorem gram_Lk_eq_simil_reversiblization (S : Stoch d) (st : Stationary S) (k : ℕ) :
    gram (Lk S st k) = simil st.mu (reversiblization S st k) := by
  rw [gram, ← Lk_timeReversal S st k]
  exact simil_mul_positive st.mu st.pos _ _

/-- Equality of the entire characteristic spectra, with algebraic multiplicity. -/
theorem reversiblization_charpoly (S : Stoch d) (st : Stationary S) (k : ℕ) :
    (reversiblization S st k).charpoly = (gram (Lk S st k)).charpoly := by
  rw [gram_Lk_eq_simil_reversiblization, simil_charpoly_positive st.mu st.pos]

/-- Increasing matrix powers followed by time reversal has a real split spectrum. -/
theorem reversiblization_charpoly_splits (S : Stoch d) (st : Stationary S) (k : ℕ) :
    (reversiblization S st k).charpoly.Splits (RingHom.id ℝ) := by
  rw [reversiblization_charpoly]
  exact (gram_isHermitian _).splits_charpoly

/-- Real characteristic roots, decreasingly ordered and counted with multiplicity.
This definition depends on the matrix itself, rather than on its normalization. -/
noncomputable def orderedRealSpectrum (A : Matrix (Fin d) (Fin d) ℝ) : List ℝ :=
  A.charpoly.roots.sort (· ≥ ·)

/-- Every ordered eigenvalue of `(P*)^k P^k` is the corresponding Gram eigenvalue. -/
theorem reversiblization_ordered_spectrum (S : Stoch d) (st : Stationary S) (k : ℕ) :
    orderedRealSpectrum (reversiblization S st k) =
      List.ofFn (gram_isHermitian (Lk S st k)).eigenvalues₀ := by
  unfold orderedRealSpectrum
  rw [reversiblization_charpoly]
  simpa using (gram_isHermitian (Lk S st k)).sort_roots_charpoly_eq_eigenvalues₀

/-- The complete spectrum of the actual reversiblization lies in `[0,1]`. -/
theorem reversiblization_root_mem_Icc (S : Stoch d) (st : Stationary S) (k : ℕ)
    (x : ℝ) (hx : x ∈ (reversiblization S st k).charpoly.roots) : x ∈ Set.Icc (0 : ℝ) 1 := by
  rw [reversiblization_charpoly, (gram_isHermitian (Lk S st k)).roots_charpoly_eq_eigenvalues₀] at hx
  obtain ⟨j, _, hj⟩ := Multiset.mem_map.mp hx
  have hxj : gramEig₀ (Lk S st k) j = x := by simpa [gramEig₀] using hj
  rw [← hxj]
  exact ⟨gramEig₀_nonneg _ _, gramEig₀_le_one _ (Lk_contraction S st k) _⟩

/-- Its top eigenvalue is exactly one, including when the unit eigenvalue has
additional multiplicity. -/
theorem reversiblization_top_eigenvalue (hd : 0 < d)
    (S : Stoch d) (st : Stationary S) (k : ℕ) :
    ((orderedRealSpectrum (reversiblization S st k))[0]?).getD 0 = 1 := by
  rw [reversiblization_ordered_spectrum]
  have hj : 0 < Fintype.card (Fin d) := by simpa using hd
  simp only [List.getElem?_ofFn, hj, ↓reduceDIte, Option.getD_some]
  apply gram_top_one_of_singular_pair hd (Lk S st k) (Lk_contraction S st k)
    (stVec st) (stVec st)
  · intro hv
    have he := congrFun hv ⟨0, hd⟩
    have hp : 0 < stVec st ⟨0, hd⟩ := Real.rpow_pos_of_pos (st.pos _) _
    exact hp.ne' he
  · exact Lk_mulVec_stVec S st k
  · exact Lk_transpose_mulVec_stVec S st k

/-- Spectral gap from the second largest characteristic root, counted with
multiplicity. In this paper it is applied to a reversible stochastic matrix
with a nonnegative real spectrum, as proved for `reversiblization`. -/
noncomputable def charpolySpectralGap (A : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  1 - ((orderedRealSpectrum A)[1]?).getD 0

/-- The spectral gap of the actual matrix `(P*)^k P^k` equals the paper's `a_k`.
This identifies an independently defined characteristic-root gap with the
sorted singular-value deficit, rather than assuming their equivalence. -/
theorem reversiblization_spectralGap_eq_aK (hd : 1 < d)
    (S : Stoch d) (st : Stationary S) (k : ℕ) :
    charpolySpectralGap (reversiblization S st k) = aK S st k := by
  have hj : 1 < Fintype.card (Fin d) := by simpa using hd
  have hnonneg := gramEig₀_nonneg (Lk S st k) ⟨1, hj⟩
  unfold charpolySpectralGap
  rw [reversiblization_ordered_spectrum]
  simp only [List.getElem?_ofFn, hj, ↓reduceDIte, Option.getD_some]
  unfold aK aOf sigma2
  rw [dif_pos hd, Real.sq_sqrt (le_max_left 0 _), max_eq_right hnonneg]
  rfl

/-- Paulin's multiplicative-reversiblization definition agrees with the
singular-value pseudo-spectral gap used by the estimator. -/
theorem gammaPS_eq_reversiblization_gaps (hd : 1 < d)
    (S : Stoch d) (st : Stationary S) :
    gammaPS S st = ⨆ k : ℕ,
      if 0 < k then charpolySpectralGap (reversiblization S st k) / k else 0 := by
  unfold gammaPS
  congr 1
  funext k
  rw [reversiblization_spectralGap_eq_aK hd S st k]

/-- The supremum in the reversiblization convention is the attained maximum
appearing in the paper, with a maximizing lag at most the inverse gap. -/
theorem reversiblization_gap_max_attained (hd : 1 < d)
    (S : Stoch d) (st : Stationary S) (hgap : 0 < gammaPS S st) :
    ∃ k : ℕ, 0 < k ∧
      charpolySpectralGap (reversiblization S st k) / k = gammaPS S st ∧
      (k : ℝ) ≤ 1 / gammaPS S st := by
  obtain ⟨k, hk, heq, hbound⟩ := exists_max_lag S st hgap
  exact ⟨k, hk, by rwa [reversiblization_spectralGap_eq_aK hd S st k], hbound⟩

end PsgEst
