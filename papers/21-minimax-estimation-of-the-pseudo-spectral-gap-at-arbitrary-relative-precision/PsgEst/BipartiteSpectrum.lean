import PsgEst.Laplacian
import PsgEst.Estimator
import PsgEst.GapsOfPowers
import Mathlib.Data.Real.StarOrdered

/-! The ordered spectral identity for the normalized bipartite Laplacian.
The proof uses only the real symmetric spectral theorem.  In particular, it
also covers singular matrices, where dividing by the second singular value
would lose the zero-singular-value case. -/

open Matrix BigOperators Real

namespace PsgEst

private noncomputable def sortedBasis {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : A.IsHermitian) :
    OrthonormalBasis (Fin (Fintype.card ι)) ℝ (EuclideanSpace ℝ ι) :=
  (Matrix.isHermitian_iff_isSymmetric.mp hA).eigenvectorBasis
    (finrank_euclideanSpace (𝕜 := ℝ) (ι := ι))

private theorem sortedBasis_eigen {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : A.IsHermitian) (j : Fin (Fintype.card ι)) :
    A *ᵥ ⇑(sortedBasis hA j) = hA.eigenvalues₀ j • ⇑(sortedBasis hA j) := by
  simpa only [sortedBasis, Matrix.IsHermitian.eigenvalues₀, Matrix.toEuclideanLin_apply]
    using congrArg (fun v : EuclideanSpace ℝ ι => (v : ι → ℝ))
      ((Matrix.isHermitian_iff_isSymmetric.mp hA).apply_eigenvectorBasis
        finrank_euclideanSpace j)

private theorem eigenvector_single_support {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : A.IsHermitian) (k : Fin (Fintype.card ι))
    (v : EuclideanSpace ℝ ι) (t : ℝ)
    (hv : A *ᵥ ⇑v = t • ⇑v)
    (hs : ∀ j, j ≠ k → hA.eigenvalues₀ j ≠ t) :
    v = (sortedBasis hA).repr v k • sortedBasis hA k := by
  let b := sortedBasis hA
  have he : Matrix.toEuclideanLin A v = t • v := by
    ext i
    exact congrFun hv i
  have hc (j : Fin (Fintype.card ι)) :
      hA.eigenvalues₀ j * b.repr v j = t * b.repr v j := by
    have h := (Matrix.isHermitian_iff_isSymmetric.mp hA).eigenvectorBasis_apply_self_apply
      finrank_euclideanSpace v j
    rw [he] at h
    simpa [b, sortedBasis, Matrix.IsHermitian.eigenvalues₀] using h.symm
  apply b.repr.injective
  ext j
  by_cases hj : j = k
  · subst j
    simp [b]
  · have hz : b.repr v j = 0 := by
      have hn := hs j hj
      have hh := hc j
      exact (mul_eq_zero.mp (show (hA.eigenvalues₀ j - t) * b.repr v j = 0 by
        nlinarith)).resolve_left (sub_ne_zero.mpr hn)
    simp [b, hj, hz]

private theorem basis_not_both_multiples {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (b : OrthonormalBasis ι ℝ E) (i j : ι) (hij : i ≠ j)
    (z : E) (a c : ℝ) (hi : b i = a • z) (hj : b j = c • z) : False := by
  classical
  have h1 : (1 : ℝ) = a * b.repr z i := by
    simpa using congrArg (fun v => b.repr v i) hi
  have h0 : (0 : ℝ) = c * b.repr z i := by
    simpa [hij] using congrArg (fun v => b.repr v i) hj
  have hz : b.repr z i ≠ 0 := by intro h; simp [h] at h1
  have hc : c = 0 := (mul_eq_zero.mp h0.symm).resolve_right hz
  have : b j = 0 := by simpa [hc] using hj
  exact b.toBasis.ne_zero j this

/-- An eigenpair of the bipartite Laplacian below `1` projects to a Gram
    eigenpair with eigenvalue `(1-t)^2`. -/
theorem bipH_eigenpair_gram {d : ℕ} (L : Matrix (Fin d) (Fin d) ℝ)
    (x y : Fin d → ℝ) (t : ℝ)
    (he : bipH L *ᵥ Sum.elim x y = t • Sum.elim x y) :
    L *ᵥ y = (1 - t) • x ∧ Lᵀ *ᵥ x = (1 - t) • y ∧
      gram L *ᵥ y = (1 - t)^2 • y := by
  rw [bipH_mulVec] at he
  have hxy : L *ᵥ y = (1 - t) • x := by
    ext i
    have h := congrFun he (Sum.inl i)
    simp only [Sum.elim_inl, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h ⊢
    linarith
  have hyx : Lᵀ *ᵥ x = (1 - t) • y := by
    ext i
    have h := congrFun he (Sum.inr i)
    simp only [Sum.elim_inr, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h ⊢
    linarith
  refine ⟨hxy, hyx, ?_⟩
  rw [gram, ← Matrix.mulVec_mulVec, hxy, Matrix.mulVec_smul, hyx, smul_smul]
  congr 1
  ring

private theorem bipH_low_eigenvector {d : ℕ} (hd : 1 < d)
    (L : Matrix (Fin d) (Fin d) ℝ) (s : ℝ) (hs : 0 ≤ s)
    (htop : gramEig₀ L ⟨0, by simp; omega⟩ = 1)
    (hsecond : gramEig₀ L ⟨1, by simpa using hd⟩ = s^2)
    (x y : Fin d → ℝ) (t : ℝ)
    (he : bipH L *ᵥ Sum.elim x y = t • Sum.elim x y)
    (ht : t < 1 - s) :
    ∃ c : ℝ, Sum.elim x y = c • Sum.elim
      (L *ᵥ ⇑(sortedBasis (gram_isHermitian L) ⟨0, by simp; omega⟩))
      ⇑(sortedBasis (gram_isHermitian L) ⟨0, by simp; omega⟩) := by
  classical
  let i0 : Fin (Fintype.card (Fin d)) := ⟨0, by simp; omega⟩
  let i1 : Fin (Fintype.card (Fin d)) := ⟨1, by simpa using hd⟩
  let b := sortedBasis (gram_isHermitian L)
  let yE : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2 y
  obtain ⟨hxy, hyx, hgram⟩ := bipH_eigenpair_gram L x y t he
  have ht1 : t < 1 := by linarith
  have hlarge : gramEig₀ L i1 < (1 - t)^2 := by
    rw [hsecond]
    nlinarith
  have hsingle : yE = b.repr yE i0 • b i0 := by
    apply eigenvector_single_support (gram_isHermitian L) i0 yE ((1-t)^2) hgram
    intro j hj
    have hj1 : i1 ≤ j := by
      have hj0 : j.val ≠ 0 := by intro h; apply hj; apply Fin.ext; exact h
      change 1 ≤ j.val
      omega
    have hh := (gram_isHermitian L).eigenvalues₀_antitone hj1
    change gramEig₀ L j ≤ gramEig₀ L i1 at hh
    exact ne_of_lt (lt_of_le_of_lt hh hlarge)
  have hy : y = b.repr yE i0 • ⇑(b i0) := by
    exact congrArg (fun v : EuclideanSpace ℝ (Fin d) => (v : Fin d → ℝ)) hsingle
  have hGramOne : gram L *ᵥ y = y := by
    rw [hy, Matrix.mulVec_smul]
    have hg0 := sortedBasis_eigen (gram_isHermitian L) i0
    change gram L *ᵥ ⇑(b i0) = gramEig₀ L i0 • ⇑(b i0) at hg0
    rw [htop, one_smul] at hg0
    rw [hg0]
  have hxp : x = L *ᵥ y := by
    by_cases hy0 : y = 0
    · rw [hy0, Matrix.mulVec_zero] at hxy ⊢
      have htne : 1 - t ≠ 0 := by linarith
      exact (smul_eq_zero.mp hxy.symm).resolve_left htne
    · have ht0 : t = 0 := by
        obtain ⟨j, hj⟩ : ∃ j, y j ≠ 0 := by
          by_contra h
          apply hy0
          ext j
          simpa using not_exists.mp h j
        have hc := congrFun (hgram.symm.trans hGramOne) j
        simp only [Pi.smul_apply, smul_eq_mul] at hc
        have hsquare : (1-t)^2 = 1 := by
          exact (mul_right_cancel₀ hj (show (1-t)^2 * y j = 1 * y j by nlinarith [hc]))
        nlinarith
      simpa [ht0] using hxy.symm
  refine ⟨b.repr yE i0, ?_⟩
  rw [hxp, hy, Matrix.mulVec_smul, sumElim_smul]

private theorem bipH_lift_eigenvector {d : ℕ}
    (L : Matrix (Fin d) (Fin d) ℝ) (v : Fin d → ℝ) (s : ℝ)
    (_hs : 0 ≤ s) (he : gram L *ᵥ v = s^2 • v) :
    ∃ x : Fin d → ℝ,
      bipH L *ᵥ Sum.elim x v = (1-s) • Sum.elim x v := by
  by_cases hs0 : s = 0
  · have hg : gram L *ᵥ v = 0 := by simpa [hs0] using he
    have hv : L *ᵥ v = 0 := by
      have hstar : Lᴴ = Lᵀ := by ext i j; simp [Matrix.conjTranspose]
      have hh := (Matrix.conjTranspose_mul_self_mulVec_eq_zero L v).mp
        (by simpa [hstar, gram] using hg)
      exact hh
    refine ⟨0, ?_⟩
    rw [bipH_mulVec, hv, Matrix.mulVec_zero]
    simp [hs0]
  · let x := s⁻¹ • (L *ᵥ v)
    have hxy : L *ᵥ v = s • x := by
      dsimp [x]
      rw [smul_smul, mul_inv_cancel₀ hs0, one_smul]
    have hyx : Lᵀ *ᵥ x = s • v := by
      dsimp [x]
      rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec]
      change s⁻¹ • (gram L *ᵥ v) = _
      rw [he, smul_smul]
      congr 1
      field_simp
    exact ⟨x, (bipH_eigenvector_of_singPair L x v s hxy hyx).1⟩

/-- A nonzero singular pair of singular value one, together with contraction,
    gives the largest Gram eigenvalue one. This supplies the hypothesis of
    `bipH_second_smallest_eq` directly from stationary or count vectors. -/
theorem gram_top_one_of_singular_pair {d : ℕ} (hd : 0 < d)
    (L : Matrix (Fin d) (Fin d) ℝ)
    (hcontr : ∀ w : Fin d → ℝ, (∑ i, (L *ᵥ w) i ^ 2) ≤ ∑ i, w i ^ 2)
    (u v : Fin d → ℝ) (hv : v ≠ 0)
    (hLu : L *ᵥ v = u) (hLTu : Lᵀ *ᵥ u = v) :
    gramEig₀ L ⟨0, by simpa using hd⟩ = 1 := by
  classical
  let i0 : Fin (Fintype.card (Fin d)) := ⟨0, by simpa using hd⟩
  apply le_antisymm (gramEig₀_le_one L hcontr i0)
  by_contra h
  have htop : gramEig₀ L i0 < 1 := lt_of_not_ge h
  have hg : gram L *ᵥ v = v := by
    rw [gram, ← Matrix.mulVec_mulVec, hLu, hLTu]
  let vE : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2 v
  let b := sortedBasis (gram_isHermitian L)
  have he : Matrix.toEuclideanLin (gram L) vE = vE := by
    ext i
    exact congrFun hg i
  have hz : b.repr vE = 0 := by
    ext j
    have hc := (Matrix.isHermitian_iff_isSymmetric.mp (gram_isHermitian L)).eigenvectorBasis_apply_self_apply
      finrank_euclideanSpace vE j
    rw [he] at hc
    change b.repr vE j = gramEig₀ L j * b.repr vE j at hc
    have hh := (gram_isHermitian L).eigenvalues₀_antitone (show i0 ≤ j by change 0 ≤ j.val; exact Nat.zero_le _)
    change gramEig₀ L j ≤ gramEig₀ L i0 at hh
    have hn : 1 - gramEig₀ L j ≠ 0 := by linarith
    have hc0 : b.repr vE j = 0 :=
      (mul_eq_zero.mp (show (1-gramEig₀ L j) * b.repr vE j = 0 by nlinarith)).resolve_left hn
    simpa using hc0
  have hv0 : vE = 0 := b.repr.injective (by simpa using hz)
  apply hv
  exact congrArg (fun w : EuclideanSpace ℝ (Fin d) => (w : Fin d → ℝ)) hv0

/-- The second smallest eigenvalue of the paper's actual block matrix is
`1 - σ₂(L)`. The hypotheses state the usual Euclidean contraction and that
the largest squared singular value is one. No simplicity hypothesis is needed. -/
theorem bipH_second_smallest_eq {d : ℕ} (hd : 1 < d)
    (L : Matrix (Fin d) (Fin d) ℝ)
    (hcontr : ∀ u : Fin d → ℝ, (∑ i, (L *ᵥ u) i ^ 2) ≤ ∑ i, u i ^ 2)
    (htop : gramEig₀ L ⟨0, by simp; omega⟩ = 1) :
    (bipH_isHermitian L).eigenvalues₀
      ⟨Fintype.card (Fin d ⊕ Fin d) - 2, by simp; omega⟩ = 1 - sigma2 L := by
  classical
  let N := Fintype.card (Fin d ⊕ Fin d)
  have hN : N = 2*d := by simp [N]; omega
  let k2 : Fin N := ⟨N-2, by omega⟩
  let kl : Fin N := ⟨N-1, by omega⟩
  let i0 : Fin (Fintype.card (Fin d)) := ⟨0, by simp; omega⟩
  let i1 : Fin (Fintype.card (Fin d)) := ⟨1, by simpa using hd⟩
  let bG := sortedBasis (gram_isHermitian L)
  let bH := sortedBasis (bipH_isHermitian L)
  let s := sigma2 L
  have hs : 0 ≤ s := (sigma2_mem_of_contraction L hcontr).1
  have hs1 : s ≤ 1 := (sigma2_mem_of_contraction L hcontr).2
  have hsecond : gramEig₀ L i1 = s^2 := by
    dsimp [s]
    rw [sigma2, dif_pos hd]
    have hge := gramEig₀_nonneg L i1
    rw [max_eq_right hge, Real.sq_sqrt hge]
  change (bipH_isHermitian L).eigenvalues₀ k2 = 1-s
  apply le_antisymm
  · by_contra hn
    have hlarge : 1-s < (bipH_isHermitian L).eigenvalues₀ k2 := lt_of_not_ge hn
    have hsupport (v : EuclideanSpace ℝ (Fin d ⊕ Fin d)) (t : ℝ)
        (he : bipH L *ᵥ ⇑v = t • ⇑v) (ht : t ≤ 1-s) :
        v = bH.repr v kl • bH kl := by
      apply eigenvector_single_support (bipH_isHermitian L) kl v t he
      intro j hj
      have hj2 : j ≤ k2 := by
        change j.val ≤ N-2
        have hlast : j.val ≠ N-1 := by
          intro h; apply hj; apply Fin.ext; exact h
        have hjn := j.isLt
        omega
      have hh := (bipH_isHermitian L).eigenvalues₀_antitone hj2
      exact ne_of_gt (lt_of_le_of_lt ht (lt_of_lt_of_le hlarge hh))
    have hg0 : gram L *ᵥ ⇑(bG i0) = (1:ℝ)^2 • ⇑(bG i0) := by
      have hh := sortedBasis_eigen (gram_isHermitian L) i0
      change gram L *ᵥ ⇑(bG i0) = gramEig₀ L i0 • ⇑(bG i0) at hh
      rw [htop] at hh
      simpa using hh
    have hg1 : gram L *ᵥ ⇑(bG i1) = s^2 • ⇑(bG i1) := by
      have hh := sortedBasis_eigen (gram_isHermitian L) i1
      change gram L *ᵥ ⇑(bG i1) = gramEig₀ L i1 • ⇑(bG i1) at hh
      simpa [hsecond] using hh
    obtain ⟨x0, he0⟩ := bipH_lift_eigenvector L ⇑(bG i0) 1 (by norm_num) hg0
    obtain ⟨x1, he1⟩ := bipH_lift_eigenvector L ⇑(bG i1) s hs hg1
    let w0 : EuclideanSpace ℝ (Fin d ⊕ Fin d) := WithLp.toLp 2 (Sum.elim x0 ⇑(bG i0))
    let w1 : EuclideanSpace ℝ (Fin d ⊕ Fin d) := WithLp.toLp 2 (Sum.elim x1 ⇑(bG i1))
    have hw0 := hsupport w0 0 (by simpa [w0] using he0) (by linarith)
    have hw1 := hsupport w1 (1-s) he1 le_rfl
    let z : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2 (fun i => bH kl (Sum.inr i))
    have hy0 : bG i0 = bH.repr w0 kl • z := by
      ext i
      exact congrArg (fun v : EuclideanSpace ℝ (Fin d ⊕ Fin d) => v (Sum.inr i)) hw0
    have hy1 : bG i1 = bH.repr w1 kl • z := by
      ext i
      exact congrArg (fun v : EuclideanSpace ℝ (Fin d ⊕ Fin d) => v (Sum.inr i)) hw1
    exact basis_not_both_multiples bG i0 i1 (by intro h; have := congrArg Fin.val h; simp [i0,i1] at this)
      z _ _ hy0 hy1
  · by_contra hn
    have hsmall : (bipH_isHermitian L).eigenvalues₀ k2 < 1-s := lt_of_not_ge hn
    have hlast : (bipH_isHermitian L).eigenvalues₀ kl < 1-s := by
      have hh := (bipH_isHermitian L).eigenvalues₀_antitone
        (show k2 ≤ kl by change N-2 ≤ N-1; omega)
      exact lt_of_le_of_lt hh hsmall
    let w : EuclideanSpace ℝ (Fin d ⊕ Fin d) := WithLp.toLp 2
      (Sum.elim (L *ᵥ ⇑(bG i0)) ⇑(bG i0))
    have hlow (j : Fin N) (hj : (bipH_isHermitian L).eigenvalues₀ j < 1-s) :
        ∃ c : ℝ, bH j = c • w := by
      let x : Fin d → ℝ := fun i => bH j (Sum.inl i)
      let y : Fin d → ℝ := fun i => bH j (Sum.inr i)
      have he : bipH L *ᵥ Sum.elim x y =
          (bipH_isHermitian L).eigenvalues₀ j • Sum.elim x y := by
        have hh := sortedBasis_eigen (bipH_isHermitian L) j
        have hv : Sum.elim x y = ⇑(bH j) := by ext q; cases q <;> rfl
        rwa [hv]
      obtain ⟨c, hc⟩ := bipH_low_eigenvector hd L s hs htop hsecond x y
        ((bipH_isHermitian L).eigenvalues₀ j) he hj
      refine ⟨c, ?_⟩
      ext q
      have hh := congrFun hc q
      cases q <;> exact hh
    obtain ⟨a, ha⟩ := hlow k2 hsmall
    obtain ⟨c, hc⟩ := hlow kl hlast
    exact basis_not_both_multiples bH k2 kl
      (by intro h; have hh := congrArg Fin.val h; change N-2 = N-1 at hh; omega)
      w a c ha hc

/-- Version whose unit top singular value is witnessed by an actual nonzero
singular pair. Both the population and empirical normalized operators have
such pairs. -/
theorem bipH_second_smallest_eq_of_singular_pair {d : ℕ} (hd : 1 < d)
    (L : Matrix (Fin d) (Fin d) ℝ)
    (hcontr : ∀ w : Fin d → ℝ, (∑ i, (L *ᵥ w) i ^ 2) ≤ ∑ i, w i ^ 2)
    (u v : Fin d → ℝ) (hv : v ≠ 0)
    (hLu : L *ᵥ v = u) (hLTu : Lᵀ *ᵥ u = v) :
    (bipH_isHermitian L).eigenvalues₀
      ⟨Fintype.card (Fin d ⊕ Fin d) - 2, by simp; omega⟩ = 1 - sigma2 L :=
  bipH_second_smallest_eq hd L hcontr
    (gram_top_one_of_singular_pair (by omega) L hcontr u v hv hLu hLTu)

/-- The second half of the empirical unit singular pair, directly from the
column sums of the transition-count matrix. -/
theorem lhat_transpose_sqrt_out {d m : ℕ}
    (Y : Fin (m+1) → Fin d) (hpos : degPos Y) :
    (lHat Y)ᵀ *ᵥ (fun i => (outDeg Y i : ℝ)^((1:ℝ)/2)) =
      (fun j => (inDeg Y j : ℝ)^((1:ℝ)/2)) := by
  classical
  have hT : (lHat Y)ᵀ =
      diagonal (fun j => (inDeg Y j : ℝ)^(-(1/2:ℝ))) *
        (countMatR Y)ᵀ * diagonal (fun i => (outDeg Y i : ℝ)^(-(1/2:ℝ))) := by
    rw [lHat_eq_of_degPos Y hpos, Matrix.transpose_mul, Matrix.transpose_mul]
    simp only [Matrix.diagonal_transpose, Matrix.mul_assoc]
  have hd : diagonal (fun i => (outDeg Y i : ℝ)^(-(1/2:ℝ))) *ᵥ
      (fun i => (outDeg Y i : ℝ)^((1:ℝ)/2)) = (fun _ => (1:ℝ)) := by
    ext i
    simp only [Matrix.mulVec_diagonal]
    exact rpow_neg_half_cancel _ (Nat.cast_pos.mpr (hpos i).1)
  have hc : (countMatR Y)ᵀ *ᵥ (fun _ => (1:ℝ)) = (fun j => (inDeg Y j : ℝ)) := by
    ext j
    simpa [Matrix.mulVec, dotProduct] using countMatR_col_sum Y j
  rw [hT, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hd, hc]
  ext j
  simp only [Matrix.mulVec_diagonal]
  exact rpow_neg_half_mul _ (Nat.cast_pos.mpr (hpos j).2)

/-- The empirical normalized count matrix has the ordered bipartite spectral
identity on the positive-degree event. -/
theorem lhat_bipH_second_smallest_eq {d m : ℕ} (hd : 1 < d)
    (Y : Fin (m+1) → Fin d) (hpos : degPos Y) :
    (bipH_isHermitian (lHat Y)).eigenvalues₀
      ⟨Fintype.card (Fin d ⊕ Fin d)-2, by simp; omega⟩ = 1-sigma2 (lHat Y) := by
  classical
  apply bipH_second_smallest_eq_of_singular_pair hd (lHat Y)
    (lhat_contraction Y hpos)
    (fun i => (outDeg Y i : ℝ)^((1:ℝ)/2))
    (fun j => (inDeg Y j : ℝ)^((1:ℝ)/2))
  · intro hv
    have hh := congrFun hv ⟨0, by omega⟩
    have hp : 0 < (inDeg Y ⟨0, by omega⟩ : ℝ)^((1:ℝ)/2) :=
      Real.rpow_pos_of_pos (Nat.cast_pos.mpr (hpos _).2) _
    exact (ne_of_gt hp) hh
  · exact (lhat_sigma1_one Y hpos).1
  · exact lhat_transpose_sqrt_out Y hpos

/-- Population normalized operators satisfy the same ordered identity, using
    the square root of the stationary law as their unit singular pair. -/
theorem Lk_bipH_second_smallest_eq {d : ℕ} (hd : 1 < d)
    (S : Stoch d) (st : Stationary S) (t : ℕ) :
    (bipH_isHermitian (Lk S st t)).eigenvalues₀
      ⟨Fintype.card (Fin d ⊕ Fin d)-2, by simp; omega⟩ = 1-sigma2 (Lk S st t) := by
  classical
  apply bipH_second_smallest_eq_of_singular_pair hd (Lk S st t)
    (Lk_contraction S st t) (stVec st) (stVec st)
  · intro hv
    have hh := congrFun hv ⟨0, by omega⟩
    have hp : 0 < stVec st ⟨0, by omega⟩ :=
      Real.rpow_pos_of_pos (st.pos _) _
    exact (ne_of_gt hp) hh
  · exact Lk_mulVec_stVec S st t
  · exact Lk_transpose_mulVec_stVec S st t

end PsgEst
