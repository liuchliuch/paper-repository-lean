import Paper26.TailConvexity
import Paper26.ShellAccounting
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# The loss-to-tail constraints in Theorem 2.4

The ambient input is a genuine finite complex matrix on a direct sum. The
bottom principal block is the actual scaled rectangular Gram matrix `ZZᴴ/r`.
All entries of that block, including its off-diagonal entries, are retained.
No tail-energy bound is supplied as an external theorem or a structure field.
-/

noncomputable section
open scoped BigOperators Matrix ComplexOrder

namespace Paper26.TailLossConstraints

open Normalization TailConvexity

variable {ι σ κ : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype σ] [DecidableEq σ] [Fintype κ]

/-- The actual bottom principal block. -/
def bottomBlock (ρ : Matrix (ι ⊕ σ) (ι ⊕ σ) ℂ) : Matrix σ σ ℂ :=
  ρ.submatrix Sum.inr Sum.inr

/-- The input bottom block of a rank-`r` flat-support state. -/
def scaledGram (r : ℝ) (Z : Matrix σ κ ℂ) : Matrix σ σ ℂ :=
  ((1 / r : ℝ) : ℂ) • (Z * Zᴴ)

/-- True input mass on the bottom subspace, in the notation of Lemma 2.2. -/
def tailMass (r : ℝ) (Z : Matrix σ κ ℂ) : ℝ :=
  (Matrix.trace (Z * Zᴴ)).re / r

theorem tailMass_eq_frobeniusSq (r : ℝ) (Z : Matrix σ κ ℂ) :
    tailMass r Z = ShellAccounting.frobeniusSq Z / r := by
  rw [tailMass, ShellAccounting.frobeniusSq_eq_trace]

theorem tailMass_nonneg {r : ℝ} (hr : 0 < r) (Z : Matrix σ κ ℂ) :
    0 ≤ tailMass r Z := by
  rw [tailMass_eq_frobeniusSq]
  exact div_nonneg (ShellAccounting.frobeniusSq_nonneg Z) hr.le

/-- The intrinsic inverse Jordan operator agrees with the explicit diagonal
spectral inverse. This proves the link to the same `Q` and `H` as Lemma 2.3. -/
theorem jordanInverse_diagonal (a : σ → ℝ) (ha : ∀ i, 0 < a i)
    (X : Matrix σ σ ℂ) :
    jordanInverse (diagonalMatrix a) X = inverseJordan a X := by
  have hA : (diagonalMatrix a).PosDef :=
    Matrix.PosDef.diagonal (fun i => Complex.zero_lt_real.2 (ha i))
  exact (jordanInverse_unique_posDef _ _ _ hA (inverseJordan_equation a ha X)).symm

/-- Every ordered entry of a Hermitian matrix occurs in the true quadratic
form from Lemma 2.3, with its positive inverse-Jordan weight. -/
theorem Q_diagonal_spectral (a : σ → ℝ) (ha : ∀ i, 0 < a i)
    (X : Matrix σ σ ℂ) (hX : X.IsHermitian) :
    Q (diagonalMatrix a) X =
      ∑ i, ∑ j, (2 / (a i + a j)) * Complex.normSq (X i j) := by
  unfold Q pairing
  rw [jordanInverse_diagonal a ha]
  have hh : (X + diagonalMatrix a)ᴴ = X + diagonalMatrix a := by
    rw [Matrix.conjTranspose_add, hX.eq, diagonalMatrix_conjTranspose]
  have h := buresEnergy_eq_trace (X + diagonalMatrix a) a hh
  simpa only [buresEnergy, spectralEnergy, Matrix.add_apply,
    add_sub_cancel_right] using h.symm

theorem H_diagonal_spectral (a : σ → ℝ) (ha : ∀ i, 0 < a i)
    (Z : Matrix σ κ ℂ) :
    H (diagonalMatrix a) Z =
      ∑ i, ∑ j, (2 / (a i + a j)) * Complex.normSq ((Z * Zᴴ) i j) := by
  exact Q_diagonal_spectral a ha _ (Matrix.isHermitian_mul_conjTranspose_self Z)

/-- Restricting the full Bures sum to its bottom principal block can only
decrease it. The proof retains all four sectors of the full complex matrix
and discards only explicitly nonnegative summands. -/
theorem bottom_bures_le (ρ : Matrix (ι ⊕ σ) (ι ⊕ σ) ℂ)
    (b : ι → ℝ) (a : σ → ℝ) (hb : ∀ i, 0 < b i) (ha : ∀ i, 0 < a i) :
    buresEnergy (bottomBlock ρ) a ≤ buresEnergy ρ (Sum.elim b a) := by
  let s := Sum.elim b a
  let f (i j : ι ⊕ σ) : ℝ :=
    (2 / (s i + s j)) * Complex.normSq (ρ i j - diagonalMatrix s i j)
  have hs : ∀ i, 0 < s i := by intro i; cases i <;> simp [s, hb, ha]
  have hf (i j : ι ⊕ σ) : 0 ≤ f i j := by
    exact mul_nonneg (div_nonneg (by norm_num) (add_pos (hs i) (hs j)).le)
      (Complex.normSq_nonneg _)
  have heq : buresEnergy (bottomBlock ρ) a =
      ∑ i : σ, ∑ j : σ, f (Sum.inr i) (Sum.inr j) := by
    simp [buresEnergy, spectralEnergy, bottomBlock, f, s, diagonalMatrix,
      Matrix.diagonal]
  rw [heq]
  change (∑ i : σ, ∑ j : σ, f (Sum.inr i) (Sum.inr j)) ≤ ∑ i, ∑ j, f i j
  rw [Fintype.sum_sum_type]
  have htop : 0 ≤ ∑ i : ι, ∑ j, f (Sum.inl i) j :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hf _ _
  have hbottom : (∑ i : σ, ∑ j : σ, f (Sum.inr i) (Sum.inr j)) ≤
      ∑ i : σ, ∑ j, f (Sum.inr i) j := by
    apply Finset.sum_le_sum
    intro i _
    rw [Fintype.sum_sum_type]
    have h := Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) => hf (Sum.inr i) (Sum.inl j))
    linarith
  linarith

theorem scaledGram_trace (r : ℝ) (Z : Matrix σ κ ℂ) :
    (∑ i, (scaledGram r Z i i).re) = tailMass r Z := by
  simp only [scaledGram, Matrix.smul_apply, smul_eq_mul, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [← Finset.mul_sum]
  simp only [tailMass, Matrix.trace, Matrix.diag_apply, Complex.re_sum]
  ring

/-- The exact bottom-block identity used in Theorem 2.4, before imposing
success or a tail-mass bound. In particular the quartic term is the actual
intrinsic `H (diag a) Z`, rather than an independently defined surrogate. -/
theorem bottom_bures_expansion (a : σ → ℝ) (ha : ∀ i, 0 < a i)
    {r : ℝ} (hr : 0 < r) (Z : Matrix σ κ ℂ) :
    buresEnergy (scaledGram r Z) a =
      H (diagonalMatrix a) Z / r ^ 2 - 2 * tailMass r Z + ∑ i, a i := by
  have hdiag (i : σ) : 2 / (a i + a i) = 1 / a i := by
    field_simp [ne_of_gt (ha i)]
    <;> ring
  have hnorm (i j : σ) : Complex.normSq (scaledGram r Z i j) =
      (1 / r) ^ 2 * Complex.normSq ((Z * Zᴴ) i j) := by
    simp only [scaledGram, Matrix.smul_apply, smul_eq_mul, Complex.normSq_mul,
      Complex.normSq_ofReal, pow_two]
  have hquad : (∑ i, ∑ j, 2 / (a i + a j) * Complex.normSq (scaledGram r Z i j)) =
      (1 / r) ^ 2 * H (diagonalMatrix a) Z := by
    rw [H_diagonal_spectral a ha]
    simp only [hnorm, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  unfold buresEnergy
  rw [spectralEnergy_expansion _ _ _ (fun i => ne_of_gt (ha i)) hdiag,
    hquad, scaledGram_trace]
  ring

/-- The bottom trace identity is an actual lower bound on the full loss. -/
theorem bottom_bures_constraint (ρ : Matrix (ι ⊕ σ) (ι ⊕ σ) ℂ)
    (b : ι → ℝ) (a : σ → ℝ) (hb : ∀ i, 0 < b i) (ha : ∀ i, 0 < a i)
    {r : ℝ} (hr : 0 < r) (Z : Matrix σ κ ℂ)
    (hbottom : bottomBlock ρ = scaledGram r Z) :
    H (diagonalMatrix a) Z / r ^ 2 - 2 * tailMass r Z + ∑ i, a i ≤
      buresEnergy ρ (Sum.elim b a) := by
  have h := bottom_bures_le ρ b a hb ha
  rwa [hbottom, bottom_bures_expansion a ha hr Z] at h

/-- Equation (21)'s quartic constraint follows from the loss and the
Lemma 2.2 tail-mass bound. No quartic-energy bound is a premise. -/
theorem bures_success_H_bound (ρ : Matrix (ι ⊕ σ) (ι ⊕ σ) ℂ)
    (b : ι → ℝ) (a : σ → ℝ) (hb : ∀ i, 0 < b i) (ha : ∀ i, 0 < a i)
    {r ε : ℝ} (hr : 0 < r) (Z : Matrix σ κ ℂ)
    (hbottom : bottomBlock ρ = scaledGram r Z)
    (hsuccess : buresEnergy ρ (Sum.elim b a) ≤ ε)
    (htail : tailMass r Z ≤ 4 * ε) :
    H (diagonalMatrix a) Z ≤ 9 * r ^ 2 * ε := by
  have h := (bottom_bures_constraint ρ b a hb ha hr Z hbottom).trans hsuccess
  have hmass : 0 ≤ ∑ i, a i := Finset.sum_nonneg fun i _ => (ha i).le
  have hdiv : H (diagonalMatrix a) Z / r ^ 2 ≤ 9 * ε := by linarith
  have hmul := (div_le_iff₀ (sq_pos_of_pos hr)).1 hdiv
  nlinarith

/-- The same successful-set implication stated for the original trace
definition of the Bures loss and an arbitrary Hermitian ambient input. -/
theorem bures_success_H_bound_trace (ρ : Matrix (ι ⊕ σ) (ι ⊕ σ) ℂ)
    (hρ : ρ.IsHermitian) (b : ι → ℝ) (a : σ → ℝ)
    (hb : ∀ i, 0 < b i) (ha : ∀ i, 0 < a i)
    {r ε : ℝ} (hr : 0 < r) (Z : Matrix σ κ ℂ)
    (hbottom : bottomBlock ρ = scaledGram r Z)
    (hsuccess : standardBuresEnergy ρ (diagonalMatrix (Sum.elim b a)) ≤ ε)
    (htail : tailMass r Z ≤ 4 * ε) :
    H (diagonalMatrix a) Z ≤ 9 * r ^ 2 * ε := by
  apply bures_success_H_bound ρ b a hb ha hr Z hbottom _ htail
  have hs : ∀ i, 0 < Sum.elim b a i := by intro i; cases i <;> simp [hb, ha]
  rw [buresEnergy_eq_trace _ _ hρ.eq]
  simpa only [standardBuresEnergy, jordanInverse_diagonal _ hs] using hsuccess

/-- The actual top principal block. -/
def topBlock (P : Matrix (ι ⊕ σ) (ι ⊕ σ) ℂ) : Matrix ι ι ℂ :=
  P.submatrix Sum.inl Sum.inl

/-- The normalized flat-support input `P/r`. -/
def flatInput {η : Type*} (r : ℝ) (P : Matrix η η ℂ) : Matrix η η ℂ :=
  ((1 / r : ℝ) : ℂ) • P

/-- The real weighted trace used for each output block. -/
def weightedTrace {η : Type*} [Fintype η] [DecidableEq η]
    (a : η → ℝ) (X : Matrix η η ℂ) : ℝ :=
  (Matrix.trace (X * diagonalMatrix (fun i => 1 / a i))).re

/-- The genuine ellipsoid quadratic form from the right-inverse argument. -/
def ellipsoidEnergy (a : σ → ℝ) (Z : Matrix σ κ ℂ) : ℝ :=
  (Matrix.trace (Zᴴ * diagonalMatrix (fun i => 1 / a i) * Z)).re

theorem weightedTrace_spectral {η : Type*} [Fintype η] [DecidableEq η]
    (a : η → ℝ) (X : Matrix η η ℂ) :
    weightedTrace a X = ∑ i, (1 / a i) * (X i i).re := by
  simp [weightedTrace, Matrix.trace, Matrix.diag_apply, diagonalMatrix,
    Matrix.mul_diagonal, Complex.mul_re, mul_comm]

/-- Hermiticity and `P²=P` imply the exact column energy identity. -/
theorem projector_column_energy {η : Type*} [Fintype η]
    (P : Matrix η η ℂ) (hP : P.IsHermitian) (hproj : P * P = P) (j : η) :
    (∑ i, Complex.normSq (P i j)) = (P j j).re := by
  have hdiag := congrArg (fun X : Matrix η η ℂ => (X j j).re) hproj
  simp only [Matrix.mul_apply, Complex.re_sum] at hdiag
  have he (i : η) : (P j i * P i j).re = Complex.normSq (P i j) := by
    rw [← hP.apply j i, Complex.star_def, ← Complex.normSq_eq_conj_mul_self,
      Complex.ofReal_re]
  simpa only [he] using hdiag

/-- The original right-inverse trace identity for a normalized orthogonal
projector, proved from `P²=P`, rather than assumed as a loss formula. -/
theorem right_projector_trace {η : Type*} [Fintype η] [DecidableEq η]
    (P : Matrix η η ℂ) (hP : P.IsHermitian) (hproj : P * P = P)
    (s : η → ℝ) (hs : ∀ i, 0 < s i) (hsum : ∑ i, s i = 1)
    {r : ℝ} (hr : 0 < r) (htrace : Matrix.trace P = (r : ℂ)) :
    1 + rightEnergy (flatInput r P) s = weightedTrace s P / r ^ 2 := by
  have htr : ∑ i, (P i i).re = r := by
    have h := congrArg Complex.re htrace
    simpa only [Matrix.trace, Matrix.diag_apply, Complex.re_sum, Complex.ofReal_re] using h
  have hflat : (∑ i, (flatInput r P i i).re) = 1 := by
    simp only [flatInput, Matrix.smul_apply, smul_eq_mul, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    rw [← Finset.mul_sum, htr]
    field_simp [ne_of_gt hr]
  have hnorm (i j : η) : Complex.normSq (flatInput r P i j) =
      (1 / r) ^ 2 * Complex.normSq (P i j) := by
    simp only [flatInput, Matrix.smul_apply, smul_eq_mul, Complex.normSq_mul,
      Complex.normSq_ofReal, pow_two]
  have hcol (j : η) : (∑ i, 1 / s j * Complex.normSq (flatInput r P i j)) =
      (1 / r) ^ 2 * ((1 / s j) * (P j j).re) := by
    calc
      _ = (1 / r) ^ 2 * ((1 / s j) * ∑ i, Complex.normSq (P i j)) := by
        simp only [hnorm, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by rw [projector_column_energy P hP hproj j]
  have hquad : (∑ i, ∑ j, 1 / s j * Complex.normSq (flatInput r P i j)) =
      (1 / r) ^ 2 * weightedTrace s P := by
    rw [Finset.sum_comm]
    simp_rw [hcol]
    rw [← Finset.mul_sum, ← weightedTrace_spectral]
  unfold rightEnergy
  rw [spectralEnergy_expansion _ _ _ (fun i => ne_of_gt (hs i)) (fun _ => rfl),
    hquad, hflat, hsum]
  ring

theorem weightedTrace_blocks (P : Matrix (ι ⊕ σ) (ι ⊕ σ) ℂ)
    (b : ι → ℝ) (a : σ → ℝ) :
    weightedTrace (Sum.elim b a) P =
      weightedTrace b (topBlock P) + weightedTrace a (bottomBlock P) := by
  simp only [weightedTrace_spectral, Fintype.sum_sum_type, topBlock, bottomBlock,
    Matrix.submatrix_apply, Sum.elim_inl, Sum.elim_inr]

theorem gram_weightedTrace (a : σ → ℝ) (Z : Matrix σ κ ℂ) :
    weightedTrace a (Z * Zᴴ) = ellipsoidEnergy a Z := by
  unfold weightedTrace ellipsoidEnergy
  congr 1
  calc
    Matrix.trace (Z * Zᴴ * diagonalMatrix (fun i => 1 / a i)) =
        Matrix.trace (Z * (Zᴴ * diagonalMatrix (fun i => 1 / a i))) := by
      rw [Matrix.mul_assoc]
    _ = _ := Matrix.trace_mul_comm _ _

/-- Exact first display in the right-inverse proof of Theorem 2.4. -/
theorem right_projector_split (P : Matrix (ι ⊕ σ) (ι ⊕ σ) ℂ)
    (hP : P.IsHermitian) (hproj : P * P = P)
    (b : ι → ℝ) (a : σ → ℝ) (hb : ∀ i, 0 < b i) (ha : ∀ i, 0 < a i)
    (hsum : ∑ i, Sum.elim b a i = 1)
    {r : ℝ} (hr : 0 < r) (htrace : Matrix.trace P = (r : ℂ))
    (Z : Matrix σ κ ℂ) (hbottom : bottomBlock P = Z * Zᴴ) :
    1 + rightEnergy (flatInput r P) (Sum.elim b a) =
      weightedTrace b (topBlock P) / r ^ 2 + ellipsoidEnergy a Z / r ^ 2 := by
  have hs : ∀ i, 0 < Sum.elim b a i := by intro i; cases i <;> simp [hb, ha]
  rw [right_projector_trace P hP hproj _ hs hsum hr htrace,
    weightedTrace_blocks, hbottom, gram_weightedTrace]
  ring

/-- Given the standard top-block Cauchy--Schwarz/principal-angle estimate,
the successful-loss event implies the ellipsoid constraint. Only that
intermediate top-block estimate is supplied; the target ellipsoid bound is
derived here from the proved projector trace identity. -/
theorem right_success_ellipsoid_bound (P : Matrix (ι ⊕ σ) (ι ⊕ σ) ℂ)
    (hP : P.IsHermitian) (hproj : P * P = P)
    (b : ι → ℝ) (a : σ → ℝ) (hb : ∀ i, 0 < b i) (ha : ∀ i, 0 < a i)
    (hsum : ∑ i, Sum.elim b a i = 1)
    {r ε : ℝ} (hr : 0 < r) (htrace : Matrix.trace P = (r : ℂ))
    (Z : Matrix σ κ ℂ) (hbottom : bottomBlock P = Z * Zᴴ)
    (htop : (1 - tailMass r Z) ^ 2 ≤ weightedTrace b (topBlock P) / r ^ 2)
    (hsuccess : rightEnergy (flatInput r P) (Sum.elim b a) ≤ ε)
    (htail : tailMass r Z ≤ 4 * ε) :
    ellipsoidEnergy a Z ≤ 9 * r ^ 2 * ε := by
  have heq := right_projector_split P hP hproj b a hb ha hsum hr htrace Z hbottom
  have htop' : 1 - 2 * tailMass r Z ≤ weightedTrace b (topBlock P) / r ^ 2 := by
    nlinarith [sq_nonneg (tailMass r Z)]
  have hdiv : ellipsoidEnergy a Z / r ^ 2 ≤ 9 * ε := by linarith
  have hmul := (div_le_iff₀ (sq_pos_of_pos hr)).1 hdiv
  nlinarith

/-- A Hermitian projector has actual diagonal entries in `[0,1]`; both
bounds follow from the proved column energy identity. -/
theorem projector_diagonal_bounds {η : Type*} [Fintype η]
    (P : Matrix η η ℂ) (hP : P.IsHermitian) (hproj : P * P = P) (j : η) :
    0 ≤ (P j j).re ∧ (P j j).re ≤ 1 := by
  have hcol := projector_column_energy P hP hproj j
  have hnonneg : 0 ≤ (P j j).re := by
    rw [← hcol]
    exact Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _
  have hself : Complex.normSq (P j j) ≤ ∑ i, Complex.normSq (P i j) :=
    Finset.single_le_sum (fun i _ => Complex.normSq_nonneg (P i j)) (Finset.mem_univ j)
  rw [hcol] at hself
  have hsquare : (P j j).re ^ 2 ≤ Complex.normSq (P j j) := by
    rw [Complex.normSq_apply]
    nlinarith [sq_nonneg (P j j).im]
  constructor
  · exact hnonneg
  · nlinarith

/-- Weighted scalar Cauchy--Schwarz, applied to entries of a projector
compression. The auxiliary spectrum need only have mass at most one. -/
theorem weighted_diagonal_lower {η : Type*} [Fintype η]
    (p b : η → ℝ) (hb : ∀ i, 0 < b i)
    (hp : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) (hmass : ∑ i, b i ≤ 1) :
    (∑ i, p i) ^ 2 ≤ ∑ i, p i / b i := by
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul (R := ℝ)
    (r := p) (f := fun i => p i ^ 2 / b i) (g := b) Finset.univ
    (fun i _ => div_nonneg (sq_nonneg _) (hb i).le) (fun i _ => (hb i).le)
    (fun i _ => by rw [div_mul_cancel₀ _ (ne_of_gt (hb i))])
  have hmassmul : (∑ i, p i ^ 2 / b i) * (∑ i, b i) ≤ ∑ i, p i ^ 2 / b i := by
    have hn : 0 ≤ ∑ i, p i ^ 2 / b i := Finset.sum_nonneg fun i _ =>
      div_nonneg (sq_nonneg _) (hb i).le
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hmass hn
  apply (hcs.trans hmassmul).trans
  apply Finset.sum_le_sum
  intro i _
  apply div_le_div_of_nonneg_right _ (hb i).le
  have h := mul_nonneg (hp i) (sub_nonneg.2 (hp1 i))
  nlinarith

/-- The top-block lower bound can be proved without a principal-angle
external input: scalar Cauchy--Schwarz on its actual diagonal entries and
the projector constraints give the required estimate. -/
theorem projector_top_lower (P : Matrix (ι ⊕ σ) (ι ⊕ σ) ℂ)
    (hP : P.IsHermitian) (hproj : P * P = P)
    (b : ι → ℝ) (a : σ → ℝ) (hb : ∀ i, 0 < b i) (ha : ∀ i, 0 < a i)
    (hsum : ∑ i, Sum.elim b a i = 1)
    {r : ℝ} (hr : 0 < r) (htrace : Matrix.trace P = (r : ℂ))
    (Z : Matrix σ κ ℂ) (hbottom : bottomBlock P = Z * Zᴴ) :
    (1 - tailMass r Z) ^ 2 ≤ weightedTrace b (topBlock P) / r ^ 2 := by
  have hp (i : ι) : 0 ≤ (topBlock P i i).re ∧ (topBlock P i i).re ≤ 1 :=
    projector_diagonal_bounds P hP hproj (Sum.inl i)
  have hmass : ∑ i, b i ≤ 1 := by
    have hs := hsum
    rw [Fintype.sum_sum_type] at hs
    simp only [Sum.elim_inl, Sum.elim_inr] at hs
    have hn : 0 ≤ ∑ i, a i := Finset.sum_nonneg fun i _ => (ha i).le
    linarith
  have hcs := weighted_diagonal_lower (fun i => (topBlock P i i).re) b hb
    (fun i => (hp i).1) (fun i => (hp i).2) hmass
  have hw : (∑ i, (topBlock P i i).re / b i) = weightedTrace b (topBlock P) := by
    rw [weightedTrace_spectral]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hw] at hcs
  have ht : (∑ i, (topBlock P i i).re) + (Matrix.trace (Z * Zᴴ)).re = r := by
    have h := congrArg Complex.re htrace
    simp only [Matrix.trace, Matrix.diag_apply, Fintype.sum_sum_type,
      Complex.add_re, Complex.re_sum, Complex.ofReal_re] at h
    change (∑ i, (topBlock P i i).re) + (∑ i, (bottomBlock P i i).re) = r at h
    rw [hbottom] at h
    simpa only [Matrix.trace, Matrix.diag_apply, Complex.re_sum] using h
  have htop : (∑ i, (topBlock P i i).re) = r * (1 - tailMass r Z) := by
    unfold tailMass
    calc
      _ = r - (Matrix.trace (Z * Zᴴ)).re := by linarith
      _ = _ := by field_simp [ne_of_gt hr] <;> ring
  rw [htop] at hcs
  apply (le_div_iff₀ (sq_pos_of_pos hr)).2
  nlinarith

/-- The right-inverse ellipsoid constraint, with no intermediate inequality
or external-tool premise. Every loss-specific step is derived from genuine
Hermitian projector identities and positive output spectral entries. -/
theorem right_success_ellipsoid_bound_proved (P : Matrix (ι ⊕ σ) (ι ⊕ σ) ℂ)
    (hP : P.IsHermitian) (hproj : P * P = P)
    (b : ι → ℝ) (a : σ → ℝ) (hb : ∀ i, 0 < b i) (ha : ∀ i, 0 < a i)
    (hsum : ∑ i, Sum.elim b a i = 1)
    {r ε : ℝ} (hr : 0 < r) (htrace : Matrix.trace P = (r : ℂ))
    (Z : Matrix σ κ ℂ) (hbottom : bottomBlock P = Z * Zᴴ)
    (hsuccess : rightEnergy (flatInput r P) (Sum.elim b a) ≤ ε)
    (htail : tailMass r Z ≤ 4 * ε) :
    ellipsoidEnergy a Z ≤ 9 * r ^ 2 * ε := by
  exact right_success_ellipsoid_bound P hP hproj b a hb ha hsum hr htrace Z hbottom
    (projector_top_lower P hP hproj b a hb ha hsum hr htrace Z hbottom) hsuccess htail

/-- Equation (21) with the source's natural rank and an actual `s × r`
rectangular complex frame block. -/
theorem bures_success_rank (ρ : Matrix (ι ⊕ σ) (ι ⊕ σ) ℂ)
    (b : ι → ℝ) (a : σ → ℝ) (hb : ∀ i, 0 < b i) (ha : ∀ i, 0 < a i)
    {r : ℕ} (hr : 0 < r) {ε : ℝ} (Z : Matrix σ (Fin r) ℂ)
    (hbottom : bottomBlock ρ = scaledGram (r : ℝ) Z)
    (hsuccess : buresEnergy ρ (Sum.elim b a) ≤ ε)
    (htail : tailMass (r : ℝ) Z ≤ 4 * ε) :
    H (diagonalMatrix a) Z ≤ 9 * (r : ℝ) ^ 2 * ε := by
  exact bures_success_H_bound ρ b a hb ha (Nat.cast_pos.2 hr) Z hbottom hsuccess htail

/-- The right-inverse ellipsoid constraint with the source's natural rank,
and with the top-block estimate proved rather than supplied. -/
theorem right_success_rank (P : Matrix (ι ⊕ σ) (ι ⊕ σ) ℂ)
    (hP : P.IsHermitian) (hproj : P * P = P)
    (b : ι → ℝ) (a : σ → ℝ) (hb : ∀ i, 0 < b i) (ha : ∀ i, 0 < a i)
    (hsum : ∑ i, Sum.elim b a i = 1)
    {r : ℕ} (hr : 0 < r) (htrace : Matrix.trace P = (r : ℂ))
    {ε : ℝ} (Z : Matrix σ (Fin r) ℂ) (hbottom : bottomBlock P = Z * Zᴴ)
    (hsuccess : rightEnergy (flatInput (r : ℝ) P) (Sum.elim b a) ≤ ε)
    (htail : tailMass (r : ℝ) Z ≤ 4 * ε) :
    ellipsoidEnergy a Z ≤ 9 * (r : ℝ) ^ 2 * ε := by
  apply right_success_ellipsoid_bound_proved P hP hproj b a hb ha hsum
    (Nat.cast_pos.2 hr) _ Z hbottom hsuccess htail
  simpa only [Complex.ofReal_natCast] using htrace

end Paper26.TailLossConstraints
