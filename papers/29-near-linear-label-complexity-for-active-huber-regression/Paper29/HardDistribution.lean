import Paper29.HardDefs
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-! Actual fixed rank-r hard designs and their normalized finite hard laws. -/
noncomputable section
open scoped BigOperators
namespace Paper29.HardDistribution

lemma embedding_right_inverse (r d : ℕ) (hrd : r ≤ d) :
    embedding r d * (embedding r d).transpose = 1 := by
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.castLE hrd i)]
  · simp [embedding, Matrix.transpose_apply, Matrix.one_apply, Fin.ext_iff, eq_comm]
  · intro b _ hbi
    have hb : i.val ≠ b.val := by
      intro h
      apply hbi
      apply Fin.ext
      exact h.symm
    simp [embedding, Matrix.transpose_apply, hb]
  · simp

lemma rank_extend (n d r : ℕ) (U : Matrix (Fin n) (Fin r) ℝ)
    (hrd : r ≤ d) (hU : U.rank = r) : (U * embedding r d).rank = r := by
  apply le_antisymm
  · exact (Matrix.rank_mul_le_left U (embedding r d)).trans_eq hU
  · have hback : (U * embedding r d) * (embedding r d).transpose = U := by
      rw [Matrix.mul_assoc, embedding_right_inverse r d hrd, Matrix.mul_one]
    have h := Matrix.rank_mul_le_left (U * embedding r d) (embedding r d).transpose
    rw [hback, hU] at h
    exact h

lemma shortCore_rank (n r : ℕ) (hrn : r ≤ n) : (shortCore n r).rank = r := by
  have hminor : (shortCore n r).submatrix (Fin.castLE hrn) (Equiv.refl (Fin r)) = 1 := by
    ext i j
    simp [shortCore, Matrix.submatrix_apply, Matrix.one_apply, Fin.ext_iff]
  have h := Matrix.rank_submatrix_le (Fin.castLE hrn) (Equiv.refl (Fin r)) (shortCore n r)
  rw [hminor, Matrix.rank_one, Fintype.card_fin] at h
  exact le_antisymm (Matrix.rank_le_width (shortCore n r)) h

/-- The short hard design has exactly rank r, including all padding rows/columns. -/
theorem shortDesign_rank (n d r : ℕ) (hrn : r ≤ n) (hrd : r ≤ d) :
    (shortDesign n d r).rank = r :=
  rank_extend n d r (shortCore n r) hrd (shortCore_rank n r hrn)

lemma longCore_rank (n r N : ℕ) (hN : 0 < N) (hblocks : r * N ≤ n) :
    (longCore n r N).rank = r := by
  let e : Fin r → Fin n := fun j =>
    ⟨j.val * N, lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right j.isLt hN) hblocks⟩
  have hminor : (longCore n r N).submatrix e (Equiv.refl (Fin r)) =
      Matrix.diagonal (fun _ : Fin r => (4 : ℝ)) := by
    ext i j
    have hi : i.val * N < r * N := Nat.mul_lt_mul_of_pos_right i.isLt hN
    simp [longCore, Matrix.submatrix_apply, Matrix.diagonal_apply, e, hi,
      Nat.mul_div_cancel _ hN, Fin.ext_iff]
  have h := Matrix.rank_submatrix_le e (Equiv.refl (Fin r)) (longCore n r N)
  rw [hminor, Matrix.rank_diagonal] at h
  simp at h
  exact le_antisymm (Matrix.rank_le_width (longCore n r N)) h

/-- The block hard design has exactly rank r, with its zero padding retained. -/
theorem longDesign_rank (n d r N : ℕ) (hN : 0 < N)
    (hblocks : r * N ≤ n) (hrd : r ≤ d) : (longDesign n d r N).rank = r :=
  rank_extend n d r (longCore n r N) hrd (longCore_rank n r N hN hblocks)

/-- The design chosen in both paper regimes is rank exactly r for every n,d,r. -/
theorem fixedDesign_rank (n d r : ℕ) (hr : 1 ≤ r) (hrn : r ≤ n) (hrd : r ≤ d) :
    (fixedDesign n d r).rank = r := by
  unfold fixedDesign
  split_ifs
  · exact shortDesign_rank n d r hrn hrd
  · apply longDesign_rank n d r (n / r) (Nat.div_pos hrn (by omega)) _ hrd
    simpa [Nat.mul_comm] using Nat.div_mul_le_self n r

/-- Matrix multiplication implements exactly the first-r-coordinate embedding. -/
lemma extend_apply (n d r : ℕ) (U : Matrix (Fin n) (Fin r) ℝ) (i : Fin n) (j : Fin d) :
    (U * embedding r d) i j = if hj : j.val < r then U i ⟨j.val, hj⟩ else 0 := by
  by_cases hj : j.val < r
  · rw [dif_pos hj, Matrix.mul_apply]
    let k : Fin r := ⟨j.val, hj⟩
    have heq : ∀ a : Fin r, (a.val = j.val) ↔ a = k := by
      intro a
      constructor
      · intro h
        apply Fin.ext
        exact h
      · intro h
        simpa [k] using congrArg Fin.val h
    simp only [embedding, heq, mul_ite, mul_one, mul_zero]
    simp [k]
  · rw [dif_neg hj, Matrix.mul_apply]
    have hneq : ∀ a : Fin r, a.val ≠ j.val := by
      intro a h
      exact hj (h ▸ a.isLt)
    simp [embedding, hneq]

/-- These are the actual standard basis/zero entries of the short design. -/
theorem shortDesign_apply (n d r : ℕ) (i : Fin n) (j : Fin d) :
    shortDesign n d r i j = if j.val < r ∧ i.val = j.val then 1 else 0 := by
  rw [shortDesign, extend_apply]
  by_cases hj : j.val < r <;> simp [hj, shortCore]

/-- These are the actual repeated 4e_j/zero entries of the long design. -/
theorem longDesign_apply (n d r N : ℕ) (i : Fin n) (j : Fin d) :
    longDesign n d r N i j =
      if j.val < r ∧ i.val / N = j.val ∧ i.val < r * N then 4 else 0 := by
  rw [longDesign, extend_apply]
  by_cases hj : j.val < r <;> simp [hj, longCore]

/-- The exact bias choice in (4.7) obeys all of the paper's parameter bounds. -/
theorem beta_bounds (ε : ℝ) (N : ℕ) (hε : 0 < ε) (hεhi : ε ≤ 1 / 800)
    (hN : 160 ≤ N) :
    0 < beta ε N ∧ 200 * ε ≤ beta ε N ∧ beta ε N ≤ 1 / 4 ∧
      10 ≤ (N : ℝ) * (beta ε N) ^ 2 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN160 : (160 : ℝ) ≤ N := by exact_mod_cast hN
  have hfrac : (10 : ℝ) / N ≤ (1 / 4 : ℝ) ^ 2 := by
    apply (div_le_iff₀ hN0).2
    nlinarith
  have hs : Real.sqrt (10 / (N : ℝ)) ≤ (1 / 4 : ℝ) :=
    (Real.sqrt_le_iff).2 ⟨by norm_num, hfrac⟩
  have hb0 : 0 < beta ε N := (by positivity : 0 < 200 * ε).trans_le (le_max_left _ _)
  have hsle : Real.sqrt (10 / (N : ℝ)) ≤ beta ε N := le_max_right _ _
  have hsq : (10 : ℝ) / N ≤ (beta ε N) ^ 2 := by
    nlinarith [Real.sq_sqrt (show 0 ≤ (10 : ℝ) / N by positivity),
      Real.sqrt_nonneg (10 / (N : ℝ))]
  refine ⟨hb0, le_max_left _ _, max_le (by linarith) hs, ?_⟩
  have := (div_le_iff₀ hN0).1 hsq
  nlinarith

lemma bitMass_nonneg (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (b : Bool) :
    0 ≤ bitMass p b := by
  cases b <;> simp [bitMass] <;> linarith

lemma bitMass_total (p : ℝ) : ∑ b : Bool, bitMass p b = 1 := by
  simp [bitMass]

lemma signMass_total (r : ℕ) : ∑ s : Signs r, signMass r s = 1 := by
  simp [signMass, Signs]

lemma conditionalMass_nonneg {r N : ℕ} (β : ℝ) (hβ : 0 ≤ β) (hβhi : β ≤ 1 / 2)
    (s : Signs r) (y : Bits r N) : 0 ≤ conditionalMass β s y := by
  apply Finset.prod_nonneg
  intro a _
  apply bitMass_nonneg
  · cases s a.1 <;> simp [sign] <;> linarith
  · cases s a.1 <;> simp [sign] <;> linarith

/-- The conditional bit law is an actual normalized product Bernoulli law. -/
lemma conditionalMass_total {r N : ℕ} (β : ℝ) (s : Signs r) :
    ∑ y : Bits r N, conditionalMass β s y = 1 := by
  unfold conditionalMass
  rw [← Fintype.prod_sum (fun (a : Fin r × Fin N) (b : Bool) =>
    bitMass (1 / 2 + β * sign (s a.1)) b)]
  simp_rw [bitMass_total]
  simp

lemma hardMass_nonneg {r N : ℕ} (β : ℝ) (hβ : 0 ≤ β) (hβhi : β ≤ 1 / 2)
    (s : Signs r) (y : Bits r N) : 0 ≤ hardMass β s y := by
  apply mul_nonneg
  · unfold signMass
    positivity
  · exact conditionalMass_nonneg β hβ hβhi s y

/-- The source signs have exactly the independent uniform distribution. -/
lemma hardMass_sign_marginal {r N : ℕ} (β : ℝ) (s : Signs r) :
    ∑ y : Bits r N, hardMass β s y = ((2 : ℝ) ^ r)⁻¹ := by
  unfold hardMass
  rw [← Finset.mul_sum, conditionalMass_total, mul_one]
  rfl

/-- The finite hard joint response law is normalized, without certificate fields. -/
theorem hardMass_total {r N : ℕ} (β : ℝ) :
    ∑ s : Signs r, ∑ y : Bits r N, hardMass β s y = 1 := by
  simp_rw [hardMass_sign_marginal]
  exact signMass_total r

/-- The exact numerical coefficient in the expected decoding-error accounting. -/
theorem decoding_coefficient_lt : Real.exp (-5) + (9 / 400 : ℝ) + 0.01 < 0.04 := by
  have h : Real.exp 1 > (8 / 3 : ℝ) := by linarith [Real.exp_one_gt_d9]
  have hexp : Real.exp 5 = (Real.exp 1) ^ 5 := by
    rw [← Real.exp_nat_mul]
    norm_num
  have hpow : (8 / 3 : ℝ) ^ 5 < (Real.exp 1) ^ 5 := by
    exact pow_lt_pow_left₀ h (by norm_num) (by norm_num)
  have he5 : (400 / 3 : ℝ) < Real.exp 5 := by rw [hexp]; norm_num at hpow ⊢; linarith
  rw [Real.exp_neg]
  have hi : (Real.exp 5)⁻¹ < (3 / 400 : ℝ) := by
    apply (inv_lt_iff_one_lt_mul₀ (Real.exp_pos 5)).2
    linarith
  linarith

end Paper29.HardDistribution
