import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Genuine norm foldings used in (2), (5), and Lemma 2.1.
The angular expression is the paper's spherical distance on unit vectors.
This file does not claim the rectifiable-current Jacobian estimate. -/

set_option autoImplicit false
noncomputable section
namespace Paper28
open scoped InnerProductSpace
open WithLp

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K]

/-- Replace a Hilbert-space block by its norm, keeping the other block. -/
def normFold (u : WithLp 2 (H × K)) : WithLp 2 (H × ℝ) :=
  toLp 2 (u.fst, ‖u.snd‖)

theorem normFold_norm (u : WithLp 2 (H × K)) : ‖normFold u‖ = ‖u‖ := by
  have h : ‖normFold u‖ ^ 2 = ‖u‖ ^ 2 := by
    simp [normFold, prod_norm_sq_eq_of_L2, Real.norm_eq_abs]
  nlinarith [norm_nonneg (normFold u), norm_nonneg u]

theorem normFold_inner (u v : WithLp 2 (H × K)) :
    ⟪u, v⟫_ℝ ≤ ⟪normFold u, normFold v⟫_ℝ := by
  simpa [normFold, prod_inner_apply, real_inner_comm, mul_comm] using
    add_le_add_left (real_inner_le_norm u.snd v.snd) ⟪u.fst, v.fst⟫_ℝ

/-- On the unit sphere this is the round angular metric of the paper. -/
def angular {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (u v : E) : ℝ := Real.arccos ⟪u, v⟫_ℝ

theorem normFold_angular (u v : WithLp 2 (H × K)) :
    angular (normFold u) (normFold v) ≤ angular u v :=
  Real.arccos_le_arccos (normFold_inner u v)

/-- The folding is also a contraction for the ambient Hilbert distance. -/
theorem normFold_dist (u v : WithLp 2 (H × K)) :
    dist (normFold u) (normFold v) ≤ dist u v := by
  have hf := normFold_inner u v
  have hsq : ‖normFold u - normFold v‖ ^ 2 ≤ ‖u - v‖ ^ 2 := by
    rw [norm_sub_sq_real, norm_sub_sq_real, normFold_norm, normFold_norm]
    linarith
  rw [dist_eq_norm, dist_eq_norm]
  nlinarith [norm_nonneg (normFold u - normFold v), norm_nonneg (u - v)]

/-- The actual induced map on unit spheres. -/
def sphereNormFold (u : {u : WithLp 2 (H × K) // ‖u‖ = 1}) :
    {u : WithLp 2 (H × ℝ) // ‖u‖ = 1} :=
  ⟨normFold u.val, (normFold_norm u.val).trans u.property⟩

/-- Ambient space of the complementary foldings in Lemma 2.1. -/
abbrev Triple (H₁ H₂ : Type*) := WithLp 2 (H₁ × WithLp 2 (ℝ × H₂))

variable {H₁ H₂ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℝ H₂]

/-- `L(x,z,y) = (x, sqrt(z²+‖y‖²))`. -/
def leftFold (u : Triple H₁ H₂) : WithLp 2 (H₁ × ℝ) := normFold u

/-- Reorder the three orthogonal blocks as `(y,z,x)`. -/
def reverseTriple (u : Triple H₁ H₂) : Triple H₂ H₁ :=
  toLp 2 (u.snd.snd, toLp 2 (u.snd.fst, u.fst))

/-- `R(x,z,y) = (y, sqrt(z²+‖x‖²))`. -/
def rightFold (u : Triple H₁ H₂) : WithLp 2 (H₂ × ℝ) :=
  normFold (reverseTriple u)

theorem leftFold_formula (u : Triple H₁ H₂) :
    leftFold u = toLp 2 (u.fst, Real.sqrt (u.snd.fst ^ 2 + ‖u.snd.snd‖ ^ 2)) := by
  have h := prod_norm_sq_eq_of_L2 u.snd
  have hn : ‖u.snd‖ = Real.sqrt (u.snd.fst ^ 2 + ‖u.snd.snd‖ ^ 2) := by
    rw [← Real.sqrt_sq (norm_nonneg u.snd), h]
    simp [Real.norm_eq_abs]
  simp [leftFold, normFold, hn]

theorem rightFold_formula (u : Triple H₁ H₂) :
    rightFold u = toLp 2 (u.snd.snd, Real.sqrt (u.snd.fst ^ 2 + ‖u.fst‖ ^ 2)) := by
  exact leftFold_formula (reverseTriple u)

theorem reverseTriple_norm (u : Triple H₁ H₂) : ‖reverseTriple u‖ = ‖u‖ := by
  have h : ‖reverseTriple u‖ ^ 2 = ‖u‖ ^ 2 := by
    simp [reverseTriple, prod_norm_sq_eq_of_L2]
    ring
  nlinarith [norm_nonneg (reverseTriple u), norm_nonneg u]

theorem reverseTriple_inner (u v : Triple H₁ H₂) :
    ⟪reverseTriple u, reverseTriple v⟫_ℝ = ⟪u, v⟫_ℝ := by
  simp [reverseTriple, prod_inner_apply]
  ring

theorem leftFold_norm (u : Triple H₁ H₂) : ‖leftFold u‖ = ‖u‖ := normFold_norm u

theorem rightFold_norm (u : Triple H₁ H₂) : ‖rightFold u‖ = ‖u‖ :=
  (normFold_norm _).trans (reverseTriple_norm u)

theorem leftFold_angular (u v : Triple H₁ H₂) :
    angular (leftFold u) (leftFold v) ≤ angular u v := normFold_angular u v

theorem rightFold_angular (u v : Triple H₁ H₂) :
    angular (rightFold u) (rightFold v) ≤ angular u v := by
  have h := normFold_angular (reverseTriple u) (reverseTriple v)
  unfold angular at h ⊢
  rw [reverseTriple_inner] at h
  exact h

end Paper28
