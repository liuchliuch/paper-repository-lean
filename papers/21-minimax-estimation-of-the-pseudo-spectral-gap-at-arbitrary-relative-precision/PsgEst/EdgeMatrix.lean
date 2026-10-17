import PsgEst.Concentration
import PsgEst.LaplacianOrder

open Matrix BigOperators Real Finset
open scoped InnerProductSpace
namespace PsgEst

/-- Euclidean operator norm for an arbitrary finite coordinate type. -/
noncomputable def matrixEuclideanNorm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) : ℝ := ‖Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) M‖

/-- A symmetric matrix has operator norm at most the uniform absolute bound
on its Rayleigh quotients. This is proved using the actual orthonormal
eigenbasis, rather than an assumed norm/order correspondence. -/
theorem matrixEuclideanNorm_le_of_quadratic {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (hM : M.IsHermitian) (R : ℝ) (hR : 0 ≤ R)
    (hq : ∀ x : ι → ℝ, |x ⬝ᵥ (M *ᵥ x)| ≤ R * (x ⬝ᵥ x)) :
    matrixEuclideanNorm M ≤ R := by
  let T := M.toEuclideanLin
  have hT : T.IsSymmetric := Matrix.isHermitian_iff_isSymmetric.mp hM
  let hn : Module.finrank ℝ (EuclideanSpace ℝ ι) = Fintype.card ι := finrank_euclideanSpace
  let b := hT.eigenvectorBasis hn
  have hq' : ∀ x : EuclideanSpace ℝ ι, |inner ℝ x (T x)| ≤ R*‖x‖^2 := by
    intro x
    rw [euclidean_norm_sq_dot]
    convert hq (x : ι → ℝ) using 1
    rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct_comm]
    rfl
  have heig (i : Fin (Fintype.card ι)) : |hT.eigenvalues hn i| ≤ R := by
    have hi := hq' (b i)
    rw [hT.apply_eigenvectorBasis hn i] at hi
    change |inner ℝ (b i) ((hT.eigenvalues hn i) • b i)| ≤ R*‖b i‖^2 at hi
    simpa only [inner_smul_right, real_inner_self_eq_norm_sq, b.orthonormal.1 i,
      one_pow, mul_one] using hi
  unfold matrixEuclideanNorm
  apply ContinuousLinearMap.opNorm_le_bound _ hR
  intro x
  have hs : ‖Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) M x‖^2 ≤ R^2*‖x‖^2 := by
    change ‖T x‖^2 ≤ R^2*‖x‖^2
    rw [spectral_norm_sq b (T x), spectral_norm_sq b x, mul_sum]
    apply sum_le_sum
    intro i _
    change ((hT.eigenvectorBasis hn).repr (T x) i)^2 ≤ R^2 * ((hT.eigenvectorBasis hn).repr x i)^2
    rw [hT.eigenvectorBasis_apply_self_apply hn x i, mul_pow]
    have hie := abs_le.mp (heig i)
    have hi2 : (hT.eigenvalues hn i)^2 ≤ R^2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hie.2) (by linarith : 0 ≤ R+hT.eigenvalues hn i)]
    exact mul_le_mul_of_nonneg_right hi2 (sq_nonneg _)
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hR (norm_nonneg x))).mp (by
    simpa only [mul_pow] using hs)

lemma posSemidef_sum {ι α : Type*} [Fintype ι] [Fintype α]
    (M : α → Matrix ι ι ℝ) (hM : ∀ a, (M a).PosSemidef) : (∑ a, M a).PosSemidef := by
  have hh : (∑ a, M a).IsHermitian := by
    change (∑ a, M a)ᴴ = ∑ a, M a
    rw [Matrix.conjTranspose_sum]
    exact sum_congr rfl (fun a _ => (hM a).isHermitian.eq)
  refine ⟨hh, ?_⟩
  intro x
  simp only [Matrix.sum_mulVec, dotProduct_sum]
  exact sum_nonneg (fun a _ => (hM a).2 x)

/-- PSD lower and upper bounds imply the required norm bound. -/
theorem matrixEuclideanNorm_le_of_psd_bounds {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (R : ℝ) (hR : 0 ≤ R)
    (hM : M.PosSemidef) (hupper : (R • (1 : Matrix ι ι ℝ) - M).PosSemidef) :
    matrixEuclideanNorm M ≤ R := by
  apply matrixEuclideanNorm_le_of_quadratic M hM.isHermitian R hR
  intro x
  have hlo : 0 ≤ x ⬝ᵥ (M *ᵥ x) := by simpa using hM.2 x
  have hhi := hupper.2 x
  simp only [sub_mulVec, smul_mulVec, one_mulVec, dotProduct_sub, dotProduct_smul,
    star_trivial, smul_eq_mul] at hhi
  rw [abs_of_nonneg hlo]
  linarith

/-- If both positive matrices are bounded by `R I`, their centered difference
has norm at most `R`, rather than the weaker triangle-inequality bound `2 R`. -/
theorem matrixEuclideanNorm_sub_le_of_psd_bounds {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W M : Matrix ι ι ℝ) (R : ℝ) (hR : 0 ≤ R)
    (hW : W.PosSemidef) (hM : M.PosSemidef)
    (hWu : (R • (1 : Matrix ι ι ℝ) - W).PosSemidef)
    (hMu : (R • (1 : Matrix ι ι ℝ) - M).PosSemidef) :
    matrixEuclideanNorm (W-M) ≤ R := by
  apply matrixEuclideanNorm_le_of_quadratic _ (hW.isHermitian.sub hM.isHermitian) R hR
  intro x
  have hw0 : 0 ≤ x ⬝ᵥ (W *ᵥ x) := by simpa using hW.2 x
  have hm0 : 0 ≤ x ⬝ᵥ (M *ᵥ x) := by simpa using hM.2 x
  have hwu := hWu.2 x
  have hmu := hMu.2 x
  simp only [sub_mulVec, smul_mulVec, one_mulVec, dotProduct_sub, dotProduct_smul,
    star_trivial, smul_eq_mul] at hwu hmu ⊢
  rw [abs_le]
  constructor <;> linarith

/-- Squaring a real self-adjoint matrix preserves positive semidefiniteness. -/
lemma hermitian_square_posSemidef {ι : Type*} [Fintype ι]
    (M : Matrix ι ι ℝ) (hM : M.IsHermitian) : (M*M).PosSemidef := by
  simpa only [hM.eq] using Matrix.posSemidef_conjTranspose_mul_self M

end PsgEst
