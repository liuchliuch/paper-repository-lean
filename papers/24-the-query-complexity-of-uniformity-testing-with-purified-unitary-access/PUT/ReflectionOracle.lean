import PUT.Oracle
import PUT.QueryModel
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

/-!
# The phase reflection as a valid preparation oracle

This packages the paper's concrete full-space reflection, rather than only
its coordinate involution, as a unitary in the actual query model.
-/

noncomputable section
open scoped ComplexConjugate InnerProductSpace
namespace PUT.ReflectionOracle

open PUT.QueryModel

/-- Coordinate vectors regarded with their physical Euclidean norm. -/
def euclid {ι : Type*} [Fintype ι] (x : ι → ℂ) : EuclideanSpace ℂ ι := WithLp.toLp 2 x

theorem inner_euclid {ι : Type*} [Fintype ι] (x : ι → ℂ)
    (y : EuclideanSpace ℂ ι) : inner ℂ (euclid x) y = cdot x (fun i => y i) := by
  simp [euclid, PiLp.inner_apply, cdot, RCLike.inner_apply, mul_comm]

theorem norm_euclid_of_cdot_one {ι : Type*} [Fintype ι] (x : ι → ℂ)
    (hx : cdot x x = 1) : ‖euclid x‖ = 1 := by
  have h : ‖euclid x‖ ^ 2 = (1 : ℝ) := by
    rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ), inner_euclid]
    change Complex.re (cdot x x) = 1
    rw [hx]
    rfl
  nlinarith [norm_nonneg (euclid x)]

/-- A unitary reflection on the entire physical register. -/
def unitary {d M : ℕ} (p : Fin d → ℝ) (θ : Fin d → Fin M → ℝ) :
    PurificationSpace d M ≃ₗᵢ[ℂ] PurificationSpace d M :=
  (ℂ ∙ euclid (sVec p M θ)).reflection

theorem unitary_apply {d M : ℕ} (p : Fin d → ℝ) (θ : Fin d → Fin M → ℝ)
    (hM : 0 < M) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (x : PurificationSpace d M) (q : HQ d M) :
    unitary p θ x q = reflectVec (sVec p M θ) (fun i => x i) q := by
  have hs : ‖euclid (sVec p M θ)‖ = 1 :=
    norm_euclid_of_cdot_one _ (sVec_dot_self p M θ hM hp hsum)
  rw [unitary, Submodule.reflection_singleton_apply, hs]
  rw [inner_euclid]
  simp [euclid, reflectVec, mul_assoc]

theorem zeroState_eq {d M : ℕ} : zeroState d M = euclid (botVec (d := d) (M := M)) := by
  ext q
  cases q with
  | inl u => cases u; simp [zeroState, euclid, botVec, EuclideanSpace.single_apply]
  | inr ij => simp [zeroState, euclid, botVec, EuclideanSpace.single_apply]

theorem unitary_prepares {d M : ℕ} (p : Fin d → ℝ) (θ : Fin d → Fin M → ℝ)
    (hM : 0 < M) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    unitary p θ (zeroState d M) = euclid (vExt p M θ) := by
  ext q
  rw [unitary_apply p θ hM hp hsum, zeroState_eq]
  change reflectVec (sVec p M θ) botVec q = vExt p M θ q
  rw [reflect_bot p M θ hM hp hsum]

theorem amplitude_factor {d M : ℕ} (p : Fin d → ℝ) (θ : Fin d → Fin M → ℝ)
    (hp : ∀ i, 0 ≤ p i) (i : Fin d) (j : Fin M) :
    vVec p M θ (i,j) = (Real.sqrt (p i) : ℂ) * garbageVec M θ i j := by
  simp only [vVec, vAmplitude, garbageVec, Real.sqrt_div (hp i),
    Complex.ofReal_div, Complex.ofReal_one]
  ring

/-- Every paper reflection is now an actual valid oracle, with no vacuous
condition on the conditional garbage. -/
def preparationOracle {d M : ℕ} (p : Fin d → ℝ) (θ : Fin d → Fin M → ℝ)
    (hM : 0 < M) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    PreparationOracle d M where
  unitary := unitary p θ
  probability := p
  nonnegative := hp
  total := hsum
  garbage := fun i => euclid (garbageVec M θ i)
  garbage_norm := by
    intro i
    apply norm_euclid_of_cdot_one
    unfold cdot
    simp_rw [conj_mul_self]
    rw [← Complex.ofReal_sum, garbageVec_normSq M θ i hM]
    rfl
  preparation_bot := by
    rw [unitary_prepares p θ hM hp hsum]
    rfl
  preparation_output := by
    intro i j
    rw [unitary_prepares p θ hM hp hsum]
    exact amplitude_factor p θ hp i j

end PUT.ReflectionOracle
