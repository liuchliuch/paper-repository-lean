import Paper18.Fusion.Basic
import Paper18.Results.PF
import Paper18.Results.PFExistence

/-!
# Frobenius–Perron dimensions derived from finite fusion rules

Raw fusion rules carry natural multiplicities, unit, duality, reciprocity and
associativity. Positive dimensions are a consequence of these rules.
-/

noncomputable section
open Classical
open scoped BigOperators Matrix
universe u

namespace Paper18

/-- Finite based fusion rules without a chosen dimension function. -/
structure FusionRules (ι : Type u) [Fintype ι] where
  one : ι
  dual : ι → ι
  N : ι → ι → ι → ℕ
  dual_involutive : ∀ x, dual (dual x) = x
  dual_one : dual one = one
  N_one_left : ∀ x y, N one x y = if x = y then 1 else 0
  N_one_right : ∀ x y, N x one y = if x = y then 1 else 0
  N_dual : ∀ x y z, N x y z = N (dual x) z y
  N_right : ∀ x y z, N x y z = N z (dual y) x
  N_assoc : ∀ x y z t, ∑ s, N x y s * N s z t = ∑ s, N y z s * N x s t

namespace FusionRules

variable {ι : Type u} [Fintype ι] (R : FusionRules ι)

lemma dual_bijective : Function.Bijective R.dual :=
  Function.Involutive.bijective R.dual_involutive

/-- Associativity and the dual-unit coefficient ensure a constituent exists. -/
lemma exists_constituent (x y : ι) : ∃ z, 0 < R.N x y z := by
  by_contra! h
  have hz : ∀ z, R.N x y z = 0 := fun z => Nat.eq_zero_of_le_zero (h z)
  have hunit : R.N (R.dual x) x R.one = 1 := by
    rw [R.N_dual, R.dual_involutive, R.N_one_right]
    simp
  have hge : 1 ≤ ∑ s, R.N (R.dual x) x s * R.N s y y := by
    calc
      1 = R.N (R.dual x) x R.one * R.N R.one y y := by
        simp [hunit, R.N_one_left]
      _ ≤ ∑ s, R.N (R.dual x) x s * R.N s y y :=
        Finset.single_le_sum
          (f := fun s => R.N (R.dual x) x s * R.N s y y)
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ R.one)
  rw [R.N_assoc] at hge
  simp [hz] at hge

lemma assoc_real (x y z t : ι) :
    ∑ s, (R.N x y s : ℝ) * (R.N s z t : ℝ) =
      ∑ s, (R.N y z s : ℝ) * (R.N x s t : ℝ) := by
  exact_mod_cast R.N_assoc x y z t

/-- Sum of all right multiplication matrices. -/
def dimensionMatrix : Matrix ι ι ℝ := fun i j => ∑ s, (R.N i s j : ℝ)

def leftMatrix (x : ι) : Matrix ι ι ℝ := fun i j => (R.N x i j : ℝ)

lemma dimensionMatrix_symm (i j : ι) : R.dimensionMatrix i j = R.dimensionMatrix j i := by
  calc
    R.dimensionMatrix i j = ∑ s, (R.N j (R.dual s) i : ℝ) := by
      apply Finset.sum_congr rfl
      intro s _
      rw [R.N_right]
    _ = R.dimensionMatrix j i :=
      Fintype.sum_bijective R.dual R.dual_bijective _ _ (fun s => rfl)

lemma dimensionMatrix_pos (i j : ι) : 0 < R.dimensionMatrix i j := by
  obtain ⟨s, hs⟩ := R.exists_constituent (R.dual i) j
  apply Finset.sum_pos' (fun _ _ => Nat.cast_nonneg _)
  refine ⟨s, Finset.mem_univ _, ?_⟩
  rw [R.N_dual]
  exact_mod_cast hs

lemma leftMatrix_commute (x : ι) :
    R.leftMatrix x * R.dimensionMatrix = R.dimensionMatrix * R.leftMatrix x := by
  ext i j
  simp only [Matrix.mul_apply, leftMatrix, dimensionMatrix, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [R.assoc_real]
  rw [Finset.sum_comm]

/-- Positive normalized multiplicative dimensions exist from the raw rules. -/
lemma exists_positive_dimension :
    ∃ d : ι → ℝ, (∀ x, 0 < d x) ∧ d R.one = 1 ∧
      ∀ x y, ∑ z, (R.N x y z : ℝ) * d z = d x * d y := by
  letI : Nonempty ι := ⟨R.one⟩
  obtain ⟨lam, d, _, hdpos, hdone, hde⟩ :=
    posSymmMatrix_exists_normalized_positive_eigenvector R.dimensionMatrix
      R.dimensionMatrix_symm R.dimensionMatrix_pos R.one
  have hdevec : R.dimensionMatrix *ᵥ d = lam • d := by
    ext i
    exact hde i
  refine ⟨d, hdpos, hdone, ?_⟩
  intro x y
  let w := R.leftMatrix x *ᵥ d
  have hwpos : ∀ i, 0 < w i := by
    intro i
    obtain ⟨j, hj⟩ := R.exists_constituent x i
    change 0 < ∑ k, (R.N x i k : ℝ) * d k
    apply Finset.sum_pos' (fun k _ => mul_nonneg (Nat.cast_nonneg _) (hdpos k).le)
    exact ⟨j, Finset.mem_univ _, mul_pos (by exact_mod_cast hj) (hdpos j)⟩
  have hwevec : R.dimensionMatrix *ᵥ w = lam • w := by
    calc
      R.dimensionMatrix *ᵥ w =
          (R.dimensionMatrix * R.leftMatrix x) *ᵥ d :=
        Matrix.mulVec_mulVec d R.dimensionMatrix (R.leftMatrix x)
      _ = (R.leftMatrix x * R.dimensionMatrix) *ᵥ d := by
        rw [R.leftMatrix_commute x]
      _ = R.leftMatrix x *ᵥ (R.dimensionMatrix *ᵥ d) :=
        (Matrix.mulVec_mulVec d (R.leftMatrix x) R.dimensionMatrix).symm
      _ = R.leftMatrix x *ᵥ (lam • d) := by rw [hdevec]
      _ = lam • w := Matrix.mulVec_smul (R.leftMatrix x) lam d
  have hwe : ∀ i, ∑ j, R.dimensionMatrix i j * w j = lam * w i :=
    fun i => congrFun hwevec i
  obtain ⟨c, _, hc⟩ := posMatrix_positive_eigenspace_one_dim R.dimensionMatrix lam
    R.dimensionMatrix_pos w d hwpos hdpos hwe hde
  have hwone : w R.one = d x := by
    change (∑ j, (R.N x R.one j : ℝ) * d j) = d x
    simp [R.N_one_right]
  have hcx : d x = c := by
    have h := hc R.one
    rwa [hwone, hdone, mul_one] at h
  change w y = d x * d y
  rw [hc y, hcx]

/-- Frobenius–Perron dimensions, including dual invariance, follow from the
finite associative fusion rules without a dimension-existence assumption. -/
theorem exists_fpdim :
    ∃ d : ι → ℝ, (∀ x, 0 < d x) ∧ d R.one = 1 ∧
      (∀ x, d (R.dual x) = d x) ∧
      ∀ x y, ∑ z, (R.N x y z : ℝ) * d z = d x * d y := by
  obtain ⟨d, hdpos, hdone, hmul⟩ := R.exists_positive_dimension
  refine ⟨d, hdpos, hdone, ?_, hmul⟩
  intro x
  have hweighted (a : ι) :
      (∑ i, d i * (∑ j, (R.N a i j : ℝ) * d j)) =
        d a * (∑ i, d i ^ 2) := by
    simp_rw [hmul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have htrans (i j : ι) : R.N (R.dual x) i j = R.N x j i := by
    rw [R.N_dual, R.dual_involutive]
  have hpair : (∑ i, d i * (∑ j, (R.N (R.dual x) i j : ℝ) * d j)) =
      ∑ i, d i * (∑ j, (R.N x i j : ℝ) * d j) := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [htrans]
    ring
  have hnorm : 0 < ∑ i, d i ^ 2 :=
    Finset.sum_pos' (fun _ _ => sq_nonneg _)
      ⟨R.one, Finset.mem_univ _, by rw [hdone]; norm_num⟩
  rw [hweighted, hweighted] at hpair
  exact mul_right_cancel₀ hnorm.ne' hpair

/-- Equip the raw rules with their canonically determined positive dimensions. -/
def toFusionBasis : FusionBasis ι where
  fpdim := Classical.choose R.exists_fpdim
  one := R.one
  dual := R.dual
  N := R.N
  fpdim_pos := (Classical.choose_spec R.exists_fpdim).1
  fpdim_one := (Classical.choose_spec R.exists_fpdim).2.1
  fpdim_dual := (Classical.choose_spec R.exists_fpdim).2.2.1
  dual_involutive := R.dual_involutive
  dual_one := R.dual_one
  N_one_left := R.N_one_left
  N_one_right := R.N_one_right
  N_dual := R.N_dual
  N_right := R.N_right
  fpdim_mul := (Classical.choose_spec R.exists_fpdim).2.2.2

@[simp] lemma toFusionBasis_one : R.toFusionBasis.one = R.one := rfl
@[simp] lemma toFusionBasis_dual (x : ι) : R.toFusionBasis.dual x = R.dual x := rfl
@[simp] lemma toFusionBasis_N (x y z : ι) : R.toFusionBasis.N x y z = R.N x y z := rfl

end FusionRules
end Paper18
