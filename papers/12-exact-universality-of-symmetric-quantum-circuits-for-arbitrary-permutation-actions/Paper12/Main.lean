import Paper12.CircuitTools
import Paper12.PauliExpand
import Paper12.Selector
import Paper12.BlockEncoding
import Paper12.Amplify

/-!
Resource estimates and the empty-register case of Theorem 1.1.
The complete elementary circuit construction and general equivalence are
proved in Universality.lean.
-/
noncomputable section
namespace Paper12
open Matrix Complex Classical
variable {X : Type*} [Fintype X]

def resourceM (U : Op X) : ℕ := coeffCard (pauliCoeff U)
def resourceLambda (U : Op X) : ℝ := coeffMass (pauliCoeff U)
def sizeBound (U : Op X) : ℕ :=
  8192 * Fintype.card X * (resourceM U + 1) * (Nat.ceil (resourceLambda U) + 1)
def workspaceBound (U : Op X) : ℕ := resourceM U + 5

theorem theorem_1_1_necessity {Γ : Subgroup (X ≃ X)} {U : Op X} {nW s : ℕ}
    (h : HasCleanSymmetricCircuit Γ U nW s) : Equivariant Γ U := by
  obtain ⟨W, hW, C, hclean, _, _, ⟨hsym⟩⟩ := h
  exact lemma_2_2 hsym hclean

theorem abs_le_one_of_mass (α : Coeffs X)
    (h2 : ∑ w : PWord X, Complex.abs (α w) ^ 2 = 1) (w : PWord X) :
    Complex.abs (α w) ≤ 1 := by
  have h := Finset.single_le_sum (s := Finset.univ)
    (f := fun v => Complex.abs (α v) ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ w)
  rw [h2] at h
  nlinarith [Complex.abs_nonneg (α w)]

/-- The normalization case has exactly one nonzero Pauli coefficient. -/
theorem mass_eq_one_unique (α : Coeffs X) (hmass : coeffMass α = 1)
    (h2 : ∑ w : PWord X, Complex.abs (α w) ^ 2 = 1) :
    ∃! w : PWord X, α w ≠ 0 := by
  have hle := abs_le_one_of_mass α h2
  have hs1 : ∑ w ∈ coeffSupport α, Complex.abs (α w) = 1 := hmass
  have hs2 : ∑ w ∈ coeffSupport α, Complex.abs (α w) ^ 2 = 1 := by
    rw [← h2]
    apply Finset.sum_subset (Finset.subset_univ _)
    intro w _ hw
    have hz : α w = 0 := by simpa [coeffSupport] using hw
    simp [hz]
  have hz : ∑ w ∈ coeffSupport α, (Complex.abs (α w) - Complex.abs (α w) ^ 2) = 0 := by
    rw [Finset.sum_sub_distrib, hs1, hs2]; ring
  have hn : ∀ w ∈ coeffSupport α,
      0 ≤ Complex.abs (α w) - Complex.abs (α w) ^ 2 := by
    intro w _
    nlinarith [hle w, Complex.abs_nonneg (α w)]
  have heach := (Finset.sum_eq_zero_iff_of_nonneg hn).mp hz
  have hone : ∀ w ∈ coeffSupport α, Complex.abs (α w) = 1 := by
    intro w hw
    have ha : 0 < Complex.abs (α w) := abs_pos_of_mem_support α hw
    have ht := heach w hw
    nlinarith
  have hc : (coeffSupport α).card = 1 := by
    have hcount : ((coeffSupport α).card : ℝ) = 1 := by
      simpa only [Finset.sum_congr rfl hone, Finset.sum_const, nsmul_eq_mul,
        mul_one] using hs1
    exact_mod_cast hcount
  obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hc
  refine ⟨w, ?_, ?_⟩
  · have hmem : w ∈ coeffSupport α := by rw [hw]; simp
    simpa [coeffSupport] using hmem
  · intro v hv
    have hmem : v ∈ coeffSupport α := by simpa [coeffSupport] using hv
    simpa [hw] using hmem

theorem pauli_support_bound (U : Op X) : resourceM U ≤ 4 ^ Fintype.card X := by
  have hcard : Fintype.card PSym = 4 := by decide
  calc resourceM U ≤ Fintype.card (PWord X) := Finset.card_le_univ _
    _ = 4 ^ Fintype.card X := by rw [Fintype.card_fun, hcard]

theorem resourceM_pos (U : Op X) (hU : Uᴴ * U = 1) : 0 < resourceM U := by
  have hm : 1 ≤ resourceLambda U := (coeff_mass_bounds U hU).1
  by_contra hn
  have hz : coeffSupport (pauliCoeff U) = ∅ :=
    Finset.card_eq_zero.mp (Nat.eq_zero_of_not_pos hn)
  simp [resourceLambda, coeffMass, hz] at hm
  norm_num at hm

theorem sizeBound_le (U : Op X) (hU : Uᴴ * U = 1) :
    (sizeBound U : ℝ) ≤
      49152 * (Fintype.card X : ℝ) * resourceM U * resourceLambda U := by
  have hm : (1 : ℝ) ≤ resourceM U := by exact_mod_cast resourceM_pos U hU
  have hl : 1 ≤ resourceLambda U := (coeff_mass_bounds U hU).1
  have hc := (Nat.ceil_lt_add_one (by linarith : 0 ≤ resourceLambda U)).le
  have hc2 : (Nat.ceil (resourceLambda U) : ℝ) + 1 ≤ 3 * resourceLambda U := by linarith
  have hm2 : (resourceM U : ℝ) + 1 ≤ 2 * resourceM U := by linarith
  unfold sizeBound
  push_cast
  calc 8192 * (Fintype.card X : ℝ) * (resourceM U + 1) * (Nat.ceil (resourceLambda U) + 1)
      ≤ 8192 * (Fintype.card X : ℝ) * (2 * resourceM U) * (3 * resourceLambda U) := by
        gcongr
    _ = _ := by ring

/-- The explicit size expression has the paper's worst-case O(n 8^n) growth.
Universality.lean supplies a realizing circuit with this measured size bound. -/
theorem sizeBound_exponential (U : Op X) (hU : Uᴴ * U = 1) :
    (sizeBound U : ℝ) ≤ 49152 * (Fintype.card X : ℝ) * (8 : ℝ) ^ Fintype.card X := by
  have hm : (resourceM U : ℝ) ≤ (4 : ℝ) ^ Fintype.card X := by
    exact_mod_cast pauli_support_bound U
  have hs : Real.sqrt (resourceM U : ℝ) ≤ (2 : ℝ) ^ Fintype.card X := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    have hp : ((2 : ℝ) ^ Fintype.card X) ^ 2 = (4 : ℝ) ^ Fintype.card X := by
      rw [← pow_mul, mul_comm (Fintype.card X) 2, pow_mul]
      norm_num
    rwa [hp]
  have hl : resourceLambda U ≤ (2 : ℝ) ^ Fintype.card X :=
    (coeff_mass_bounds U hU).2.trans hs
  calc (sizeBound U : ℝ)
      ≤ 49152 * (Fintype.card X : ℝ) * resourceM U * resourceLambda U := sizeBound_le U hU
    _ ≤ 49152 * (Fintype.card X : ℝ) * (4 : ℝ) ^ Fintype.card X *
        (2 : ℝ) ^ Fintype.card X := by
      gcongr
      exact (coeff_mass_bounds U hU).1.trans' (by norm_num)
    _ = _ := by rw [mul_assoc, ← mul_pow]; norm_num

/-- The single computational basis vector of an empty active register. -/
def zeroBasis (X : Type*) : Basis X := fun _ => 0

theorem empty_op_eq_scalar [IsEmpty X] (U : Op X) :
    U = (U (zeroBasis X) (zeroBasis X)) • (1 : Op X) := by
  ext i j
  have hi : i = zeroBasis X := Subsingleton.elim _ _
  have hj : j = zeroBasis X := Subsingleton.elim _ _
  subst i; subst j
  simp

theorem empty_unitary_entry [IsEmpty X] {U : Op X} (hU : Uᴴ * U = 1) :
    star (U (zeroBasis X) (zeroBasis X)) * U (zeroBasis X) (zeroBasis X) = 1 := by
  have h := congrFun (congrFun hU (zeroBasis X)) (zeroBasis X)
  simp only [Matrix.mul_apply, Matrix.one_apply_eq] at h
  rw [Finset.sum_eq_single (zeroBasis X)] at h
  · simpa only [Matrix.conjTranspose_apply] using h
  · intro b _ hb
    exact (hb (Subsingleton.elim _ _)).elim
  · intro hb
    exact (hb (Finset.mem_univ _)).elim

/-- The empty-register case, for any finite empty wire type. -/
theorem theorem_1_1_of_isEmpty [IsEmpty X] (Γ : Subgroup (X ≃ X))
    (U : Op X) (hU : Uᴴ * U = 1) : HasCleanSymmetricCircuit Γ U 1 1 := by
  let z := U (zeroBasis X) (zeroBasis X)
  have hz : star z * z = 1 := empty_unitary_entry hU
  refine ⟨Fin 1, inferInstance, phaseCircuit z hz, ?_, by simp, ?_, ?_⟩
  · rw [empty_op_eq_scalar U]
    exact phaseCircuit_clean z hz
  · simp [phaseCircuit]
  · exact phaseCircuit_symmetric Γ z hz

theorem theorem_1_1_empty (Γ : Subgroup ((Empty : Type) ≃ Empty))
    (U : Op Empty) (hU : Uᴴ * U = 1) : HasCleanSymmetricCircuit Γ U 1 1 :=
  theorem_1_1_of_isEmpty Γ U hU

end Paper12
