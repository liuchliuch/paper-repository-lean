import Paper22.Basic
import Paper22.Programs
import Paper22.Spectral
import Paper22.CompletionMargins
import Paper22.CompletionSolve
import Paper22.CompletionBounds

/-!
# Effect completion (Lemma 1)

Given effects `Tₓ` on a finite-dimensional Hilbert space with
`A := ∑ₓ qₓ • Tₓ ≤ (1/K) • I` where `K = M + 6` and `M ≥ 2`,
there are effects `Qₓ` with `Tₓ ≤ Qₓ ≤ I` and `∑ₓ qₓ • Qₓ = (1/M) • I`.
-/

open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Matrix

noncomputable section

namespace Paper22

local instance (d : ℕ) : CStarAlgebra (Matrix (Fin d) (Fin d) ℂ) where

/-- Auxiliary operators of the effect-completion construction. -/
def effectC {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  CFC.sqrt (1 - T)

def effectD {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  1 - effectC T

/-- Auxiliary: left/right matrix multiplication is additive in the middle slot. -/
private theorem mul_mid_add {m : ℕ} (C X Y : Matrix (Fin m) (Fin m) ℂ) :
    C * (X + Y) * C = C * X * C + C * Y * C := by
  rw [mul_add, add_mul]

/-- Auxiliary: commuting a real scalar through middle multiplication. -/
private theorem mul_mid_smul {m : ℕ} (C : Matrix (Fin m) (Fin m) ℂ) (t : ℝ)
    (X : Matrix (Fin m) (Fin m) ℂ) :
    C * (t • X) * C = t • (C * X * C) := by
  rw [Matrix.mul_smul, smul_mul_assoc]

/-- The linear map `Φ(X) = ∑ₓ qₓ • (Cₓ * X * Cₓ)`. -/
def phiMap {n m : ℕ} (q : Fin n → ℝ) (C : Fin n → Matrix (Fin m) (Fin m) ℂ) :
    Matrix (Fin m) (Fin m) ℂ →ₗ[ℝ] Matrix (Fin m) (Fin m) ℂ where
  toFun := fun X => ∑ x, q x • (C x * X * C x)
  map_add' := by
    intro X Y
    apply Eq.trans (b := ∑ x, q x • (C x * X * C x + C x * Y * C x))
    · apply Finset.sum_congr rfl
      intro x _
      rw [mul_mid_add]
    apply Eq.trans (b := ∑ x, (q x • (C x * X * C x) + q x • (C x * Y * C x)))
    · apply Finset.sum_congr rfl
      intro x _
      exact smul_add _ _ _
    exact Finset.sum_add_distrib
  map_smul' := by
    intro t X
    apply Eq.trans (b := ∑ x, q x • (t • (C x * X * C x)))
    · apply Finset.sum_congr rfl
      intro x _
      rw [mul_mid_smul]
    apply Eq.trans (b := ∑ x, t • (q x • (C x * X * C x)))
    · apply Finset.sum_congr rfl
      intro x _
      exact smul_comm _ _ _
    rw [Finset.smul_sum, RingHom.id_apply]

/-- The linear map `Ψ(X) = ∑ₓ qₓ • (Dₓ * X * Dₓ)`. -/
def psiMap {n m : ℕ} (q : Fin n → ℝ) (D : Fin n → Matrix (Fin m) (Fin m) ℂ) :
    Matrix (Fin m) (Fin m) ℂ →ₗ[ℝ] Matrix (Fin m) (Fin m) ℂ where
  toFun := fun X => ∑ x, q x • (D x * X * D x)
  map_add' := by
    intro X Y
    apply Eq.trans (b := ∑ x, q x • (D x * X * D x + D x * Y * D x))
    · apply Finset.sum_congr rfl
      intro x _
      rw [mul_mid_add]
    apply Eq.trans (b := ∑ x, (q x • (D x * X * D x) + q x • (D x * Y * D x)))
    · apply Finset.sum_congr rfl
      intro x _
      exact smul_add _ _ _
    exact Finset.sum_add_distrib
  map_smul' := by
    intro t X
    apply Eq.trans (b := ∑ x, q x • (t • (D x * X * D x)))
    · apply Finset.sum_congr rfl
      intro x _
      rw [mul_mid_smul]
    apply Eq.trans (b := ∑ x, t • (q x • (D x * X * D x)))
    · apply Finset.sum_congr rfl
      intro x _
      exact smul_comm _ _ _
    rw [Finset.smul_sum, RingHom.id_apply]

/-- The completion map preserves the real space of Hermitian matrices. -/
theorem phiMap_selfAdjoint {n d : ℕ} (q : Fin n → ℝ)
    (C : Fin n → Matrix (Fin d) (Fin d) ℂ)
    (hC : ∀ x, IsSelfAdjoint (C x)) (X : Matrix (Fin d) (Fin d) ℂ)
    (hX : IsSelfAdjoint X) : IsSelfAdjoint (phiMap q C X) := by
  exact matrix_weighted_conjugate_selfAdjoint q C hC hX

/-- Expanding `Cₓ=I-Dₓ` gives exactly equation (14). -/
theorem phiMap_expansion {n d : ℕ} (q : Fin n → ℝ) (hq1 : ∑ x, q x = 1)
    (C D : Fin n → Matrix (Fin d) (Fin d) ℂ) (hCD : ∀ x, C x = 1 - D x)
    (X : Matrix (Fin d) (Fin d) ℂ) :
    phiMap q C X = X - (∑ x, q x • D x) * X - X * (∑ x, q x • D x) + psiMap q D X := by
  calc
    phiMap q C X = ∑ x, q x • (X - D x * X - X * D x + D x * X * D x) := by
      change (∑ x, q x • (C x * X * C x)) = _
      apply Finset.sum_congr rfl
      intro x _
      rw [hCD x]
      congr 1
      noncomm_ring
    _ = _ := by
      simp only [smul_add, smul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.sum_smul, hq1, one_smul, Matrix.sum_mul, Matrix.mul_sum,
        smul_mul_assoc, Matrix.mul_smul, psiMap, LinearMap.coe_mk, AddHom.coe_mk]

/-- **Lemma 1 (Effect completion).**
Let `M ≥ 2` and `K = M + 6`.  Suppose `q` is a probability distribution on `Fin n`
and `T : Fin n → Matrix (Fin d) (Fin d) ℂ` are effects with
`A := ∑ x, q x • T x ≤ (1 / K) • 1`.
Then there are effects `Q` with `T x ≤ Q x ≤ 1` for all `x` and
`∑ x, q x • Q x = (1 / M) • 1`. -/
theorem lemma_effect_completion
    {n d : ℕ} (M : ℕ) (hM : 2 ≤ M) (K : ℕ) (hK : K = M + 6)
    (q : Fin n → ℝ) (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∑ i, q i = 1)
    (T : Fin n → Matrix (Fin d) (Fin d) ℂ)
    (hT : ∀ x, IsEffect (T x))
    (hA : (∑ x, q x • T x) ≤ (1 / (K : ℝ)) • (1 : Matrix (Fin d) (Fin d) ℂ)) :
    ∃ Q : Fin n → Matrix (Fin d) (Fin d) ℂ,
      (∀ x, IsEffect (Q x)) ∧
      (∀ x, T x ≤ Q x) ∧
      ((∑ x, q x • Q x) = (1 / (M : ℝ)) • (1 : Matrix (Fin d) (Fin d) ℂ)) := by
  classical
  have hm : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hk : (0 : ℝ) < K := by rw [hK]; positivity
  have hmk : (M : ℝ) ≤ K := by rw [hK]; norm_num
  have hk3 : (3 : ℝ) < K := by rw [hK]; exact_mod_cast (show 3 < M + 6 by omega)
  have hki : (1 : ℝ) / K ≤ 1 / M := one_div_le_one_div_of_le hm hmk
  let A : Matrix (Fin d) (Fin d) ℂ := ∑ x, q x • T x
  let C : Fin n → Matrix (Fin d) (Fin d) ℂ := fun x => effectSqrtC (T x)
  let D : Fin n → Matrix (Fin d) (Fin d) ℂ := fun x => effectD' (T x)
  let B : Matrix (Fin d) (Fin d) ℂ := ∑ x, q x • D x
  let H : Matrix (Fin d) (Fin d) ℂ := (1 / (M : ℝ)) • 1 - A
  have hC0 : ∀ x, 0 ≤ C x := fun x => effectSqrtC_nonneg _
  have hCs : ∀ x, IsSelfAdjoint (C x) := fun x => .of_nonneg (hC0 x)
  have hD0 : ∀ x, 0 ≤ D x := fun x => effectD'_nonneg (hT x)
  have hDs : ∀ x, IsSelfAdjoint (D x) := fun x => .of_nonneg (hD0 x)
  have hCD : ∀ x, C x = 1 - D x := by intro x; dsimp [C, D, effectD']; abel
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun x _ => smul_nonneg (hq0 x) (hT x).nonneg
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun x _ => smul_nonneg (hq0 x) (hD0 x)
  have hBA : B ≤ A := by
    apply Finset.sum_le_sum
    intro x _
    exact smul_le_smul_of_nonneg_left (effectD'_le (hT x)) (hq0 x)
  have hS : (∑ x, q x • (D x * D x)) ≤ (1 / (K : ℝ)) • (1 : Matrix (Fin d) (Fin d) ℂ) := by
    apply le_trans (b := A) _ hA
    apply Finset.sum_le_sum
    intro x _
    exact smul_le_smul_of_nonneg_left
      ((effectD'_mul_self_le (hT x)).trans (effectD'_le (hT x))) (hq0 x)
  have hH0 : 0 ≤ H := sub_nonneg.mpr
    (hA.trans (smul_le_smul_of_nonneg_right hki (zero_le_one_matrix d)))
  have hHu : H ≤ (1 / (M : ℝ)) • (1 : Matrix (Fin d) (Fin d) ℂ) := sub_le_self _ hA0
  have hHl : (1 / (M : ℝ) - 1 / (K : ℝ)) • (1 : Matrix (Fin d) (Fin d) ℂ) ≤ H := by
    dsimp [H]
    rw [sub_smul]
    exact sub_le_sub_left hA _
  have hHn : ‖H‖ ≤ 1 / (M : ℝ) := by
    apply (CStarAlgebra.norm_le_iff_le_algebraMap _ (by positivity) hH0).mpr
    simpa only [Algebra.algebraMap_eq_smul_one] using hHu
  have hc0 : (0 : ℝ) ≤ 3 / K := by positivity
  have hc1 : (3 : ℝ) / K < 1 := (div_lt_one hk).mpr hk3
  have hnorm : ∀ X : Matrix (Fin d) (Fin d) ℂ, IsSelfAdjoint X →
      ‖X - phiMap q C X‖ ≤ (3 / (K : ℝ)) * ‖X‖ := by
    intro X hX
    have hex : X - phiMap q C X = B * X + X * B - psiMap q D X := by
      rw [phiMap_expansion q hq1 C D hCD X]
      dsimp [B]
      abel
    rw [hex]
    simpa only [B, psiMap, LinearMap.coe_mk, AddHom.coe_mk, mul_one_div] using
      matrix_completion_defect_norm_le q hq0 D hDs (by positivity : 0 ≤ 1 / (K : ℝ))
        hB0 (hBA.trans hA) hS hX
  obtain ⟨X, hX, hsolve, hclose⟩ := completion_linear_solve (phiMap q C)
    (phiMap_selfAdjoint q C hCs) (3 / K) hc0 hc1 hnorm H (.of_nonneg hH0)
  let e : ℝ := 3 / ((M : ℝ) * ((K : ℝ) - 3))
  have hclose' : ‖X - H‖ ≤ e := by
    apply hclose.trans
    calc (3 / (K : ℝ)) * ‖H‖ / (1 - 3 / (K : ℝ)) ≤
        (3 / (K : ℝ)) * (1 / (M : ℝ)) / (1 - 3 / (K : ℝ)) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hHn hc0) (sub_nonneg.mpr hc1.le)
      _ = e := completion_error_identity hM hK
  have he0 : 0 ≤ e := completion_margin_nonneg hM hK
  have hem : e ≤ 1 / (M : ℝ) - 1 / (K : ℝ) := completion_margin_lower hM hK
  have heu : 1 / (M : ℝ) + e ≤ 1 := completion_margin_upper hM hK
  have hdist := (matrix_selfAdjoint_norm_le_iff
    (hX.sub (.of_nonneg hH0)) he0).mp hclose'
  have hX0 : 0 ≤ X := by
    have hlo : H - e • (1 : Matrix (Fin d) (Fin d) ℂ) ≤ X := by
      have hh := add_le_add_right hdist.1 H
      convert hh using 1 <;> abel
    apply le_trans (b := H - e • (1 : Matrix (Fin d) (Fin d) ℂ)) _ hlo
    exact sub_nonneg.mpr ((smul_le_smul_of_nonneg_right hem (zero_le_one_matrix d)).trans hHl)
  have hX1 : X ≤ 1 := by
    have hhi : X ≤ H + e • (1 : Matrix (Fin d) (Fin d) ℂ) := by
      have hh := add_le_add_right hdist.2 H
      convert hh using 1 <;> abel
    calc X ≤ H + e • (1 : Matrix (Fin d) (Fin d) ℂ) := hhi
      _ ≤ (1 / (M : ℝ)) • (1 : Matrix (Fin d) (Fin d) ℂ) + e • 1 := add_le_add_right hHu _
      _ = (1 / (M : ℝ) + e) • (1 : Matrix (Fin d) (Fin d) ℂ) := (add_smul _ _ _).symm
      _ ≤ 1 := by simpa only [one_smul] using
        smul_le_smul_of_nonneg_right heu (zero_le_one_matrix d)
  refine ⟨fun x => T x + C x * X * C x, ?_, ?_, ?_⟩
  · intro x
    constructor
    · exact add_nonneg (hT x).nonneg ((hCs x).conjugate_nonneg hX0)
    · apply sub_nonneg.mp
      have hconj := (hCs x).conjugate_nonneg (sub_nonneg.mpr hX1)
      have hc2 : C x * C x = 1 - T x := effectSqrtC_mul_self (hT x)
      have heq : 1 - (T x + C x * X * C x) = C x * (1 - X) * C x := by
        rw [mul_sub, sub_mul, mul_one, hc2]
        noncomm_ring
      rw [heq]
      exact hconj
  · intro x
    exact le_add_of_nonneg_right ((hCs x).conjugate_nonneg hX0)
  · simp only [smul_add, Finset.sum_add_distrib]
    change A + phiMap q C X = _
    rw [hsolve]
    dsimp [H]
    abel

end Paper22

end
