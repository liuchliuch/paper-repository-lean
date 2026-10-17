import K44K35Free.Cap
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Fintype.Option

/-! Exact cardinality of the anisotropic quadratic norm fibers used in Proposition 4.
The proof is elementary: a rational parametrization counts the norm-one conic,
a quadratic-polynomial pigeonhole argument produces a norm-minus-one point,
and multiplication by that point identifies the two fibers. -/

namespace K44K35Free

open Polynomial

variable {F : Type*} [Field F]

/-- The actual pairs whose quadratic norm is `c`. -/
def NormFiber (α c : F) := {p : F × F // p.1 ^ 2 - α * p.2 ^ 2 = c}

lemma norm_denominator_ne_zero {α : F} (hα : IsNonsquare α) (t : F) :
    1 - α * t ^ 2 ≠ 0 := by
  intro h
  by_cases ht : t = 0
  · simp [ht] at h
  · apply hα t⁻¹
    have hh : α * t ^ 2 = 1 := by linear_combination -h
    field_simp
    linear_combination -hh

/-- Rational parametrization of the norm-one conic, with its one point at infinity
in the slope parameter supplied by `none`. -/
noncomputable def normOneParam {α : F} (hα : IsNonsquare α) :
    Option F → NormFiber α 1
  | none => ⟨(-1, 0), by simp⟩
  | some t => ⟨((1 + α * t ^ 2) / (1 - α * t ^ 2),
      2 * t / (1 - α * t ^ 2)), by
      dsimp
      field_simp [norm_denominator_ne_zero hα t]
      ring⟩

lemma normOne_x_eq_neg_one {α : F} (hα : IsNonsquare α)
    (p : NormFiber α 1) (hx : p.val.1 = -1) : p.val.2 = 0 := by
  have hα0 : α ≠ 0 := fun h => hα 0 (by simp [h])
  have h := p.property
  rw [hx] at h
  have : α * p.val.2 ^ 2 = 0 := by linear_combination -h
  exact pow_eq_zero ((mul_eq_zero.mp this).resolve_left hα0)

/-- The inverse slope parameter. -/
noncomputable def normOneSlope {α : F} (p : NormFiber α 1) : Option F := by
  classical
  exact if p.val.1 = -1 then none else some (p.val.2 / (p.val.1 + 1))

lemma normOneSlope_param {α : F} (hα : IsNonsquare α) (h2 : (2 : F) ≠ 0)
    (t : Option F) : normOneSlope (normOneParam hα t) = t := by
  cases t with
  | none => simp [normOneSlope, normOneParam]
  | some t =>
      have hd := norm_denominator_ne_zero hα t
      have hx : (1 + α * t ^ 2) / (1 - α * t ^ 2) ≠ -1 := by
        intro h
        have := (div_eq_iff hd).mp h
        apply h2
        linear_combination this
      simp only [normOneSlope, normOneParam, hx, ↓reduceIte, Option.some.injEq]
      have hadd : (1 + α * t ^ 2) / (1 - α * t ^ 2) + 1 =
          2 / (1 - α * t ^ 2) := by
        field_simp
        ring
      rw [hadd]
      have hdn : 1 - t ^ 2 * α ≠ 0 := by simpa [mul_comm] using hd
      field_simp [hd, hdn]

lemma normOneParam_slope {α : F} (hα : IsNonsquare α) (h2 : (2 : F) ≠ 0)
    (p : NormFiber α 1) : normOneParam hα (normOneSlope p) = p := by
  apply Subtype.ext
  by_cases hx : p.val.1 = -1
  · have hy := normOne_x_eq_neg_one hα p hx
    simp only [normOneSlope, hx, ↓reduceIte, normOneParam]
    exact Prod.ext hx.symm hy.symm
  · have hx' : p.val.1 + 1 ≠ 0 := by
      intro h
      apply hx
      linear_combination h
    have hn := p.property
    have hd : 1 - α * (p.val.2 / (p.val.1 + 1)) ^ 2 =
        2 / (p.val.1 + 1) := by
      field_simp
      linear_combination hn
    simp only [normOneSlope, hx, ↓reduceIte, normOneParam]
    rw [hd]
    apply Prod.ext
    · dsimp
      field_simp
      linear_combination -hn
    · dsimp
      field_simp

/-- The norm-one conic is a projective line as a finite set. -/
noncomputable def normOneEquiv {α : F} (hα : IsNonsquare α) (h2 : (2 : F) ≠ 0) :
    Option F ≃ NormFiber α 1 where
  toFun := normOneParam hα
  invFun := normOneSlope
  left_inv := normOneSlope_param hα h2
  right_inv := normOneParam_slope hα h2

lemma card_norm_one [Fintype F] {α : F} (hα : IsNonsquare α)
    (h2 : (2 : F) ≠ 0) : Nat.card (NormFiber α 1) = Fintype.card F + 1 := by
  rw [← Nat.card_congr (normOneEquiv hα h2), Nat.card_eq_fintype_card]
  simp

/-- A nonsquare quadratic norm over an odd finite field represents minus one. -/
lemma exists_norm_neg_one [Fintype F] {α : F} (hα : IsNonsquare α)
    (hF : ringChar F ≠ 2) : ∃ a b : F, a ^ 2 - α * b ^ 2 = -1 := by
  have hα0 : α ≠ 0 := fun h => hα 0 (by simp [h])
  have hg : (C (-α) * X ^ 2 + 1 : F[X]).degree = 2 := by
    rw [degree_add_eq_left_of_degree_lt]
    · rw [degree_C_mul (neg_ne_zero.mpr hα0), degree_X_pow]
      norm_num
    · rw [degree_one, degree_C_mul (neg_ne_zero.mpr hα0), degree_X_pow]
      norm_num
  obtain ⟨a, b, hab⟩ := FiniteField.exists_root_sum_quadratic
    (f := (X ^ 2 : F[X])) (g := C (-α) * X ^ 2 + 1)
    (degree_X_pow 2) hg (FiniteField.odd_card_of_char_ne_two hF)
  refine ⟨a, b, ?_⟩
  simp only [eval_add, eval_mul, eval_pow, eval_X, eval_C, eval_one] at hab
  linear_combination hab

/-- Multiplication by a norm-minus-one point identifies the norm-one and
norm-minus-one fibers. Its inverse is multiplication by the negative conjugate. -/
noncomputable def normNegOneEquiv {α a b : F} (hab : a ^ 2 - α * b ^ 2 = -1) :
    NormFiber α 1 ≃ NormFiber α (-1) where
  toFun p := ⟨(a * p.val.1 + α * b * p.val.2, b * p.val.1 + a * p.val.2), by
    have h := p.property
    dsimp
    linear_combination (a ^ 2 - α * b ^ 2) * h + hab⟩
  invFun p := ⟨(-a * p.val.1 + α * b * p.val.2, b * p.val.1 - a * p.val.2), by
    have h := p.property
    dsimp
    linear_combination (a ^ 2 - α * b ^ 2) * h - hab⟩
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext <;> dsimp
    · linear_combination -p.val.1 * hab
    · linear_combination -p.val.2 * hab
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext <;> dsimp
    · linear_combination -p.val.1 * hab
    · linear_combination -p.val.2 * hab

/-- Equation (10) has exactly `q+1` solutions, proved for the actual quadratic equation. -/
theorem card_norm_neg_one [Fintype F] {α : F} (hα : IsNonsquare α)
    (hF : ringChar F ≠ 2) : Nat.card (NormFiber α (-1)) = Fintype.card F + 1 := by
  obtain ⟨a, b, hab⟩ := exists_norm_neg_one hα hF
  rw [← Nat.card_congr (normNegOneEquiv hab)]
  exact card_norm_one hα (Ring.two_ne_zero hF)

end K44K35Free
