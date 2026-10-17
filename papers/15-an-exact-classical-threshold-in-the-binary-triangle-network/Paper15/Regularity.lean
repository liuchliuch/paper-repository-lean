import Paper15.Basic

/-!
# Lemma 6 (Regularity) and the moment identities (18)–(19)

For the exceptional table `F` and three source laws written as
`(x_i, y_i, z_i)` with `z_i = 1 - x_i - y_i`, Section 4 introduces
the quantities `E, T, S, V` of (17) and the moments (18).  This module

* proves the algebraic identity `V = u₀ u₁ u₂ - x₀ x₁ x₂`;
* defines the formal partial derivatives of `E` and `V`;
* proves Lemma 6: on the positive orthant the gradients of `M₁` and `M₃`
  (equivalently of `E` and `V`) are linearly independent;
* records the moment formulas (18) and the vanishing criterion (19).
-/

noncomputable section

namespace Paper15

open Finset Real BigOperators

/-! ## The identity `V = u₀ u₁ u₂ - x₀ x₁ x₂` -/

/-- Equation (17): `V = T + S = u₀ u₁ u₂ - x₀ x₁ x₂`. -/
theorem vQty_eq_u_sub (x y : Fin 3 → ℝ) :
    vQty x y = uOf x y 0 * uOf x y 1 * uOf x y 2 - x 0 * x 1 * x 2 := by
  simp only [vQty, tQty, sQty, uOf]
  ring

/-- The expansion of `T + S` matching the paper's right-hand side. -/
theorem vQty_eq_expand (x y : Fin 3 → ℝ) :
    vQty x y = y 0 * y 1 * y 2
      + (x 0 * y 1 * y 2 + x 1 * y 0 * y 2 + x 2 * y 0 * y 1)
      + (y 0 * x 1 * x 2 + y 1 * x 0 * x 2 + y 2 * x 0 * x 1) := by
  simp only [vQty, tQty, sQty]
  ring

/-! ## Formal partial derivatives of `E` and `V`

The six coordinates are `(x_i, y_i)_{i<3}`.  The complementary indices to
`i : Fin 3` are `i + 1` and `i + 2`.
-/

/-- `∂E/∂x_i = y_j + y_k` where `{j, k}` is the complement of `i`. -/
def eQtyPx (_x y : Fin 3 → ℝ) (i : Fin 3) : ℝ := y (i + 1) + y (i + 2)

/-- `∂E/∂y_i = u_j + u_k`. -/
def eQtyPy (x y : Fin 3 → ℝ) (i : Fin 3) : ℝ := uOf x y (i + 1) + uOf x y (i + 2)

/-- `∂V/∂x_i = u_j u_k - x_j x_k`. -/
def vQtyPx (x y : Fin 3 → ℝ) (i : Fin 3) : ℝ :=
  uOf x y (i + 1) * uOf x y (i + 2) - x (i + 1) * x (i + 2)

/-- `∂V/∂y_i = u_j u_k`. -/
def vQtyPy (x y : Fin 3 → ℝ) (i : Fin 3) : ℝ :=
  uOf x y (i + 1) * uOf x y (i + 2)

/-- Cyclic successor indices in `Fin 3`. -/
@[simp] lemma fin3_zero_add_one : ((0 : Fin 3) + 1) = 1 := by decide
@[simp] lemma fin3_zero_add_two : ((0 : Fin 3) + 2) = 2 := by decide
@[simp] lemma fin3_one_add_one : ((1 : Fin 3) + 1) = 2 := by decide
@[simp] lemma fin3_one_add_two : ((1 : Fin 3) + 2) = 0 := by decide
@[simp] lemma fin3_two_add_one : ((2 : Fin 3) + 1) = 0 := by decide
@[simp] lemma fin3_two_add_two : ((2 : Fin 3) + 2) = 1 := by decide

/-- Concrete value of `∂E/∂y` at `0`. -/
@[simp] lemma eQtyPy_zero (x y : Fin 3 → ℝ) :
    eQtyPy x y 0 = uOf x y 1 + uOf x y 2 := by simp [eQtyPy]

/-- Concrete value of `∂E/∂y` at `1`. -/
@[simp] lemma eQtyPy_one (x y : Fin 3 → ℝ) :
    eQtyPy x y 1 = uOf x y 2 + uOf x y 0 := by simp [eQtyPy]

/-- Concrete value of `∂E/∂y` at `2`. -/
@[simp] lemma eQtyPy_two (x y : Fin 3 → ℝ) :
    eQtyPy x y 2 = uOf x y 0 + uOf x y 1 := by simp [eQtyPy]

/-- Under positivity, `u_i > 0` for all `i`. -/
theorem uOf_pos {x y : Fin 3 → ℝ} (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i) (i : Fin 3) :
    0 < uOf x y i := by
  simp only [uOf]; exact add_pos (hx i) (hy i)

/-- On the positive orthant every `∂E/∂y_i` is strictly positive. -/
theorem eQtyPy_pos {x y : Fin 3 → ℝ} (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i)
    (i : Fin 3) : 0 < eQtyPy x y i := by
  simp only [eQtyPy]
  exact add_pos (uOf_pos hx hy _) (uOf_pos hx hy _)

/-- The gradient of `E` is nonzero on the positive orthant. -/
theorem eQty_grad_ne_zero {x y : Fin 3 → ℝ} (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i) :
    ¬ (∀ i, eQtyPy x y i = 0 ∧ eQtyPx x y i = 0) := by
  intro h
  exact (eQtyPy_pos hx hy 0).ne' (h 0).1

/-! ## Lemma 6 (Regularity)

The paper shows that `∇V = ρ ∇E` is impossible on the positive orthant, which
gives linear independence of the gradients of `M₁ = (2/3)E - 1` and
`M₃ = -1 + 2E - 4V`.
-/

/-- From `u_j u_k = ρ (u_j + u_k)` with all `u` positive one gets `ρ > 0`. -/
theorem rho_pos_of_u {x y : Fin 3 → ℝ} {ρ : ℝ}
    (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i)
    (h : ∀ i, uOf x y (i + 1) * uOf x y (i + 2) =
        ρ * (uOf x y (i + 1) + uOf x y (i + 2))) : 0 < ρ := by
  have u1 : 0 < uOf x y 1 := uOf_pos hx hy 1
  have u2 : 0 < uOf x y 2 := uOf_pos hx hy 2
  have h0 : uOf x y 1 * uOf x y 2 = ρ * (uOf x y 1 + uOf x y 2) := by simpa using h 0
  have hp : 0 < uOf x y 1 * uOf x y 2 := mul_pos u1 u2
  rw [h0] at hp
  exact pos_of_mul_pos_left hp (le_of_lt (add_pos u1 u2))

/-- Equalities `u_j u_k = ρ (u_j + u_k)` for all pairs force `u₀ = u₁ = u₂`. -/
theorem uOf_eq_of_u {x y : Fin 3 → ℝ} {ρ : ℝ}
    (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i)
    (h : ∀ i, uOf x y (i + 1) * uOf x y (i + 2) =
        ρ * (uOf x y (i + 1) + uOf x y (i + 2))) :
    uOf x y 0 = uOf x y 1 ∧ uOf x y 1 = uOf x y 2 := by
  have u0 : 0 < uOf x y 0 := uOf_pos hx hy 0
  have u1 : 0 < uOf x y 1 := uOf_pos hx hy 1
  have u2 : 0 < uOf x y 2 := uOf_pos hx hy 2
  have h0 : uOf x y 1 * uOf x y 2 = ρ * (uOf x y 1 + uOf x y 2) := by simpa using h 0
  have h1 : uOf x y 2 * uOf x y 0 = ρ * (uOf x y 2 + uOf x y 0) := by simpa using h 1
  have h2 : uOf x y 0 * uOf x y 1 = ρ * (uOf x y 0 + uOf x y 1) := by simpa using h 2
  -- (u1 - u0)(u2 - ρ) = 0,  (u2 - u0)(u1 - ρ) = 0,  (u2 - u1)(u0 - ρ) = 0
  have s01 : (uOf x y 1 - uOf x y 0) * (uOf x y 2 - ρ) = 0 := by nlinarith [h0, h1]
  have s02 : (uOf x y 2 - uOf x y 0) * (uOf x y 1 - ρ) = 0 := by nlinarith [h0, h2]
  have s12 : (uOf x y 2 - uOf x y 1) * (uOf x y 0 - ρ) = 0 := by nlinarith [h1, h2]
  rcases mul_eq_zero.mp s01 with e1 | e2
  · -- u1 = u0
    have u1eq : uOf x y 1 = uOf x y 0 := sub_eq_zero.mp e1
    rcases mul_eq_zero.mp s02 with f1 | f2
    · -- u2 = u0
      have u2eq : uOf x y 2 = uOf x y 0 := sub_eq_zero.mp f1
      exact ⟨u1eq.symm, by nlinarith⟩
    · -- u1 = ρ and u1 = u0
      have u1ρ : uOf x y 1 = ρ := sub_eq_zero.mp f2
      rcases mul_eq_zero.mp s12 with g1 | g2
      · -- u2 = u1
        have u2eq : uOf x y 2 = uOf x y 1 := sub_eq_zero.mp g1
        exact ⟨u1eq.symm, u2eq.symm⟩
      · -- u0 = ρ
        have u0ρ : uOf x y 0 = ρ := sub_eq_zero.mp g2
        -- then u0 = u1 = ρ
        exact ⟨u1eq.symm, by nlinarith [u1ρ, u0ρ]⟩
  · -- u2 = ρ
    have u2ρ : uOf x y 2 = ρ := sub_eq_zero.mp e2
    -- then h0: u1 * ρ = ρ (u1 + ρ) ⇒ ρ² = 0 ⇒ ρ = 0, contradicting u2 > 0
    have h0' := h0
    rw [u2ρ] at h0'
    have ρsq : ρ * ρ = 0 := by nlinarith [u1]
    have ρ0 : ρ = 0 := by nlinarith
    nlinarith [u2]

/-- If `∇V = ρ ∇E` then the `u_i` coincide and `ρ = u/2`. -/
theorem rho_eq_half_u {x y : Fin 3 → ℝ} {ρ : ℝ}
    (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i)
    (h : ∀ i, uOf x y (i + 1) * uOf x y (i + 2) =
        ρ * (uOf x y (i + 1) + uOf x y (i + 2))) :
    uOf x y 0 = uOf x y 1 ∧ uOf x y 1 = uOf x y 2 ∧ ρ = uOf x y 0 / 2 := by
  have eqs := uOf_eq_of_u hx hy h
  have u0 : 0 < uOf x y 0 := uOf_pos hx hy 0
  have h2 : uOf x y 0 * uOf x y 1 = ρ * (uOf x y 0 + uOf x y 1) := by simpa using h 2
  refine ⟨eqs.1, eqs.2, ?_⟩
  have h2' : uOf x y 0 * uOf x y 0 = ρ * (uOf x y 0 + uOf x y 0) := by
    rw [← eqs.1] at h2
    exact h2
  -- u² = 2 ρ u, so u = 2 ρ
  have ueq : uOf x y 0 = 2 * ρ := by nlinarith [h2', u0]
  nlinarith [ueq]

/-- The central contradiction of Lemma 6: `∇V = ρ ∇E` is impossible on the
positive orthant. -/
theorem not_grad_proportional {x y : Fin 3 → ℝ} (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i)
    (ρ : ℝ)
    (hyEq : ∀ i, vQtyPy x y i = ρ * eQtyPy x y i)
    (hxEq : ∀ i, vQtyPx x y i = ρ * eQtyPx x y i) : False := by
  -- y-partials give u_j u_k = ρ (u_j + u_k)
  have hu : ∀ i, uOf x y (i + 1) * uOf x y (i + 2) =
      ρ * (uOf x y (i + 1) + uOf x y (i + 2)) := by
    intro i
    simpa [vQtyPy, eQtyPy] using hyEq i
  have ρpos : 0 < ρ := rho_pos_of_u hx hy hu
  obtain ⟨u01, u12, ρeq⟩ := rho_eq_half_u hx hy hu
  have u0 : 0 < uOf x y 0 := uOf_pos hx hy 0
  have u1 : 0 < uOf x y 1 := uOf_pos hx hy 1
  have u2 : 0 < uOf x y 2 := uOf_pos hx hy 2
  have ueq02 : uOf x y 0 = uOf x y 2 := u01.trans u12
  -- x-partials at i = 0: u1 u2 - x1 x2 = ρ (y1 + y2)
  have h0 : uOf x y 1 * uOf x y 2 - x 1 * x 2 = ρ * (y 1 + y 2) := by
    have := hxEq 0
    simpa [vQtyPx, eQtyPx] using this
  -- all u equal to u0
  have u1eq : uOf x y 1 = uOf x y 0 := u01.symm
  have u2eq : uOf x y 2 = uOf x y 0 := ueq02.symm
  have y1eq : y 1 = uOf x y 0 - x 1 := by
    have : uOf x y 0 = x 1 + y 1 := by rw [← u1eq]; simp [uOf]
    linarith
  have y2eq : y 2 = uOf x y 0 - x 2 := by
    have : uOf x y 0 = x 2 + y 2 := by rw [← u2eq]; simp [uOf]
    linarith
  have x1pos : 0 < x 1 := hx 1
  have x2pos : 0 < x 2 := hx 2
  have x1ltu : x 1 < uOf x y 0 := by
    have : x 1 < uOf x y 1 := by simp only [uOf]; linarith [hy 1]
    linarith [u1eq]
  have x2ltu : x 2 < uOf x y 0 := by
    have : x 2 < uOf x y 2 := by simp only [uOf]; linarith [hy 2]
    linarith [u2eq]
  -- Key equality 2 x1 x2 = u0 (x1 + x2)
  have key : 2 * x 1 * x 2 = uOf x y 0 * (x 1 + x 2) := by
    rw [u1eq, u2eq, y1eq, y2eq, ρeq] at h0
    nlinarith [u0]
  -- But 0 < x1(u0 - x2) + x2(u0 - x1) = u0(x1+x2) - 2 x1 x2
  have pos : 0 < uOf x y 0 * (x 1 + x 2) - 2 * x 1 * x 2 := by
    have eq :
        uOf x y 0 * (x 1 + x 2) - 2 * x 1 * x 2
          = x 1 * (uOf x y 0 - x 2) + x 2 * (uOf x y 0 - x 1) := by ring
    rw [eq]
    exact add_pos (mul_pos x1pos (by linarith)) (mul_pos x2pos (by linarith))
  linarith [key, pos]

/-- Lemma 6 (Regularity).  The gradients of `M₁ = (2/3)E - 1` and
`M₃ = -1 + 2E - 4V` with respect to the six coordinates `(x_i, y_i)` are
linearly independent whenever `x_i > 0` and `y_i > 0` for all `i`. -/
theorem lemma6_grad_independent {x y : Fin 3 → ℝ}
    (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i) :
    ¬ ∃ α β : ℝ, (α ≠ 0 ∨ β ≠ 0) ∧
      (∀ i, (α : ℝ) * ((2:ℝ) / 3 * eQtyPx x y i) +
          β * (2 * eQtyPx x y i - 4 * vQtyPx x y i) = 0) ∧
      (∀ i, (α : ℝ) * ((2:ℝ) / 3 * eQtyPy x y i) +
          β * (2 * eQtyPy x y i - 4 * vQtyPy x y i) = 0) := by
  intro hex
  obtain ⟨α, β, hne, hx0, hy0⟩ := hex
  by_cases hβ : β = 0
  · -- then α ≠ 0 and α * (2/3) eQtyPy = 0 forces eQtyPy = 0
    subst hβ
    have hα : α ≠ 0 := by
      cases hne with
      | inl h => exact h
      | inr h => exact absurd rfl h
    have hpy0 : α * ((2:ℝ) / 3 * eQtyPy x y 0) = 0 := by
      have := hy0 0
      simpa using this
    have h23 : ((2:ℝ) / 3 * eQtyPy x y 0) = 0 := by
      rcases mul_eq_zero.mp hpy0 with h | h
      · exact absurd h hα
      · exact h
    have hpy0' : eQtyPy x y 0 = 0 := by
      rcases mul_eq_zero.mp h23 with h | h
      · exact absurd h (by norm_num)
      · exact h
    exact (eQtyPy_pos hx hy 0).ne' hpy0'
  · -- β ≠ 0: extract ρ such that ∇V = ρ ∇E
    have h4β : (4:ℝ) * β ≠ 0 := mul_ne_zero (by norm_num) hβ
    -- ρ = (2α/3 + 2β) / (4β)
    set ρ : ℝ := (2 * α / 3 + 2 * β) / (4 * β) with hρdef
    have hpy : ∀ i, vQtyPy x y i = ρ * eQtyPy x y i := by
      intro i
      have h1 : α * ((2:ℝ) / 3 * eQtyPy x y i) +
          β * (2 * eQtyPy x y i - 4 * vQtyPy x y i) = 0 := hy0 i
      have key : (2 * α / 3 + 2 * β) * eQtyPy x y i = 4 * β * vQtyPy x y i := by
        ring_nf at h1 ⊢
        linarith
      have : vQtyPy x y i = ((2 * α / 3 + 2 * β) / (4 * β)) * eQtyPy x y i := by
        field_simp [h4β]
        nlinarith [key]
      rw [hρdef]
      exact this
    have hpx : ∀ i, vQtyPx x y i = ρ * eQtyPx x y i := by
      intro i
      have h1 : α * ((2:ℝ) / 3 * eQtyPx x y i) +
          β * (2 * eQtyPx x y i - 4 * vQtyPx x y i) = 0 := hx0 i
      have key : (2 * α / 3 + 2 * β) * eQtyPx x y i = 4 * β * vQtyPx x y i := by
        ring_nf at h1 ⊢
        linarith
      have : vQtyPx x y i = ((2 * α / 3 + 2 * β) / (4 * β)) * eQtyPx x y i := by
        field_simp [h4β]
        nlinarith [key]
      rw [hρdef]
      exact this
    exact not_grad_proportional hx hy ρ hpy hpx

/-- Restatement of Lemma 6 in the `E, V` form used in the paper's proof. -/
theorem lemma6 {x y : Fin 3 → ℝ} (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i) :
    ¬ ∃ ρ : ℝ, (∀ i, vQtyPy x y i = ρ * eQtyPy x y i) ∧
        (∀ i, vQtyPx x y i = ρ * eQtyPx x y i) := by
  rintro ⟨ρ, hy0, hx0⟩
  exact not_grad_proportional hx hy ρ hy0 hx0

/-! ## Moments (18) and the vanishing criterion (19)

With `E, T, S, V` of (17), the moments of the exceptional table are

  `M₁ = (2/3) E - 1`,
  `M₂ = 1 - (4/3) E + (4/3)(3T + S)`,
  `M₃ = -1 + 2E - 4V`.
-/

/-- `M₁` of (18) in terms of `E`. -/
def m1Of (E : ℝ) : ℝ := (2 : ℝ) / 3 * E - 1

/-- `M₂` of (18) in terms of `E, T, S`. -/
def m2Of (E T S : ℝ) : ℝ := 1 - (4 : ℝ) / 3 * E + (4 : ℝ) / 3 * (3 * T + S)

/-- `M₃` of (18) in terms of `E, V`. -/
def m3Of (E V : ℝ) : ℝ := -1 + 2 * E - 4 * V

/-- The moments of (18) for the quantities `E, T, S, V` of (17). -/
def momentsOf (x y : Fin 3 → ℝ) : AggregateMoments where
  M1 := m1Of (eQty x y)
  M2 := m2Of (eQty x y) (tQty x y) (sQty x y)
  M3 := m3Of (eQty x y) (vQty x y)

/-- Equation (19): `M₁ = M₃ = 0` iff `E = 3/2` and `V = 1/2`. -/
theorem vanishing_iff_eq (E V : ℝ) :
    m1Of E = 0 ∧ m3Of E V = 0 ↔ E = 3 / 2 ∧ V = 1 / 2 := by
  constructor
  · rintro ⟨h1, h3⟩
    have eE : E = 3 / 2 := by
      simp only [m1Of] at h1
      nlinarith
    have eV : V = 1 / 2 := by
      simp only [m3Of] at h3
      nlinarith [eE]
    exact ⟨eE, eV⟩
  · rintro ⟨eE, eV⟩
    refine ⟨?_, ?_⟩
    · simp only [m1Of, eE]; ring
    · simp only [m3Of, eE, eV]; ring

/-- The same criterion specialized to the quantities of (17). -/
theorem vanishing_iff_eQty_vQty (x y : Fin 3 → ℝ) :
    m1Of (eQty x y) = 0 ∧ m3Of (eQty x y) (vQty x y) = 0 ↔
      eQty x y = 3 / 2 ∧ vQty x y = 1 / 2 :=
  vanishing_iff_eq _ _

/-- `M₁` and `M₃` as explicit affine combinations of `E` and `V`. -/
theorem m1Of_eq (E : ℝ) : m1Of E = (2 : ℝ) / 3 * E - 1 := rfl

theorem m3Of_eq (E V : ℝ) : m3Of E V = -1 + 2 * E - 4 * V := rfl

/-- From (18), `M₁ = 0` iff `E = 3/2`. -/
theorem m1Of_eq_zero_iff (E : ℝ) : m1Of E = 0 ↔ E = 3 / 2 := by
  constructor <;> intro h
  · simp only [m1Of] at h; nlinarith
  · simp only [m1Of, h]; ring

/-! ## Source laws as functions `Fin 3 → ℝ`

For the three sources the paper writes laws `(x_i, y_i, z_i)` with
`z_i = 1 - x_i - y_i`.  We record the corresponding functions on `Fin 3`
used by `detMoments`.
-/

/-- `z_i = 1 - x_i - y_i`. -/
def zOf (x y : Fin 3 → ℝ) (i : Fin 3) : ℝ := 1 - x i - y i

/-- Source `i`'s law as a function `Fin 3 → ℝ`. -/
def lawOf (x y : Fin 3 → ℝ) (i : Fin 3) : Fin 3 → ℝ :=
  fun j => if j = 0 then x i else if j = 1 then y i else zOf x y i

@[simp] lemma lawOf_zero (x y : Fin 3 → ℝ) (i : Fin 3) : lawOf x y i 0 = x i := by
  simp [lawOf]

@[simp] lemma lawOf_one (x y : Fin 3 → ℝ) (i : Fin 3) : lawOf x y i 1 = y i := by
  simp [lawOf]

@[simp] lemma lawOf_two (x y : Fin 3 → ℝ) (i : Fin 3) : lawOf x y i 2 = zOf x y i := by
  have h0 : (2 : Fin 3) ≠ 0 := by decide
  have h1 : (2 : Fin 3) ≠ 1 := by decide
  simp [lawOf, h0, h1]

lemma lawOf_sum (x y : Fin 3 → ℝ) (i : Fin 3) :
    ∑ j, lawOf x y i j = x i + y i + zOf x y i := by
  rw [Fin.sum_univ_three, lawOf_zero, lawOf_one, lawOf_two]

/-- Values of the exceptional table `F` on the nine pairs. -/
lemma exceptionalTable_eq (j k : Fin 3) :
    DetTriangle.exceptionalTable j k =
      if (j = 0 ∧ k = 1) ∨ (j = 1 ∧ k = 0) ∨ (j = 1 ∧ k = 1) then (1 : ℝ) else -1 :=
  rfl

end Paper15
