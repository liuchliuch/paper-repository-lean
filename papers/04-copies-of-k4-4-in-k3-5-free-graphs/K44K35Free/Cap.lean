import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic

/-!
# Cap property (Lemma 3)

We work over an arbitrary field `F` together with a nonsquare `α`.
The point set of the paper is

  `S_f = {(x, y, z, x², y² − α z² + f(x)) | x, y, z ∈ F}`  in  `F⁵`.

**Lemma 3 (Cap property).**  No three points of `S_f` are collinear.

The proof is the affine second-difference argument of the paper:
if three distinct points of `S_f` are collinear, write them as
`p`, `p+h`, `p+lam h` with `h ≠ 0` and `lam ∉ {0,1}`.  The `u = x²`
coordinate forces `h_x = 0`; the `v = y² − α z² + f(x)` coordinate
then forces `h_y² − α h_z² = 0`, which for nonsquare `α` gives
`h_y = h_z = 0`, contradicting `h ≠ 0`.
-/

namespace K44K35Free

/-! ## Algebraic core -/

/-- Nonsquare predicate: `α` is not a square in the monoid. -/
def IsNonsquare {F : Type*} [Monoid F] [Pow F ℕ] (α : F) : Prop :=
  ∀ a : F, a ^ 2 ≠ α

/-- If `lam (lam-1) t = 0`, `lam ≠ 0`, `lam ≠ 1`, then `t = 0`. -/
lemma mul_lam_cancel {F : Type*} [Field F] {lam t : F}
    (h : lam * (lam - 1) * t = 0) (h0 : lam ≠ 0) (h1 : lam ≠ 1) : t = 0 := by
  have hne : lam * (lam - 1) ≠ 0 := mul_ne_zero h0 (sub_ne_zero.mpr h1)
  exact Or.resolve_left (mul_eq_zero.1 h) hne

/-- `a² − α b² = 0` and `α` nonsquare imply `a = 0` and `b = 0`. -/
lemma nonsquare_zero_of_sq_sub {F : Type*} [Field F] {α a b : F}
    (hα : IsNonsquare α) (h : a ^ 2 - α * b ^ 2 = 0) : a = 0 ∧ b = 0 := by
  by_cases hb : b = 0
  · subst hb
    have ha : a ^ 2 = 0 := by
      have : a ^ 2 - α * 0 ^ 2 = 0 := h
      linear_combination this
    exact ⟨pow_eq_zero ha, rfl⟩
  · exfalso
    have hαb : a ^ 2 = α * b ^ 2 := by
      linear_combination h
    have hsq : α = (a / b) ^ 2 := by
      rw [div_eq_mul_inv, mul_pow]
      have hbb : b ^ 2 * b⁻¹ ^ 2 = 1 := by
        rw [← mul_pow, mul_inv_cancel₀ hb, one_pow]
      have : α = α * (b ^ 2 * b⁻¹ ^ 2) := by rw [hbb, mul_one]
      rw [this, ← mul_assoc, hαb]
    exact hα (a / b) hsq.symm

/-- **Second difference in the `u = x²` coordinate.**
If `(x + lam hx)² = x² + lam ((x + hx)² - x²)` and `lam ∉ {0,1}`, then `hx = 0`. -/
lemma u_coord_forces_hx_zero {F : Type*} [Field F]
    {x hx lam : F} (h : (x + lam * hx) ^ 2 = x ^ 2 + lam * ((x + hx) ^ 2 - x ^ 2))
    (h0 : lam ≠ 0) (h1 : lam ≠ 1) : hx = 0 := by
  have heq : (x + lam * hx) ^ 2 - x ^ 2 = lam * ((x + hx) ^ 2 - x ^ 2) := by
    linear_combination h
  have hL : (x + lam * hx) ^ 2 - x ^ 2 = 2 * x * (lam * hx) + (lam * hx) ^ 2 := by
    ring
  have hR : (x + hx) ^ 2 - x ^ 2 = 2 * x * hx + hx ^ 2 := by ring
  have hcancel : (lam * hx) ^ 2 - lam * hx ^ 2 = 0 := by
    linear_combination heq - hL + lam * hR
  have hfact : lam * (lam - 1) * hx ^ 2 = 0 := by
    linear_combination hcancel
  have h2 : hx ^ 2 = 0 := mul_lam_cancel hfact h0 h1
  exact pow_eq_zero h2

/-- **Second difference in the `v` coordinate.**
If the `v`-coordinates satisfy the affine relation with parameter
`lam ∉ {0,1}`, then `hy² − α hz² = 0`. -/
lemma v_coord_forces_norm_zero {F : Type*} [Field F] {α : F}
    {y hy z hz lam : F} {f : F → F} {x : F}
    (h : (y + lam * hy) ^ 2 - α * (z + lam * hz) ^ 2 + f x
        = y ^ 2 - α * z ^ 2 + f x
          + lam * ((y + hy) ^ 2 - α * (z + hz) ^ 2 + f x
                 - (y ^ 2 - α * z ^ 2 + f x)))
    (h0 : lam ≠ 0) (h1 : lam ≠ 1) :
    hy ^ 2 - α * hz ^ 2 = 0 := by
  have h2 : (y + lam * hy) ^ 2 - α * (z + lam * hz) ^ 2
      = y ^ 2 - α * z ^ 2
        + lam * ((y + hy) ^ 2 - α * (z + hz) ^ 2 - (y ^ 2 - α * z ^ 2)) := by
    linear_combination h
  have hL : (y + lam * hy) ^ 2 = y ^ 2 + 2 * y * (lam * hy) + (lam * hy) ^ 2 := by ring
  have hR : (y + hy) ^ 2 = y ^ 2 + 2 * y * hy + hy ^ 2 := by ring
  have hLz : (z + lam * hz) ^ 2 = z ^ 2 + 2 * z * (lam * hz) + (lam * hz) ^ 2 := by ring
  have hRz : (z + hz) ^ 2 = z ^ 2 + 2 * z * hz + hz ^ 2 := by ring
  have h3 : lam ^ 2 * (hy ^ 2 - α * hz ^ 2) = lam * (hy ^ 2 - α * hz ^ 2) := by
    have key : (y + lam * hy) ^ 2 - α * (z + lam * hz) ^ 2
        - (y ^ 2 - α * z ^ 2)
        - lam * ((y + hy) ^ 2 - α * (z + hz) ^ 2 - (y ^ 2 - α * z ^ 2)) = 0 := by
      linear_combination h2
    rw [hL, hR, hLz, hRz] at key
    ring_nf at key ⊢
    linear_combination key
  have h4 : lam * (lam - 1) * (hy ^ 2 - α * hz ^ 2) = 0 := by
    linear_combination h3
  exact mul_lam_cancel h4 h0 h1

/-! ## Point set and cap property -/

/-- The point set `S_f ⊆ F⁵` as a function of the affine parameters `(x,y,z)`. -/
def sPoint {F : Type*} [Ring F] (α : F) (f : F → F)
    (x y z : F) : F × F × F × F × F :=
  (x, y, z, x ^ 2, y ^ 2 - α * z ^ 2 + f x)

/-- **Lemma 3 (Cap property), core form.**
For every field `F`, every nonsquare `α`, every `f : F → F`, and every
parameters with `lam ∉ {0,1}` and `(hx,hy,hz) ≠ 0`, the three points

  `sPoint α f x y z`,
  `sPoint α f (x+hx) (y+hy) (z+hz)`,
  `sPoint α f (x+lam hx) (y+lam hy) (z+lam hz)`

do not satisfy the `u`- and `v`-affine relations of collinearity. -/
lemma cap_property_core {F : Type*} [Field F] (α : F) (f : F → F)
    (hα : IsNonsquare α)
    (x y z hx hy hz lam : F)
    (h0 : lam ≠ 0) (h1 : lam ≠ 1) (hh : (hx, hy, hz) ≠ (0, 0, 0)) :
    ¬ ((x + lam * hx) ^ 2 = x ^ 2 + lam * ((x + hx) ^ 2 - x ^ 2) ∧
       (y + lam * hy) ^ 2 - α * (z + lam * hz) ^ 2 + f (x + lam * hx)
         = y ^ 2 - α * z ^ 2 + f x
           + lam * ((y + hy) ^ 2 - α * (z + hz) ^ 2 + f (x + hx)
                  - (y ^ 2 - α * z ^ 2 + f x))) := by
  rintro ⟨hu, hv⟩
  have hhx : hx = 0 := u_coord_forces_hx_zero hu h0 h1
  have hv' : (y + lam * hy) ^ 2 - α * (z + lam * hz) ^ 2 + f x
      = y ^ 2 - α * z ^ 2 + f x
        + lam * ((y + hy) ^ 2 - α * (z + hz) ^ 2 + f x
               - (y ^ 2 - α * z ^ 2 + f x)) := by
    rw [hhx, mul_zero, add_zero] at hv
    exact hv
  have hnorm : hy ^ 2 - α * hz ^ 2 = 0 :=
    v_coord_forces_norm_zero (f := f) (x := x) hv' h0 h1
  have hpair := nonsquare_zero_of_sq_sub hα hnorm
  exact hh (by simp [hhx, hpair.1, hpair.2])

/-- **Lemma 3 (Cap property).**
No three points of `S_f` are collinear.  Expressed in the paper's affine
parametrization: if three points of `S_f` lie on an affine line with
parameter `lam ∉ {0,1}`, then the direction `h = (hx,hy,hz)` vanishes.
Together with the uniqueness of the affine parametrization of three distinct
collinear points, this is exactly Lemma 3. -/
theorem lemma_3_cap_property {F : Type*} [Field F] (α : F) (f : F → F)
    (hα : IsNonsquare α)
    (x y z hx hy hz lam : F)
    (h0 : lam ≠ 0) (h1 : lam ≠ 1) (hh : (hx, hy, hz) ≠ (0, 0, 0)) :
    ¬ ((x + lam * hx) ^ 2 = x ^ 2 + lam * ((x + hx) ^ 2 - x ^ 2) ∧
       (y + lam * hy) ^ 2 - α * (z + lam * hz) ^ 2 + f (x + lam * hx)
         = y ^ 2 - α * z ^ 2 + f x
           + lam * ((y + hy) ^ 2 - α * (z + hz) ^ 2 + f (x + hx)
                  - (y ^ 2 - α * z ^ 2 + f x))) :=
  cap_property_core α f hα x y z hx hy hz lam h0 h1 hh

end K44K35Free
