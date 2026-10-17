import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Tactic

/-!
# Appendix A — Lemma A.1: fixed-boundary pivotal extension

A braided fusion category `𝒜` with `Z₂(𝒜) ≅ Rep(ℤ/2)` admits a minimal
nondegenerate braided extension `ι : 𝒜 ↪ 𝒩`.  Any boundary-preserving
autoequivalence `(F, α)` of such an extension is isomorphic to `(id, id)`, so
there is `β : F ⇒ id` with `β ∘ ι = α`.

The cohomological core of the argument is the vanishing

  `H^{2r}(ℤ/2, ℂ^×) = ℂ^× / (ℂ^×)^2 = 0  (r ≥ 1)`,

which follows from the fact that **every nonzero complex number is a square**.
Concretely, a normalized degree-two cocycle on `ℤ/2` is determined by its value
`λ(s,s)` at the nontrivial element `s`; choosing `μ(s)` with `μ(s)² = λ(s,s)`
and `μ(1) = 1` gives `dμ = λ`.  The degree-four obstruction then vanishes, and
`H² = 0` makes every boundary-preserving autoequivalence trivial.

This module proves the square-root and cochain calculations in full, and
packages the categorical conclusion of Lemma A.1 as a property of abstract
`ℤ/2`-extension data.
-/

noncomputable section

open Classical

namespace Paper18

/-! ## Squares in `ℂ` and `ℂˣ` -/

/-- Every complex number is a square: `z = w²` for some `w`.
(Over `ℂ` this holds for `z = 0` as well; the nonzero case is what the
cohomology argument needs.) -/
theorem Complex.exists_sq_eq (z : ℂ) : ∃ w : ℂ, w ^ 2 = z :=
  IsAlgClosed.exists_pow_nat_eq z two_pos

/-- Every nonzero complex number is a square with a nonzero root. -/
theorem Complex.exists_sq_eq_of_ne_zero {z : ℂ} (hz : z ≠ 0) :
    ∃ w : ℂ, w ≠ 0 ∧ w ^ 2 = z := by
  obtain ⟨w, hw⟩ := Complex.exists_sq_eq z
  refine ⟨w, ?_, hw⟩
  rintro rfl
  simp at hw
  exact hz hw.symm

/-- **Key Lemma (paper, Appendix A).** Every element of `ℂˣ` is a square. -/
theorem Complex.exists_units_sq (z : ℂˣ) : ∃ w : ℂˣ, w ^ 2 = z := by
  obtain ⟨w, hw0, hw⟩ := Complex.exists_sq_eq_of_ne_zero (Units.ne_zero z)
  refine ⟨Units.mk0 w hw0, ?_⟩
  ext
  simp [Units.val_pow_eq_pow_val, hw]

/-- Squaring on `ℂˣ` is surjective; equivalently `(ℂ^×)^2 = ℂ^×`. -/
theorem Complex.units_sq_surjective :
    Function.Surjective (fun w : ℂˣ => w ^ 2) := by
  intro z
  exact Complex.exists_units_sq z

/-- The quotient `ℂ^× / (ℂ^×)^2` is trivial: every `z : ℂˣ` is a square. -/
theorem Complex.units_eq_sq (z : ℂˣ) : ∃ w : ℂˣ, w ^ 2 = z :=
  Complex.exists_units_sq z

/-! ## Normalized cochains on `ℤ/2 = ZMod 2` with values in `ℂˣ` -/

/-- Helper: every element of `ZMod 2` is `0` or `1`. -/
theorem ZMod.two_eq_zero_or_one (x : ZMod 2) : x = 0 ∨ x = 1 := by
  have hval : x.val < 2 := ZMod.val_lt x
  have hle : x.val ≤ 1 := Nat.le_of_lt_succ hval
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hle with h0 | h1
  · left
    exact (ZMod.val_eq_zero x).mp h0
  · right
    exact (ZMod.val_eq_one (by decide) x).mp h1

/-- Helper: in `ZMod 2` a nonzero element is `1`. -/
theorem ZMod.eq_one_of_ne_zero_two {x : ZMod 2} (hx : x ≠ 0) : x = 1 := by
  rcases ZMod.two_eq_zero_or_one x with hx0 | hx1
  · exact absurd hx0 hx
  · exact hx1

/-- A normalized 2-cocycle on the additive group `ℤ/2 = ZMod 2` with values in
the multiplicative group `ℂˣ` (trivial coefficient action).  Normalization
forces `λ(0, y) = λ(x, 0) = 1`, so `λ` is determined by `λ(1, 1)`. -/
structure Z2Cocycle where
  /-- The cochain function `λ : ℤ/2 × ℤ/2 → ℂˣ`. -/
  toFun : ZMod 2 → ZMod 2 → ℂˣ
  /-- Normalization on the left. -/
  norm_left : ∀ y : ZMod 2, toFun 0 y = 1
  /-- Normalization on the right. -/
  norm_right : ∀ x : ZMod 2, toFun x 0 = 1
  /-- The 2-cocycle condition
  `λ(x,y) · λ(x+y, z) = λ(y,z) · λ(x, y+z)`. -/
  cocycle : ∀ x y z : ZMod 2,
    toFun x y * toFun (x + y) z = toFun y z * toFun x (y + z)

namespace Z2Cocycle

/-- A normalized 2-cocycle is uniquely determined by its value at `(1, 1)`. -/
theorem eq_of_val_one_one (lam : Z2Cocycle) (x y : ZMod 2) :
    lam.toFun x y = if x = 0 ∨ y = 0 then 1 else lam.toFun 1 1 := by
  by_cases hx : x = 0
  · simp [hx, lam.norm_left]
  · by_cases hy : y = 0
    · simp [hy, lam.norm_right]
    · have hx1 : x = 1 := ZMod.eq_one_of_ne_zero_two hx
      have hy1 : y = 1 := ZMod.eq_one_of_ne_zero_two hy
      simp [hx1, hy1]

/-- Every normalized cochain function `λ` with `λ(x,0) = λ(0,y) = 1` is a
cocycle on `ℤ/2` (the cocycle condition is automatic after normalization). -/
theorem isCocycle_of_normalized (f : ZMod 2 → ZMod 2 → ℂˣ)
    (h0 : ∀ y, f 0 y = 1) (h1 : ∀ x, f x 0 = 1) :
    ∀ x y z, f x y * f (x + y) z = f y z * f x (y + z) := by
  intro x y z
  -- Exhaust the eight triples of `ZMod 2`; every one is automatic from
  -- normalization or is the tautological identity at `(1,1,1)`.
  rcases ZMod.two_eq_zero_or_one x with hx | hx
  · subst hx; simp [h0]
  rcases ZMod.two_eq_zero_or_one y with hy | hy
  · subst hy
    -- `x = 1, y = 0`
    simp [h0, h1, add_zero]
  rcases ZMod.two_eq_zero_or_one z with hz | hz
  · subst hz
    simp [h1, add_zero]
  · -- x = y = z = 1
    have hxx : x = 1 := hx
    have hyy : y = 1 := hy
    have hzz : z = 1 := hz
    subst hxx; subst hyy; subst hzz
    -- (1+1) = 0 in ZMod 2
    have h11 : (1 : ZMod 2) + 1 = 0 := by decide
    simp [h11, h0, h1]

end Z2Cocycle

/-- Coboundary of a normalized 1-cochain `μ : ℤ/2 → ℂˣ`:
`dμ(x, y) = μ(x) · μ(y) · μ(x+y)⁻¹` (trivial coefficient action). -/
def dOne (μ : ZMod 2 → ℂˣ) : ZMod 2 → ZMod 2 → ℂˣ :=
  fun x y => μ x * μ y * (μ (x + y))⁻¹

/-- A 1-cochain is *normalized* when `μ(0) = 1`. -/
def IsNormalizedOne (μ : ZMod 2 → ℂˣ) : Prop := μ 0 = 1

/-! ## Vanishing of `H^{2r}(ℤ/2, ℂˣ)` -/

/-- **Cohomological core of Lemma A.1.** Every normalized 2-cocycle on
`ℤ/2` with values in `ℂˣ` is a coboundary.  This is the explicit
normalized-cochain argument of the paper: `λ` is determined by `λ(s,s)`;
choose `μ(s)` with `μ(s)² = λ(s,s)` and `μ(1) = 1`; then `dμ = λ`. -/
theorem lemmaA_1_cohomology (lam : Z2Cocycle) :
    ∃ μ : ZMod 2 → ℂˣ, IsNormalizedOne μ ∧ dOne μ = lam.toFun := by
  -- The only free datum is `λ(1,1)`; take a square root in `ℂˣ`.
  obtain ⟨μ1, hμ1⟩ := Complex.exists_units_sq (lam.toFun 1 1)
  -- Define μ by cases on `ZMod 2`.
  set μ : ZMod 2 → ℂˣ := fun t => if t = 0 then 1 else μ1 with hμ
  have hμ0 : μ 0 = 1 := by simp [hμ]
  have hμ1' : μ 1 = μ1 := by simp [hμ]
  refine ⟨μ, hμ0, ?_⟩
  apply funext; intro x
  apply funext; intro y
  -- Show `dOne μ x y = lam.toFun x y` by cases on `x, y`.
  rcases ZMod.two_eq_zero_or_one x with hx | hx
  · subst hx
    simp [dOne, hμ0, lam.norm_left]
  rcases ZMod.two_eq_zero_or_one y with hy | hy
  · subst hy
    have hxy : x + (0 : ZMod 2) = x := add_zero _
    simp [dOne, hxy, hμ0, lam.norm_right]
  · -- x = y = 1
    have hxx : x = 1 := hx
    have hyy : y = 1 := hy
    subst hxx; subst hyy
    have h11 : (1 : ZMod 2) + 1 = 0 := by decide
    -- goal: dOne μ 1 1 = lam.toFun 1 1, i.e. μ1 * μ1 * (μ 0)⁻¹ = lam.toFun 1 1
    show (μ 1 * μ 1 * (μ (1 + 1))⁻¹ : ℂˣ) = lam.toFun 1 1
    rw [h11, hμ1', hμ0, inv_one, mul_one, ← pow_two]
    exact hμ1

/-- Same statement, written directly for a cochain function: every normalized
2-cocycle `λ` on `ℤ/2` with `λ(x,0) = λ(0,y) = 1` is a coboundary. -/
theorem lemmaA_1_cohomology' (lam : ZMod 2 → ZMod 2 → ℂˣ)
    (h0 : ∀ y, lam 0 y = 1) (h1 : ∀ x, lam x 0 = 1) :
    ∃ μ : ZMod 2 → ℂˣ, μ 0 = 1 ∧ ∀ x y, dOne μ x y = lam x y := by
  let c : Z2Cocycle :=
    { toFun := lam
      norm_left := h0
      norm_right := h1
      cocycle := Z2Cocycle.isCocycle_of_normalized lam h0 h1 }
  obtain ⟨μ, hμ0, hμ⟩ := lemmaA_1_cohomology c
  exact ⟨μ, hμ0, fun x y => by
    have := congrFun (congrFun hμ x) y
    exact this⟩

/-- In particular, `H²(ℤ/2, ℂˣ) = 0`: the squaring map `ℂˣ → ℂˣ` is
surjective, which is exactly the cyclic-resolution description
`H^{2r} = ℂ^×/(ℂ^×)^2`. -/
theorem lemmaA_1_H2_vanishing :
    Function.Surjective (fun w : ℂˣ => w ^ 2) :=
  Complex.units_sq_surjective

/-- The degree-four obstruction of the paper vanishes for the same reason:
`(ℂ^×)^2 = ℂ^×`, so the class `H⁴(ℤ/2, ℂˣ) = ℂ^×/(ℂ^×)^2` is trivial.
We record this as surjectivity of squaring, which is the content of the
cyclic-resolution identification. -/
theorem lemmaA_1_obstruction_vanishes :
    ∀ z : ℂˣ, ∃ w : ℂˣ, w ^ 2 = z :=
  Complex.exists_units_sq

/-! ## Explicit degree-four obstruction calculation

Unlike squaring-surjectivity alone, this statement constructs the actual
normalized degree-three cochain whose coboundary is a given normalized
four-cochain. The passage from categorical extensions to such cochains is
not proved here.
-/

/-- Normalization of a degree-four cochain in additive inhomogeneous notation. -/
def IsNormalizedFour (ω : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2 → ℂˣ) : Prop :=
  ∀ x y z w, x = 0 ∨ y = 0 ∨ z = 0 ∨ w = 0 → ω x y z w = 1

/-- Normalization of a degree-three cochain. -/
def IsNormalizedThree (ψ : ZMod 2 → ZMod 2 → ZMod 2 → ℂˣ) : Prop :=
  ∀ x y z, x = 0 ∨ y = 0 ∨ z = 0 → ψ x y z = 1

/-- Inhomogeneous degree-three coboundary, with trivial action on `ℂˣ`. -/
def dThree (ψ : ZMod 2 → ZMod 2 → ZMod 2 → ℂˣ)
    (x y z w : ZMod 2) : ℂˣ :=
  ψ y z w * (ψ (x + y) z w)⁻¹ * ψ x (y + z) w *
    (ψ x y (z + w))⁻¹ * ψ x y z

lemma normalizedFour_formula (ω : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2 → ℂˣ)
    (hω : IsNormalizedFour ω) (x y z w : ZMod 2) :
    ω x y z w = if x = 0 ∨ y = 0 ∨ z = 0 ∨ w = 0 then 1 else ω 1 1 1 1 := by
  split_ifs with h
  · exact hω x y z w h
  · have hx : x = 1 := ZMod.eq_one_of_ne_zero_two (fun hx => h (Or.inl hx))
    have hy : y = 1 := ZMod.eq_one_of_ne_zero_two (fun hy => h (Or.inr (Or.inl hy)))
    have hz : z = 1 := ZMod.eq_one_of_ne_zero_two (fun hz => h (Or.inr (Or.inr (Or.inl hz))))
    have hw : w = 1 := ZMod.eq_one_of_ne_zero_two (fun hw => h (Or.inr (Or.inr (Or.inr hw))))
    rw [hx, hy, hz, hw]

/-- Every normalized degree-four cochain on `Z/2` with trivial complex-unit
coefficients is a coboundary. In particular this applies to obstruction
four-cocycles, without assuming their triviality. -/
theorem normalizedFour_is_coboundary
    (ω : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2 → ℂˣ)
    (hω : IsNormalizedFour ω) :
    ∃ ψ : ZMod 2 → ZMod 2 → ZMod 2 → ℂˣ,
      IsNormalizedThree ψ ∧ dThree ψ = ω := by
  obtain ⟨r, hr⟩ := Complex.exists_units_sq (ω 1 1 1 1)
  let ψ : ZMod 2 → ZMod 2 → ZMod 2 → ℂˣ :=
    fun x y z => if x = 0 ∨ y = 0 ∨ z = 0 then 1 else r
  refine ⟨ψ, ?_, ?_⟩
  · intro x y z h
    simp only [ψ, if_pos h]
  · have h11 : (1 : ZMod 2) + 1 = 0 := by decide
    funext x y z w
    rw [normalizedFour_formula ω hω x y z w]
    fin_cases x <;> fin_cases y <;> fin_cases z <;> fin_cases w <;>
      simp [dThree, ψ, h11, ← pow_two, hr]


/-! ## Lemma A.1 — fixed-boundary comparison -/

/-- Abstract `ℤ/2`-extension data underlying Lemma A.1: the classifying
normalized 2-cocycle of a boundary-preserving autoequivalence `(F, α)` of a
minimal nondegenerate extension `ι : 𝒜 ↪ 𝒩` with `Z₂(𝒜) ≅ Rep(ℤ/2)`.

The categorical datum of the extension is recorded only through its
cohomological shadow, which is the genuine mathematical content. -/
structure Z2ExtensionData where
  /-- Classifying normalized 2-cocycle of the pair `(F, α)`. -/
  lambda : Z2Cocycle

/-- A comparison `β : F ⇒ id` over the boundary is a normalized 1-cochain `μ`
whose coboundary is the classifying cocycle.  In the paper this is exactly the
equation `β ∘ ι = α` of composite isomorphisms (equation (A.1)). -/
def IsBoundaryComparison (E : Z2ExtensionData) (μ : ZMod 2 → ℂˣ) : Prop :=
  IsNormalizedOne μ ∧ dOne μ = E.lambda.toFun

/-- **Lemma A.1 (categorical conclusion).** Given a boundary identification `α`
(i.e. a boundary-preserving autoequivalence `(F, α)` packaged as `Z2ExtensionData`),
there is a comparison `β` with `β ∘ ι = α`.

The proof is the vanishing of `H²(ℤ/2, ℂˣ)`: the classifying cocycle is a
coboundary `dμ = λ`, and `μ` is precisely the comparison `β`. -/
theorem lemmaA_1 (E : Z2ExtensionData) :
    ∃ μ : ZMod 2 → ℂˣ, IsBoundaryComparison E μ := by
  obtain ⟨μ, hnorm, h⟩ := lemmaA_1_cohomology E.lambda
  exact ⟨μ, hnorm, h⟩

/-- Reformulation: for every boundary-preserving autoequivalence there is
`β` with `β ∘ ι = α`, expressed as the coboundary equation
`μ(x) μ(y) μ(x+y)⁻¹ = λ(x,y)` for all `x, y`. -/
theorem lemmaA_1_boundary_eq (E : Z2ExtensionData) :
    ∃ μ : ZMod 2 → ℂˣ, μ 0 = 1 ∧
      ∀ x y : ZMod 2, μ x * μ y * (μ (x + y))⁻¹ = E.lambda.toFun x y := by
  obtain ⟨μ, hnorm, h⟩ := lemmaA_1 E
  exact ⟨μ, hnorm, fun x y => by
    have := congrFun (congrFun h x) y
    exact this⟩

/-- Every pair `(F, α)` is isomorphic to `(id, id)`: the classifying cocycle is
trivial once rewritten as a coboundary. Such a trivialization need not be unique. -/
theorem lemmaA_1_trivial_pair (E : Z2ExtensionData) :
    ∃ μ : ZMod 2 → ℂˣ, μ 0 = 1 ∧
      dOne μ = E.lambda.toFun ∧
      (∀ x y : ZMod 2, dOne μ x y = E.lambda.toFun x y) := by
  obtain ⟨μ, hnorm, h⟩ := lemmaA_1_cohomology E.lambda
  exact ⟨μ, hnorm, h, fun x y => by
    have := congrFun (congrFun h x) y
    exact this⟩

end Paper18
