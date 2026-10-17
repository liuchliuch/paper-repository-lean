import Paper18.Fusion.Braided
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

/-!
# Lemma 2.1 (Lacabanne) — the twist constraint on the pivotal slope

Let `C` be a nondegenerate braided fusion category with pivotal structure `j`
and balancing `θ`.  For a simple `X` write

* `d_X = jdim X`  (pivotal dimension),
* `n_X = d_X d_{X*} = ndim X`  (quantum dimension),
* `γ_X = d_X / d_{X*} = gamma X`  (slope).

The slope defines a tensor automorphism of the identity, and by the monodromy
isomorphism (2.3) it is represented by monodromy with a unique invertible
object `t`:

* (2.1) `c_{X,t} c_{t,X} = γ_X id_{t ⊗ X}` for every simple `X`;
* (2.2) `θ_{t^{-1}} = 1`.

This module proves the paper's Gauss-sum argument for (2.2) and the uniqueness
of `t` in (2.1), against the combinatorial fusion interface.

Categorical input that the interface cannot express (tensoring with an
invertible object; the Hopf-link formula for `S`) is recorded as explicit
hypotheses in the structures `InvertibleTensor` and `HopfLinkIdentity`, never
as custom axioms.  `BraidedData.S_invertible` and `BalancingData.theta_dual`
supply the remaining ingredients.

## Main declarations

* `Paper18.gaussSum`: `τ = ∑_X θ_X n_X`.
* `Paper18.lemma2_1_twist`: any invertible `t` whose monodromy is the slope
  satisfies `θ_{t^{-1}} = θ(dual t) = 1`.
* `Paper18.lemma2_1_unique`: `t` is unique among invertibles satisfying (2.1).
-/

noncomputable section

open Classical

universe u

open scoped BigOperators

namespace Paper18

section Lacabanne

variable {ι : Type u} [Fintype ι] {B : FusionBasis ι}
  {J : PivotalData B} {θ : BalancingData J} {C : BraidedData B}

/-! ## Gauss sum -/

/-- Gauss sum `τ = ∑_X θ_X n_X` of the balancing data. -/
def gaussSum (J : PivotalData B) (θ : BalancingData J) : ℂ :=
  ∑ x, θ.theta x * J.ndim x

/-- Unfolding of `gaussSum`. -/
lemma gaussSum_def (J : PivotalData B) (θ : BalancingData J) :
    gaussSum J θ = ∑ x, θ.theta x * J.ndim x := rfl

/-- Equation (2.1): monodromy of every simple `x` with `t` equals the slope
`γ_x`.  Equivalently `c_{X,t} c_{t,X} = γ_X id_{t ⊗ X}`. -/
def SlopeIsMonodromy (C : BraidedData B) (J : PivotalData B) (t : ι) : Prop :=
  ∀ x : ι, C.monodromy x t = J.gamma x

/-! ## Tensoring with an invertible object

For an invertible simple `t` we have `t^{-1} = t* = dual t`.  Tensoring with
`t^{-1}` permutes the simple objects, preserves `n_X`, and the balancing
formula for the twist reads `θ_{t^{-1} ⊗ X} = θ_{t^{-1}} θ_X monodromy(t^{-1},X)`.
-/

/-- Combinatorial shadow of tensoring with an invertible simple `t`:
the permutation `x ↦ t^{-1} ⊗ x` of simples, together with the two
compatibilities used in the Gauss-sum argument (preservation of `n_X` and
the balancing formula for the twist), and the inverse relation for
monodromy with `t^{-1} = dual t`. -/
structure InvertibleTensor (B : FusionBasis ι) (C : BraidedData B)
    (J : PivotalData B) (θ : BalancingData J) (t : ι) where
  /-- The simple `t^{-1} ⊗ x` (with `t^{-1} = dual t`). -/
  mu : ι → ι
  /-- Tensoring with an invertible object permutes the simple objects. -/
  mu_bijective : Function.Bijective mu
  /-- Tensoring with an invertible object preserves `n_X = d_X d_{X*}`. -/
  ndim_mu : ∀ x : ι, J.ndim (mu x) = J.ndim x
  /-- Monodromy with `t^{-1} = dual t` is the inverse of monodromy with `t`. -/
  monodromy_dual : ∀ x : ι, C.monodromy (B.dual t) x = (C.monodromy t x)⁻¹
  /-- Balancing formula for twists along `mu`:
  `θ_{t^{-1} ⊗ x} = θ_{t^{-1}} · θ_x · monodromy(t^{-1}, x)`. -/
  theta_mu : ∀ x : ι, θ.theta (mu x) =
    θ.theta (B.dual t) * θ.theta x * C.monodromy (B.dual t) x

/-- Pivotal Hopf-link identity driving the nonvanishing of the Gauss sum:
`∑_X θ_X d_{X*} S_{X,Y} = τ · d_Y / θ_Y`.  This is the paper's computation
from the balancing formula and Frobenius reciprocity; `S` is not tied to the
fusion rules in `BraidedData`, so the identity is an explicit hypothesis. -/
def HopfLinkIdentity (C : BraidedData B) (J : PivotalData B)
    (θ : BalancingData J) : Prop :=
  ∀ y : ι, ∑ x, θ.theta x * J.jdim (B.dual x) * C.S x y
    = gaussSum J θ * J.jdim y * (θ.theta y)⁻¹

/-! ## Reindexing identities -/

/-- Reindexing the Gauss sum by duality and applying `θ_{X*} = θ_X γ_X^{-1}`,
`n_{X*} = n_X` yields `τ = ∑_X θ_X γ_X^{-1} n_X`. -/
lemma gaussSum_eq_theta_gamma_inv (J : PivotalData B) (θ : BalancingData J) :
    gaussSum J θ = ∑ x, θ.theta x * (J.gamma x)⁻¹ * J.ndim x := by
  classical
  have hre : ∑ x, θ.theta x * J.ndim x
      = ∑ x, θ.theta (B.dual x) * J.ndim (B.dual x) := by
    let e : ι ≃ ι :=
      { toFun := B.dual, invFun := B.dual
        left_inv := B.dual_involutive, right_inv := B.dual_involutive }
    exact (Equiv.sum_comp e (fun x => θ.theta x * J.ndim x)).symm
  rw [gaussSum_def, hre]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [θ.theta_dual, J.ndim_dual]

/-- The dual-reindexed Gauss sum equals the original. -/
lemma sum_theta_gamma_inv_eq (J : PivotalData B) (θ : BalancingData J) :
    (∑ x, θ.theta x * (J.gamma x)⁻¹ * J.ndim x) = ∑ x, θ.theta x * J.ndim x :=
  (gaussSum_eq_theta_gamma_inv J θ).symm

/-! ## Nonvanishing of the Gauss sum -/

/-- The vector `(θ_X d_{X*})_X` is not the zero function: already at the unit
it equals `1`. -/
lemma gaussWeight_ne_zero (J : PivotalData B) (θ : BalancingData J) :
    (fun x : ι => θ.theta x * J.jdim (B.dual x)) ≠ 0 := by
  intro h
  have h1 := congrFun h B.one
  rw [θ.theta_one, B.dual_one, J.jdim_one, one_mul] at h1
  exact one_ne_zero h1

/-- `τ ≠ 0`: the Hopf-link identity writes the `S`-transform of the nonzero
vector `(θ_X d_{X*})_X` as `τ · d_Y / θ_Y`, and `S` is invertible. -/
lemma gaussSum_ne_zero (hH : HopfLinkIdentity C J θ) :
    gaussSum J θ ≠ 0 := by
  classical
  set v : ι → ℂ := fun x => θ.theta x * J.jdim (B.dual x) with hv
  -- The `S`-transform of `v` is given by the Hopf-link identity.
  have hw_eq : ∀ y : ι, (∑ x, C.S x y * v x)
      = gaussSum J θ * J.jdim y * (θ.theta y)⁻¹ := by
    intro y
    have hy := hH y
    simp only [v]
    convert hy using 1
    refine Finset.sum_congr rfl (fun x _ => ?_)
    ring
  -- `v ≠ 0`.
  have hv_ne : v ≠ 0 := fun h => gaussWeight_ne_zero J θ (hv.symm.trans h)
  -- The `S`-transform is bijective, so it sends `v` to a nonzero function.
  have hinj : Function.Injective
      (fun (u : ι → ℂ) => fun y => ∑ x, C.S x y * u x) :=
    C.S_invertible.injective
  have hw_ne : (fun y => ∑ x, C.S x y * v x) ≠ 0 := by
    intro h
    have htr0 : (fun (u : ι → ℂ) => fun y => ∑ x, C.S x y * u x) 0
        = (0 : ι → ℂ) := by
      funext y
      simp
    have htrv : (fun (u : ι → ℂ) => fun y => ∑ x, C.S x y * u x) v
        = (0 : ι → ℂ) := h
    exact hv_ne (hinj (htrv.trans htr0.symm))
  -- So some component is nonzero, forcing `τ ≠ 0`.
  obtain ⟨y, hy⟩ : ∃ y, (∑ x, C.S x y * v x) ≠ 0 := by
    by_contra hall
    apply hw_ne
    funext y
    by_contra hne
    exact hall ⟨y, hne⟩
  have hwy := hw_eq y
  rw [hwy] at hy
  have hassoc : gaussSum J θ * J.jdim y * (θ.theta y)⁻¹
      = gaussSum J θ * (J.jdim y * (θ.theta y)⁻¹) := mul_assoc _ _ _
  rw [hassoc] at hy
  exact (mul_ne_zero_iff.mp hy).1

/-! ## Twists along `mu` -/

/-- Combining (2.1) with the balancing formula:
`θ_{t^{-1} ⊗ x} = θ_{t^{-1}} θ_x γ_x^{-1}`. -/
lemma theta_mu_eq_gamma_inv (t : ι) (A : InvertibleTensor B C J θ t)
    (hmono : SlopeIsMonodromy C J t) (x : ι) :
    θ.theta (A.mu x) = θ.theta (B.dual t) * θ.theta x * (J.gamma x)⁻¹ := by
  have hmd : C.monodromy (B.dual t) x = (J.gamma x)⁻¹ := by
    rw [A.monodromy_dual, C.monodromy_symm, hmono x]
  rw [A.theta_mu x, hmd]

/-- Termwise identity for the reindexing `X ↦ t^{-1} ⊗ X`:
`θ_{t^{-1}⊗X} n_{t^{-1}⊗X} = θ_{t^{-1}} θ_X γ_X^{-1} n_X`. -/
lemma theta_ndim_mu_eq (t : ι) (A : InvertibleTensor B C J θ t)
    (hmono : SlopeIsMonodromy C J t) (x : ι) :
    θ.theta (A.mu x) * J.ndim (A.mu x)
      = θ.theta (B.dual t) * (θ.theta x * (J.gamma x)⁻¹ * J.ndim x) := by
  rw [theta_mu_eq_gamma_inv t A hmono, A.ndim_mu]
  ring

/-! ## Main theorems -/

/-- **Lemma 2.1 (Lacabanne), twist constraint (2.2).**
Let `t` be invertible with monodromy equal to the slope (2.1).  Then
`θ_{t^{-1}} = 1`, i.e. `θ (dual t) = 1`.

The proof is the paper's Gauss-sum argument.  Reindexing `τ` by duality gives
`τ = ∑_X θ_X γ_X^{-1} n_X`; reindexing by `X ↦ t^{-1} ⊗ X` together with the
balancing formula gives `τ = θ_{t^{-1}} τ`.  The Hopf-link identity and the
invertibility of `S` yield `τ ≠ 0`, so `θ_{t^{-1}} = 1`.

`ht` records that `t` is invertible (as in the paper statement); the proof
only uses the action `A` of `t^{-1}`, which presupposes invertibility. -/
theorem lemma2_1_twist (t : ι) (ht : B.IsInvertible t)
    (hmono : SlopeIsMonodromy C J t)
    (A : InvertibleTensor B C J θ t)
    (hH : HopfLinkIdentity C J θ) :
    θ.theta (B.dual t) = 1 := by
  classical
  have _ := ht
  have hτ : gaussSum J θ ≠ 0 := gaussSum_ne_zero hH
  -- Reindexing `τ` by `x ↦ A.mu x` (a permutation of simples).
  have hre : ∑ x, θ.theta x * J.ndim x
      = ∑ x, θ.theta (A.mu x) * J.ndim (A.mu x) :=
    (Equiv.sum_comp (Equiv.ofBijective _ A.mu_bijective)
      (fun x => θ.theta x * J.ndim x)).symm
  -- `τ = θ_{t^{-1}} · ∑_X θ_X γ_X^{-1} n_X = θ_{t^{-1}} τ`.
  have hkey : gaussSum J θ = θ.theta (B.dual t) * gaussSum J θ := by
    conv_lhs => rw [gaussSum_def, hre]
    conv_rhs => rw [gaussSum_def, ← sum_theta_gamma_inv_eq]
    rw [Finset.mul_sum]
    -- LHS: `∑ θ(μ x) n(μ x)`, RHS: `∑ θ(dual t) · (θ x γ x⁻¹ n x)`.
    refine Finset.sum_congr rfl (fun x _ => theta_ndim_mu_eq t A hmono x)
  -- Cancel `τ ≠ 0`.
  have hcancel : (θ.theta (B.dual t) - 1) * gaussSum J θ = 0 := by
    rw [sub_mul, one_mul, sub_eq_zero]
    exact hkey.symm
  cases' mul_eq_zero.mp hcancel with hz hτ0
  · exact sub_eq_zero.mp hz
  · exact absurd hτ0 hτ

/-- **Lemma 2.1 (Lacabanne), uniqueness in (2.1).**
Invertible objects are determined by their monodromy pairing (the monodromy
isomorphism (2.3)); hence at most one invertible `t` satisfies (2.1). -/
theorem lemma2_1_unique
    (hInj : ∀ t t' : ι, B.IsInvertible t → B.IsInvertible t' →
      (∀ x : ι, C.monodromy x t = C.monodromy x t') → t = t')
    (t t' : ι) (ht : B.IsInvertible t) (ht' : B.IsInvertible t')
    (hmono : SlopeIsMonodromy C J t) (hmono' : SlopeIsMonodromy C J t') :
    t = t' :=
  hInj t t' ht ht' (fun x => (hmono x).trans (hmono' x).symm)

/-- Package of both halves of Lemma 2.1: any two invertibles satisfying (2.1)
coincide, and the common value satisfies (2.2). -/
theorem lemma2_1
    (hInj : ∀ t t' : ι, B.IsInvertible t → B.IsInvertible t' →
      (∀ x : ι, C.monodromy x t = C.monodromy x t') → t = t')
    (t t' : ι) (ht : B.IsInvertible t) (ht' : B.IsInvertible t')
    (hmono : SlopeIsMonodromy C J t) (hmono' : SlopeIsMonodromy C J t')
    (A : InvertibleTensor B C J θ t) (hH : HopfLinkIdentity C J θ) :
    t = t' ∧ θ.theta (B.dual t) = 1 :=
  ⟨lemma2_1_unique hInj t t' ht ht' hmono hmono',
    lemma2_1_twist t ht hmono A hH⟩

end Lacabanne

end Paper18
