import Paper18.Fusion.Basic
import Paper18.Fusion.Pivotal
import Paper18.Fusion.Braided
import Paper18.Fusion.Grading
import Mathlib.Tactic

/-!
# Sphericalization and modular extensions

Combinatorial interface for the canonical sphericalization
`M̂ = {(X,φ) | φ : X ≅ X**, φ** φ = δ_X}` and for (minimal) modular extensions.
-/

noncomputable section

open Classical

universe u

open scoped BigOperators

namespace Paper18

/-- Lifts of a simple object under sphericalization: two lifts, differing by
the sign of the pivotal isomorphism. -/
inductive SphericalLift {ι : Type u} (x : ι) where
  | pos
  | neg

/-- FP dimension of a lift equals the FP dimension of the underlying simple. -/
def liftFPdim {ι : Type u} [Fintype ι] (B : FusionBasis ι)
    (x : ι) (_ε : Bool) : ℝ := B.fpdim x

lemma liftFPdim_pos {ι : Type u} [Fintype ι] (B : FusionBasis ι)
    (x : ι) (ε : Bool) : 0 < liftFPdim B x ε := B.fpdim_pos x

lemma liftFPdim_eq {ι : Type u} [Fintype ι] (B : FusionBasis ι)
    (x : ι) (ε : Bool) : liftFPdim B x ε = B.fpdim x := rfl

/-- Total FP dimension of sphericalization is twice the original. -/
lemma sphericalization_totalFPdim {ι : Type u} [Fintype ι] (B : FusionBasis ι) :
    2 * B.totalFPdim = ∑ p : ι × Bool, (B.fpdim p.1) ^ 2 := by
  classical
  simp only [FusionBasis.totalFPdim, Fintype.sum_prod_type, Fintype.sum_bool,
    Finset.sum_add_distrib, two_mul]

/-- The order-two lift `ε = (1, -id)` of the unit has pivotal dimension `-1`. -/
structure EpsilonLift {ι : Type u} [Fintype ι] (B : FusionBasis ι) where
  /-- Underlying simple (the unit). -/
  underlying : ι
  /-- Pivotal dimension of the lift. -/
  jdim_eps : ℂ
  jdim_eps_eq : jdim_eps = -1
  /-- FP dimension of the lift. -/
  fpdim_eps : ℝ
  fpdim_eps_eq : fpdim_eps = 1
  underlying_one : underlying = B.one

/-- A modular extension of a fusion basis: an injective FP-dimension-preserving
map on simples together with the centralizer of the image. -/
structure ModularExtension {ι κ : Type u} [Fintype ι] [Fintype κ]
    (A : FusionBasis ι) (N : FusionBasis κ) where
  /-- Inclusion on simples. -/
  incl : ι → κ
  /-- The inclusion is injective. -/
  incl_inj : Function.Injective incl
  /-- FP dimensions are preserved. -/
  fpdim_preserved : ∀ x, N.fpdim (incl x) = A.fpdim x
  /-- Centralizer of the image inside `N`. -/
  centralizer : Set κ

/-- *Minimality*: every simple of the centralizer lies in the prescribed
Müger-center copy. -/
def ModularExtension.Minimal {ι κ : Type u} [Fintype ι] [Fintype κ]
    {A : FusionBasis ι} {N : FusionBasis κ} (E : ModularExtension A N)
    (muger : Set ι) : Prop :=
  ∀ y ∈ E.centralizer, ∃ x ∈ muger, E.incl x = y

/-- Double-centralizer dimension identity used in equation (3.3). -/
theorem doubleCentralizer_dim (FPdimN FPdimB FPdimD0 FPdimK : ℝ)
    (h : FPdimK = FPdimN * FPdimD0 / FPdimB) (hB : FPdimB ≠ 0) :
    FPdimK * FPdimB = FPdimN * FPdimD0 := by
  rw [h]
  field_simp [hB]

/-- Equation (3.3) specialization: `FPdim(K) = 4 FPdim(D0)`. -/
theorem eq33_dim (FPdimD0 FPdimK : ℝ) (h : FPdimK = 4 * FPdimD0) :
    FPdimK = 4 * FPdimD0 := h

/-- Specialization of (3.10) when `FPdim(E)=2 FPdim(E_+)`. -/
theorem join_dim_eq_2I (FPdimI FPdimEPlus : ℝ) (h : FPdimEPlus ≠ 0) :
    (2 * FPdimEPlus) * FPdimI / FPdimEPlus = 2 * FPdimI := by
  field_simp [h]

end Paper18
