import Paper23.Labels
import Mathlib.Algebra.MonoidAlgebra.Module

/-!
The integral basis decomposition underlying the group-ring representation.
The equivalence below is explicitly Z-linear; it retains every S4 coefficient.
-/
namespace Paper23.Labels
open Cubical

abbrev GroupRing := MonoidAlgebra ℤ S4

noncomputable def curryCoefficients : ((Canonical × S4) →₀ ℤ) ≃ₗ[ℤ] (Canonical →₀ GroupRing) where
  toFun f := Finsupp.curry f
  invFun f := Finsupp.uncurry f
  left_inv := Finsupp.uncurry_curry
  right_inv := Finsupp.curry_uncurry
  map_add' f g := by ext c p; rfl
  map_smul' r f := by ext c p; rfl

/-- Every labelled cube has its own integral coefficient, grouped by the
canonical cell and permutation. This is not augmentation to Z. -/
noncomputable def coefficientEquiv : (Cube →₀ ℤ) ≃ₗ[ℤ] (Canonical →₀ GroupRing) :=
  (Finsupp.domLCongr canonicalEquiv).trans curryCoefficients

@[simp] theorem coefficientEquiv_single (c : Cube) (n : ℤ) :
    coefficientEquiv (Finsupp.single c n) =
      Finsupp.single (canonical c) (Finsupp.single (assignment c) n) := by
  simp [coefficientEquiv, Finsupp.domLCongr_single, curryCoefficients, canonicalEquiv,
    Finsupp.curry_single]

theorem canonical_degree (c : Cube) : degree (canonical c).val.val = degree c.val :=
  ((canonical_perm c).map GraphCell.dimension).sum_eq

/-- Relabelling left-multiplies the permutation coefficient. -/
theorem assignment_relabel (p : S4) (c : Cube) :
    assignment (relabel p c) = p * assignment c := by
  apply relabel_free (c := (canonical c).val)
  calc
    relabel (assignment (relabel p c)) (canonical c).val = relabel p c := by
      rw [← canonical_relabel p c]
      exact reconstruct _
    _ = relabel (p * assignment c) (canonical c).val := by
      rw [relabel_mul, reconstruct]

/-- The basis permutation action is a genuine left action, before any chain
boundary is considered. -/
noncomputable def labelledAction (p : S4) : (Cube →₀ ℤ) →ₗ[ℤ] (Cube →₀ ℤ) :=
  Finsupp.lmapDomain ℤ ℤ (relabel p)

@[simp] theorem labelledAction_single (p : S4) (c : Cube) (n : ℤ) :
    labelledAction p (Finsupp.single c n) = Finsupp.single (relabel p c) n := by
  simp [labelledAction, Finsupp.lmapDomain_apply]

@[simp] theorem labelledAction_one : labelledAction 1 = LinearMap.id := by
  apply Finsupp.lhom_ext
  intro c n
  simp

@[simp] theorem labelledAction_mul (p q : S4) :
    labelledAction (p*q) = (labelledAction p).comp (labelledAction q) := by
  apply Finsupp.lhom_ext
  intro c n
  simp

/-- Each relabelled single coefficient appears at p*g, with its integer value
unchanged. In particular no sign character or augmentation has been applied. -/
theorem coefficientEquiv_relabel_single (p : S4) (c : Cube) (n : ℤ) :
    coefficientEquiv (labelledAction p (Finsupp.single c n)) =
      Finsupp.single (canonical c) (Finsupp.single (p * assignment c) n) := by
  simp [canonical_relabel, assignment_relabel]

end Paper23.Labels
