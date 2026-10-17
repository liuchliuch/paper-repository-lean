import Paper23.GroupRingEncoding
import Mathlib.Algebra.MonoidAlgebra.Basic

/-!
The group-ring module structure on the genuine labelled-cell free group.
It is transported along the proved canonical-coordinate bijection, then
identified with the actual relabelling action for every group element.
-/
namespace Paper23.Labels
open Cubical

noncomputable instance labelledGroupRingSMul : SMul GroupRing (Cube →₀ ℤ) where
  smul r x := coefficientEquiv.symm (r • coefficientEquiv x)

@[simp] theorem coefficientEquiv_smul (r : GroupRing) (x : Cube →₀ ℤ) :
    coefficientEquiv (r • x) = r • coefficientEquiv x :=
  coefficientEquiv.apply_symm_apply _

noncomputable instance labelledGroupRingModule : Module GroupRing (Cube →₀ ℤ) :=
  Function.Injective.module GroupRing coefficientEquiv.toAddMonoidHom
    coefficientEquiv.injective coefficientEquiv_smul

/-- The actual labelled-cell integral free group is free over Z[S4], with
canonical cells as basis. The comparison retains every permutation coordinate. -/
noncomputable def groupRingEquiv : (Cube →₀ ℤ) ≃ₗ[GroupRing] (Canonical →₀ GroupRing) where
  toFun := coefficientEquiv
  invFun := coefficientEquiv.symm
  left_inv := coefficientEquiv.symm_apply_apply
  right_inv := coefficientEquiv.apply_symm_apply
  map_add' := coefficientEquiv.map_add
  map_smul' := coefficientEquiv_smul

noncomputable def permutationBasis (p : S4) : GroupRing := Finsupp.single p 1

/-- A basis element p of the group ring acts by the actual relabelling p,
without an additional orientation sign. -/
theorem groupRing_single_smul_single (p : S4) (c : Cube) (n : ℤ) :
    permutationBasis p • Finsupp.single c n =
      Finsupp.single (relabel p c) n := by
  apply coefficientEquiv.injective
  rw [coefficientEquiv_smul, coefficientEquiv_single, coefficientEquiv_single]
  rw [canonical_relabel, assignment_relabel]
  simp only [permutationBasis, Finsupp.smul_single, smul_eq_mul,
    MonoidAlgebra.single_mul_single, one_mul]

/-- The transported module operation agrees with the original particle action
on every integral labelled chain, not only on a chosen basis. -/
theorem groupRing_single_smul (p : S4) (x : Cube →₀ ℤ) :
    permutationBasis p • x = labelledAction p x := by
  induction x using Finsupp.induction with
  | zero => simp
  | single_add c n x hc hn ih =>
    rw [smul_add, map_add, ih, groupRing_single_smul_single, labelledAction_single]

end Paper23.Labels
