import Paper18.Category.DrinfeldNoPivotalNondegenerateRegular
import Paper18.Category.DrinfeldNoPivotalNondegenerateProjection

/-! # Actual Müger nondegeneracy of a braided fusion category's center, without pivotal data -/
noncomputable section
set_option maxHeartbeats 2000000
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped MonObj
universe v u w
namespace Paper18.Category.DrinfeldNoPivotal
open DrinfeldCoendModules
attribute [local instance 2000] RightRigidCategory.rightDual
variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
  [RightRigidCategory D] [Preadditive D] [Linear ℂ D]
  [MonoidalPreadditive D] [MonoidalLinear ℂ D] [HasKernels D] [HasFiniteBiproducts D]
  [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ D)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton D ι)

/-- The actual regular coend annular action detects every nonunit simple
label. Triviality would collapse its nonzero simple-diagonal cap summand. -/
lemma unitLabel_of_regularHolonomy_eq_id (i : ι)
    (h : moduleHolonomy S (Mod_.regular (algebra S)) (S.simpleObject i) = 𝟙 _) :
    i = S.unitLabel := by
  by_contra hi
  have hg := injection_eq_evaluation_unit_of_regularHolonomy S (S.simpleObject i) h
  have hz : 𝟙 (dual D (S.simpleObject i) ⊗ S.simpleObject i) = 0 := by
    rw [← injection_projection_self S i, hg, assoc, unit_projection_zero S i hi, comp_zero]
  have he : ε_ (S.simpleObject i) (dual D (S.simpleObject i)) = 0 := by
    rw [← id_comp (ε_ (S.simpleObject i) (dual D (S.simpleObject i))), hz, zero_comp]
  letI := S.simple_rightDual (S.simpleObject i)
  exact exactPairing_evaluation_ne_zero (S.simpleObject i) (dual D (S.simpleObject i)) he

/-- Every actual underlying simple constituent of a transparent central
object has the actual tensor-unit label. -/
lemma transparent_constituent_unitLabel (Z : Center D) (hZ : Z ∈ mugerCenter)
    (a : Fin (S.length Z.1)) : S.label Z.1 a = S.unitLabel := by
  let r : Retract (S.simpleObject (S.label Z.1 a)) Z.1 := {
    i := S.coendInclusion Z.1 a
    r := S.coendProjection Z.1 a
    retract := by
      simp only [FiniteSemisimpleSkeleton.coendInclusion,
        FiniteSemisimpleSkeleton.coendProjection, assoc,
        Iso.inv_hom_id_assoc, biproduct.ι_π_self] }
  exact unitLabel_of_regularHolonomy_eq_id S _
    (regularHolonomy_eq_id_of_retract S r (regularHolonomy_eq_id_of_transparent S Z hZ))

include S

/-- The regular coend test forces the underlying object of every actual
transparent central object to be a finite direct sum of tensor units. -/
lemma transparent_underlying_unitSum (Z : Center D) (hZ : Z ∈ mugerCenter) : IsUnitSum Z.1 := by
  refine ⟨S.length Z.1, ⟨S.decomposition Z.1 ≪≫ biproduct.mapIso (fun a => ?_)⟩⟩
  exact eqToIso (congrArg S.simpleObject (transparent_constituent_unitLabel S Z hZ a)) ≪≫ S.unitIso

/-- The actual Drinfeld center of every actual braided fusion category
is Müger nondegenerate. No pivotal, spherical, positive, matrix-invertibility,
or nondegeneracy premise on the original category is used. -/
theorem center_nondegenerate : IsNondegenerate (C := Center D) := by
  intro Z hZ
  apply IsUnitSum.of_iso (Drinfeld.isoPositiveOfCentralizes Z
    (fun Y => hZ ((Drinfeld.negative D).obj Y) (Set.mem_univ _)))
  exact Drinfeld.positive_unitSum (transparent_underlying_unitSum S Z hZ)

end Paper18.Category.DrinfeldNoPivotal
