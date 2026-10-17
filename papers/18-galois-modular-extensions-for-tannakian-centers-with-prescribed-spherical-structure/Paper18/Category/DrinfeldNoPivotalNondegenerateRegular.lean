import Paper18.Category.DrinfeldCoendModulesInverse
import Paper18.Category.DrinfeldNondegenerate

/-! # The regular coend module tests transparent central objects without pivotal data -/
noncomputable section
set_option maxHeartbeats 2000000
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
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

/-- The actual central object recovered from the regular coend module. -/
def regularCenter : Center D := (fromModules S).obj (Mod_.regular (algebra S))

/-- Transparency against the actual regular coend module makes its
annular operator the identity on the transparent underlying object. -/
lemma regularHolonomy_eq_id_of_transparent (Z : Center D) (hZ : Z ∈ mugerCenter) :
    moduleHolonomy S (Mod_.regular (algebra S)) Z.1 = 𝟙 _ := by
  let I := regularCenter S
  have hz := congrArg Center.Hom.f (hZ I (Set.mem_univ _))
  change (Z.2.β I.1).hom ≫ (I.2.β Z.1).hom = 𝟙 _ at hz
  have hb : (Z.2.β I.1).hom = (β_ Z.1 I.1).hom :=
    (Drinfeld.centralizes_negative_iff Z I.1).mp
      (hZ ((Drinfeld.negative D).obj I.1) (Set.mem_univ _))
  rw [hb] at hz
  have hi : (I.2.β Z.1).inv = (β_ Z.1 I.1).hom := by
    apply (cancel_mono (I.2.β Z.1).hom).mp
    rw [Iso.inv_hom_id, hz]
  rw [← fromModules_holonomy S (Mod_.regular (algebra S)) Z.1]
  change (I.2.β Z.1).inv ≫ (β_ Z.1 I.1).inv = 𝟙 _
  rw [hi, Iso.hom_inv_id]

/-- Naturality restricts the identity regular annular operator to every
actual retract of the label. -/
lemma regularHolonomy_eq_id_of_retract {X Y : D} (r : Retract X Y)
    (h : moduleHolonomy S (Mod_.regular (algebra S)) Y = 𝟙 _) :
    moduleHolonomy S (Mod_.regular (algebra S)) X = 𝟙 _ := by
  have hn := moduleHolonomy_naturality S (Mod_.regular (algebra S)) r.i
  rw [h, comp_id] at hn
  have hh := congrArg (fun q => q ≫ r.r ▷ algebra S) hn
  change r.i ▷ algebra S ≫ r.r ▷ algebra S =
    (moduleHolonomy S (Mod_.regular (algebra S)) X ≫ r.i ▷ algebra S) ≫ r.r ▷ algebra S at hh
  simp only [assoc, ← comp_whiskerRight, r.retract,
    id_whiskerRight] at hh
  exact (comp_id _).symm.trans hh.symm

omit [Simple (𝟙_ D)] in
/-- If the regular annular operator is trivial, the actual coend generator
factors through its evaluation and the actual algebra unit. -/
lemma injection_eq_evaluation_unit_of_regularHolonomy (X : D)
    (h : moduleHolonomy S (Mod_.regular (algebra S)) X = 𝟙 _) :
    injection S X = ε_ X (dual D X) ≫ η[algebra S] := by
  have hc := moduleHolonomy_cap S (Mod_.regular (algebra S)) X
  rw [h] at hc
  change (α_ (dual D X) X (algebra S)).hom ≫
      (dual D X ◁ 𝟙 (X ⊗ algebra S) ≫ (α_ (dual D X) X (algebra S)).inv ≫
        ε_ X (dual D X) ▷ algebra S ≫ (λ_ (algebra S)).hom) =
    injection S X ▷ algebra S ≫ μ[algebra S] at hc
  simp only [whiskerLeft_id, id_comp, Iso.hom_inv_id_assoc] at hc
  have hh := congrArg (fun q => (dual D X ⊗ X) ◁ η[algebra S] ≫ q) hc
  change (dual D X ⊗ X) ◁ η[algebra S] ≫
      ε_ X (dual D X) ▷ algebra S ≫ (λ_ (algebra S)).hom =
    (dual D X ⊗ X) ◁ η[algebra S] ≫ injection S X ▷ algebra S ≫ μ[algebra S] at hh
  rw [whisker_exchange_assoc, leftUnitor_naturality, whisker_exchange_assoc,
    MonObj.mul_one, rightUnitor_naturality] at hh
  apply (cancel_epi (ρ_ (dual D X ⊗ X)).hom).mp
  simpa only [unitors_equal, rightUnitor_naturality_assoc, assoc] using hh.symm

end Paper18.Category.DrinfeldNoPivotal
