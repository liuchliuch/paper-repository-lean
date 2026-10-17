import Paper18.Category.LocalModulesCenterFunctor
import Paper18.Category.DrinfeldBasic
import Paper18.Category.CentralizerClosure

/-! # Actual centralizer recognition for local separable modules -/
noncomputable section
open Classical CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open CategoryTheory.BraidedCategory
open scoped MonObj
universe v u
namespace Paper18.Category
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [RightRigidCategory C] [HasCoequalizers C] {A : C} [MonObj A] [IsCommMonObj A]
open RelativeTensor

/-- Centralizing the central free generator determines that component of
an arbitrary actual half-braiding. -/
theorem centralizes_centralFree_iff (Z : Center (Mod_ C A)) (X : C) :
    Centralizes ((centralFreeFunctor (A := A)).obj X) Z ↔
      (Z.2.β (InternalModule.free A X)).hom = (freeCentralIso X Z.1).inv := by
  rw [centralizes_iff]
  constructor
  · intro h
    have h' := congrArg Center.Hom.f h
    change (freeCentralIso X Z.1).hom ≫ (Z.2.β (InternalModule.free A X)).hom = 𝟙 _ at h'
    calc
      (Z.2.β (InternalModule.free A X)).hom =
          (freeCentralIso X Z.1).inv ≫
            ((freeCentralIso X Z.1).hom ≫ (Z.2.β (InternalModule.free A X)).hom) := by simp
      _ = _ := by rw [h', Category.comp_id]
  · intro h
    apply Center.ext
    change (freeCentralIso X Z.1).hom ≫ (Z.2.β (InternalModule.free A X)).hom = 𝟙 _
    rw [h, Iso.hom_inv_id]

omit [BraidedCategory C] [RightRigidCategory C] [HasCoequalizers C] [IsCommMonObj A] in
@[reassoc (attr := simp)]
theorem freeUnit_actionHom (M : Mod_ C A) :
    freeUnit M.X ≫ (InternalModule.actionHom M).hom = 𝟙 M.X := by
  change ((λ_ M.X).inv ≫ η[A] ▷ M.X) ≫ γ[A,M.X] = 𝟙 M.X
  rw [Category.assoc, InternalModule.one_smul, Iso.inv_hom_id]

/-- Naturality with the action of the algebra detects actual locality of
the underlying module. -/
theorem local_of_centralizes_centralFree (Z : Center (Mod_ C A))
    (hZ : ∀ X : C, Centralizes ((centralFreeFunctor (A := A)).obj X) Z) :
    IsLocalModule Z.1 := by
  let a := InternalModule.actionHom (𝟙_ (Mod_ C A))
  have ha : freeUnit (A := A) A ≫ a.hom = 𝟙 A :=
    freeUnit_actionHom (𝟙_ (Mod_ C A))
  have h := congrArg (fun k => (freeCentralIso A Z.1).hom ≫ k ≫ (λ_ Z.1).hom)
    (Z.2.naturality a)
  dsimp only at h
  change (freeCentralIso A Z.1).hom ≫ (Z.1 ◁ a ≫ (Z.2.β (𝟙_ (Mod_ C A))).hom) ≫
      (λ_ Z.1).hom =
    (freeCentralIso A Z.1).hom ≫ ((Z.2.β (InternalModule.free A A)).hom ≫ a ▷ Z.1) ≫
      (λ_ Z.1).hom at h
  rw [(centralizes_centralFree_iff Z A).mp (hZ A),
    Category.assoc, Category.assoc, Iso.hom_inv_id_assoc,
    Drinfeld.halfBraiding_unit] at h
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id] at h
  have hh := congrArg (fun k => freeTensorGenerator A Z.1 ≫ k.hom) h
  simp only [freeTensorGenerator, Mod_.comp_hom', Category.assoc] at hh
  rw [freeUnit_π_freeCentralIso_assoc, π_whiskerLeft_assoc,
    ← whiskerLeft_comp_assoc, ha, whiskerLeft_id,
    Category.id_comp, π_rightUnitor] at hh
  rw [π_whiskerRight_assoc, ← comp_whiskerRight_assoc, ha,
    id_whiskerRight, Category.id_comp, π_leftUnitor] at hh
  unfold IsLocalModule
  apply (cancel_epi (β_ A Z.1.X).hom).mp
  rw [Iso.hom_inv_id_assoc]
  exact hh

namespace SeparableAlgebra
variable (S : SeparableAlgebra A)

include S in
/-- Half-braidings on separable modules are determined on the actual free
modules, using actual free retracts. -/
theorem halfBraiding_hom_eq_of_free {M : Mod_ C A} (b c : HalfBraiding M)
    (h : ∀ X : C, (b.β (InternalModule.free A X)).hom =
      (c.β (InternalModule.free A X)).hom) (N : Mod_ C A) :
    (b.β N).hom = (c.β N).hom := by
  let R := S.freeRetract N
  calc
    (b.β N).hom = M ◁ R.i ≫ (b.β (InternalModule.free A N.X)).hom ≫ R.r ▷ M := by
      rw [b.naturality_assoc, ← comp_whiskerRight, R.retract, id_whiskerRight,
        Category.comp_id]
    _ = M ◁ R.i ≫ (c.β (InternalModule.free A N.X)).hom ≫ R.r ▷ M := by rw [h]
    _ = (c.β N).hom := by
      rw [c.naturality_assoc, ← comp_whiskerRight, R.retract, id_whiskerRight,
        Category.comp_id]

/-- Every actual center object centralizing the free image is isomorphic
to the central lift of its actual local underlying module. -/
def localCenterIsoOfCentralizes (Z : Center (Mod_ C A))
    (hZ : ∀ X : C, Centralizes ((centralFreeFunctor (A := A)).obj X) Z) :
    Z ≅ S.localCenterObj ⟨Z.1, local_of_centralizes_centralFree Z hZ⟩ := by
  let f : Z ⟶ S.localCenterObj ⟨Z.1, local_of_centralizes_centralFree Z hZ⟩ :=
    { f := 𝟙 Z.1
      comm N := by
        simp only [id_whiskerRight, whiskerLeft_id, Category.id_comp, Category.comp_id]
        apply S.halfBraiding_hom_eq_of_free
        intro X
        change (S.localCrossingIso Z.1 (InternalModule.free A X)
          (local_of_centralizes_centralFree Z hZ)).inv =
          (Z.2.β (InternalModule.free A X)).hom
        rw [S.localCrossingIso_free, (centralizes_centralFree_iff Z X).mp (hZ X)] }
  letI : IsIso f.f := show IsIso (𝟙 Z.1) from inferInstance
  exact Center.isoMk f

end SeparableAlgebra
end Paper18.Category
