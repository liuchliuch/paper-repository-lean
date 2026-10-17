import Paper18.Category.BimoduleRelativeTensorMonoidalBasic

/-! # Actual reversed tensor coherence from the bimodule pentagon -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits MonoidalOpposite
open scoped MonObj MonoidalLeftAction
universe v u
namespace Paper18.Category.BimoduleRelativeTensor
variable {D : Type u} [Category.{v} D] [MonoidalCategory D]
  [HasCoequalizers D] [LeftRigidCategory D] [RightRigidCategory D]
  [Preadditive D] [Linear ℂ D] [MonoidalPreadditive D] [MonoidalLinear ℂ D]
attribute [local instance] InternalModule.ambientMonoidalOppositeLeftAction
variable (R : D) [MonObj R]
attribute [local instance] nativeMonoidal

lemma reverseHom_ext {F G : (ModuleEnd R)ᴹᵒᵖ} {f g : F ⟶ G}
    (h : ∀ N : Mod_ D R, (f.unmop.val.app N).hom = (g.unmop.val.app N).hom) : f = g := by
  apply Quiver.Hom.unmop_inj
  apply Subtype.ext
  apply NatTrans.ext
  funext N
  apply Mod_.Hom.ext
  exact h N

/-- All actual reversed tensor comparison laws follow from the actual
bimodule associator naturality, pentagon and triangle equations. -/
def reverseRepresentationOplax : (reverseRepresentation R).OplaxMonoidal where
  «η» := (reverseUnitIso R).hom
  δ P Q := (reverseTensorIso R P Q).hom
  δ_natural_left {P P'} f Q := by
    apply reverseHom_ext R
    intro N
    letI := nativeBicategory (D := D)
    change (associator P Q (moduleAsNative N)).hom.hom.hom ≫
        (whiskerRight f (tensor Q (moduleAsNative N))).hom.hom =
      (whiskerRight (whiskerRight f Q) (moduleAsNative N)).hom.hom ≫
        (associator P' Q (moduleAsNative N)).hom.hom.hom
    exact congrArg (fun k => k.hom.hom)
      (Bicategory.associator_naturality_left
        (a := Mon.mk R) (b := Mon.mk R) (c := Mon.mk R) (d := Mon.mk (𝟙_ D))
        f Q (moduleAsNative N)).symm
  δ_natural_right {Q Q'} P f := by
    apply reverseHom_ext R
    intro N
    letI := nativeBicategory (D := D)
    change (associator P Q (moduleAsNative N)).hom.hom.hom ≫
        (whiskerLeft P (whiskerRight f (moduleAsNative N))).hom.hom =
      (whiskerRight (whiskerLeft P f) (moduleAsNative N)).hom.hom ≫
        (associator P Q' (moduleAsNative N)).hom.hom.hom
    exact congrArg (fun k => k.hom.hom)
      (Bicategory.associator_naturality_middle
        (a := Mon.mk R) (b := Mon.mk R) (c := Mon.mk R) (d := Mon.mk (𝟙_ D))
        P f (moduleAsNative N)).symm
  oplax_associativity P Q U := by
    apply reverseHom_ext R
    intro N
    change (associator (tensor P Q) U (moduleAsNative N)).hom.hom.hom ≫
        (associator P Q (tensor U (moduleAsNative N))).hom.hom.hom ≫ 𝟙 _ =
      (whiskerRight (associator P Q U).hom (moduleAsNative N)).hom.hom ≫
        (associator P (tensor Q U) (moduleAsNative N)).hom.hom.hom ≫
          (whiskerLeft P (associator Q U (moduleAsNative N)).hom).hom.hom
    rw [comp_id]
    exact congrArg (fun k => k.hom.hom) (pentagon P Q U (moduleAsNative N)).symm
  oplax_left_unitality P := by
    apply reverseHom_ext R
    intro N
    letI := nativeBicategory (D := D)
    change 𝟙 _ = (whiskerRight (leftUnitor P).inv (moduleAsNative N)).hom.hom ≫
      (associator (regular R) P (moduleAsNative N)).hom.hom.hom ≫
        (leftUnitor (tensor P (moduleAsNative N))).hom.hom.hom
    have h : (whiskerRight (leftUnitor P).inv (moduleAsNative N)) ≫
        (associator (regular R) P (moduleAsNative N)).hom ≫
          (leftUnitor (tensor P (moduleAsNative N))).hom = 𝟙 _ := by
      have hu : whiskerRight (leftUnitor P).inv (moduleAsNative N) =
          (leftUnitor (tensor P (moduleAsNative N))).inv ≫
            (associator (regular R) P (moduleAsNative N)).inv :=
        Bicategory.leftUnitor_inv_whiskerRight
          (a := Mon.mk R) (b := Mon.mk R) (c := Mon.mk (𝟙_ D)) P (moduleAsNative N)
      rw [hu]
      simp only [assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id]
    exact congrArg (fun k => k.hom.hom) h.symm
  oplax_right_unitality P := by
    apply reverseHom_ext R
    intro N
    letI := nativeBicategory (D := D)
    change 𝟙 _ = (whiskerRight (rightUnitor P).inv (moduleAsNative N)).hom.hom ≫
      (associator P (regular R) (moduleAsNative N)).hom.hom.hom ≫
        (whiskerLeft P (leftUnitor (moduleAsNative N)).hom).hom.hom
    have h : whiskerRight (rightUnitor P).inv (moduleAsNative N) ≫
        (associator P (regular R) (moduleAsNative N)).hom ≫
          whiskerLeft P (leftUnitor (moduleAsNative N)).hom = 𝟙 _ := by
      rw [triangle]
      have hw : whiskerRight (rightUnitor P).inv (moduleAsNative N) ≫
          whiskerRight (rightUnitor P).hom (moduleAsNative N) =
            whiskerRight ((rightUnitor P).inv ≫ (rightUnitor P).hom) (moduleAsNative N) :=
        (Bicategory.comp_whiskerRight
          (a := Mon.mk R) (b := Mon.mk R) (c := Mon.mk (𝟙_ D))
          (rightUnitor P).inv (rightUnitor P).hom (moduleAsNative N)).symm
      rw [hw, Iso.inv_hom_id]
      exact Bicategory.id_whiskerRight
        (a := Mon.mk R) (b := Mon.mk R) (c := Mon.mk (𝟙_ D)) P (moduleAsNative N)
    exact congrArg (fun k => k.hom.hom) h.symm

end Paper18.Category.BimoduleRelativeTensor
