import Paper18.Category.RigidMultiplicity
import Paper18.Category.SphericalizationFunctor
import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# Rigid conversion from a left adjoint to a right adjoint

For a strong monoidal functor between rigid complex-linear categories,
dualizing the proved left-adjoint Hom equivalence constructs the actual
right adjoint. This is the adjunction foundation for the actual diagonal
algebra; no multiplication or Frobenius law is supplied as extra data.
-/

noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
universe v u v₁ u₁
namespace Paper18.Category.DiagonalAlgebra

section Duality
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]

/-- The actual linear Hom duality is the chosen rigid mate. -/
lemma rightDualHomLinearEquiv_apply {X Y : C} [HasRightDual X] [HasRightDual Y]
    (f : X ⟶ Y) : rightDualHomLinearEquiv X Y f = rightAdjointMate f := by
  dsimp [rightDualHomLinearEquiv, tensorLeftHomLinearEquiv, tensorRightHomLinearEquiv,
    tensorLeftHomEquiv, tensorRightHomEquiv, CategoryTheory.Linear.homCongr,
    rightAdjointMate]
  monoidal

/-- Left duality in the represented object and right duality in the
variable object give the required actual Hom correspondence. -/
def leftRightDualHomLinearEquiv (X W : C) [HasRightDual X] [HasLeftDual W] :
    (W ⟶ Xᘁ) ≃ₗ[ℂ] (X ⟶ ᘁW) :=
  letI : HasRightDual (ᘁW) := CategoryTheory.hasRightDualLeftDual (X := W)
  (rightDualHomLinearEquiv X (ᘁW)).symm

lemma leftRightDualHomLinearEquiv_naturality {X X' W : C}
    [HasRightDual X] [HasRightDual X'] [HasLeftDual W]
    (f : X' ⟶ X) (h : W ⟶ Xᘁ) :
    leftRightDualHomLinearEquiv X' W (h ≫ rightAdjointMate f) =
      f ≫ leftRightDualHomLinearEquiv X W h := by
  letI : HasRightDual (ᘁW) := CategoryTheory.hasRightDualLeftDual (X := W)
  apply (rightDualHomLinearEquiv X' (ᘁW)).injective
  change (rightDualHomLinearEquiv X' (ᘁW))
      ((rightDualHomLinearEquiv X' (ᘁW)).symm (h ≫ rightAdjointMate f)) =
    (rightDualHomLinearEquiv X' (ᘁW))
      (f ≫ (rightDualHomLinearEquiv X (ᘁW)).symm h)
  rw [LinearEquiv.apply_symm_apply, rightDualHomLinearEquiv_apply, comp_rightAdjointMate]
  have hh : rightAdjointMate ((rightDualHomLinearEquiv X (ᘁW)).symm h) = h := by
    rw [← rightDualHomLinearEquiv_apply]
    exact LinearEquiv.apply_symm_apply _ _
  rw [hh]

end Duality

section Adjoint
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [RightRigidCategory C] [LeftRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  {D : Type u₁} [Category.{v₁} D] [MonoidalCategory D] [RightRigidCategory D]
  [Preadditive D] [Linear ℂ D] [MonoidalPreadditive D] [MonoidalLinear ℂ D]
  (F : C ⥤ D) [F.Monoidal] [F.Additive] [F.Linear ℂ]
  (L : D ⥤ C) (adj : L ⊣ F)

/-- The given actual adjunction is automatically complex-linear on Hom
spaces because its right adjoint is complex-linear. -/
def linearAdjunctionHomEquiv (Y : D) (X : C) :
    (L.obj Y ⟶ X) ≃ₗ[ℂ] (Y ⟶ F.obj X) where
  toEquiv := adj.homEquiv Y X
  map_add' f g := by
    change adj.unit.app Y ≫ F.map (f + g) =
      adj.unit.app Y ≫ F.map f + adj.unit.app Y ≫ F.map g
    simp only [Functor.map_add, Preadditive.comp_add]
  map_smul' c f := by
    change adj.unit.app Y ≫ F.map (c • f) = c • (adj.unit.app Y ≫ F.map f)
    simp only [Functor.map_smul, Linear.comp_smul]

/-- The object underlying the constructed actual right adjoint. -/
def rigidRightAdjointObj (Y : D) : C := ᘁ(L.obj (Yᘁ))

/-- Dualizing the actual left-adjoint Hom equivalence gives the actual
right-adjoint Hom equivalence. -/
def rigidRightAdjointHomLinearEquiv (X : C) (Y : D) :
    (F.obj X ⟶ Y) ≃ₗ[ℂ] (X ⟶ rigidRightAdjointObj L Y) :=
  (rightDualHomLinearEquiv (F.obj X) Y).trans
    ((CategoryTheory.Linear.homCongr ℂ (Iso.refl (Yᘁ)) (dualComparison F X).symm).trans
      ((linearAdjunctionHomEquiv F L adj (Yᘁ) (Xᘁ)).symm.trans
        (leftRightDualHomLinearEquiv X (L.obj (Yᘁ)))))

lemma rigidRightAdjointHomLinearEquiv_naturality
    {X X' : C} (Y : D) (f : X' ⟶ X) (g : F.obj X ⟶ Y) :
    rigidRightAdjointHomLinearEquiv F L adj X' Y (F.map f ≫ g) =
      f ≫ rigidRightAdjointHomLinearEquiv F L adj X Y g := by
  simp only [rigidRightAdjointHomLinearEquiv, LinearEquiv.trans_apply,
    CategoryTheory.Linear.homCongr_apply, Iso.refl_inv, Iso.symm_hom, id_comp]
  change leftRightDualHomLinearEquiv X' (L.obj (Yᘁ))
      ((adj.homEquiv (Yᘁ) (X'ᘁ)).symm
        (rightDualHomLinearEquiv (F.obj X') Y (F.map f ≫ g) ≫
          (dualComparison F X').inv)) =
    f ≫ leftRightDualHomLinearEquiv X (L.obj (Yᘁ))
      ((adj.homEquiv (Yᘁ) (Xᘁ)).symm
        (rightDualHomLinearEquiv (F.obj X) Y g ≫ (dualComparison F X).inv))
  rw [rightDualHomLinearEquiv_apply, rightDualHomLinearEquiv_apply,
    comp_rightAdjointMate]
  have hn : rightAdjointMate (F.map f) ≫ (dualComparison F X').inv =
      (dualComparison F X).inv ≫ F.map (rightAdjointMate f) :=
    (dualComparison_inv_naturality F f).symm
  simp only [Category.assoc]
  rw [hn, ← Category.assoc, adj.homEquiv_naturality_right_symm]
  exact leftRightDualHomLinearEquiv_naturality f _

/-- The actual right adjoint functor is constructed from the proved Hom
equivalence; its map and functor laws follow from representability. -/
def rigidRightAdjoint : D ⥤ C :=
  Adjunction.rightAdjointOfEquiv
    (fun X Y => (rigidRightAdjointHomLinearEquiv F L adj X Y).toEquiv)
    (fun _ _ Y f g => rigidRightAdjointHomLinearEquiv_naturality F L adj Y f g)

/-- The actual right adjunction, with no right-adjoint existence premise. -/
def rigidRightAdjunction : F ⊣ rigidRightAdjoint F L adj :=
  Adjunction.adjunctionOfEquivRight
    (fun X Y => (rigidRightAdjointHomLinearEquiv F L adj X Y).toEquiv)
    (fun _ _ Y f g => rigidRightAdjointHomLinearEquiv_naturality F L adj Y f g)

@[simp] lemma rigidRightAdjoint_obj (Y : D) :
    (rigidRightAdjoint F L adj).obj Y = rigidRightAdjointObj L Y := rfl

lemma rigidRightAdjoint_map {Y Y' : D} (g : Y ⟶ Y') :
    (rigidRightAdjoint F L adj).map g =
      rigidRightAdjointHomLinearEquiv F L adj (rigidRightAdjointObj L Y) Y'
        ((rigidRightAdjointHomLinearEquiv F L adj (rigidRightAdjointObj L Y) Y).symm
          (𝟙 _) ≫ g) := rfl

instance rigidRightAdjoint_additive : (rigidRightAdjoint F L adj).Additive where
  map_add {Y Y'} g h := by
    simp only [rigidRightAdjoint_map, Preadditive.comp_add, map_add]

instance rigidRightAdjoint_linear : (rigidRightAdjoint F L adj).Linear ℂ where
  map_smul g c := by
    simp only [rigidRightAdjoint_map, Linear.comp_smul, map_smul]

/-- The actual right adjoint inherits its lax monoidal structure from the
actual adjunction and the proved strong monoidal structure of `F`. -/
instance rigidRightAdjoint_laxMonoidal : (rigidRightAdjoint F L adj).LaxMonoidal :=
  (rigidRightAdjunction F L adj).rightAdjointLaxMonoidal

@[simp] theorem rigidRightAdjunction_homEquiv (X : C) (Y : D) :
    (rigidRightAdjunction F L adj).homEquiv X Y =
      (rigidRightAdjointHomLinearEquiv F L adj X Y).toEquiv := by
  unfold rigidRightAdjunction Adjunction.adjunctionOfEquivRight
  rw [Adjunction.mkOfHomEquiv_homEquiv]

end Adjoint

end Paper18.Category.DiagonalAlgebra
