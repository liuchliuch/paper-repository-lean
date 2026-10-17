import Paper18.Category.GraphPicardMoritaImageTensorMonad

/-! # The actual tensor image is the actual right-module category

Actual Beck monadicity, the actual rigid projection monad isomorphism,
and the actual native Eilenberg--Moore/right-module comparison compose.
No equivalence, essential-surjectivity or separability conclusion is an input.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits MonoidalOpposite
open scoped MonObj
universe v u w u' w'
namespace Paper18.Category.GraphPicard.MoritaImage
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [HasFiniteBiproducts C] [HasKernels C] [MonoidalCategory C]
  [MonoidalPreadditive C] [MonoidalLinear ℂ C] [RightRigidCategory C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {D : Type u'} [Category.{v} D] [Preadditive D] [Linear ℂ D]
  [HasFiniteBiproducts D] [HasKernels D] [MonoidalCategory D]
  [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  (F : C ⥤ D) [F.Additive] [F.Linear ℂ] [F.Monoidal]
open DiagonalAlgebra

lemma adjunction_unit (X : C) :
    (adjunction S F).unit.app X = (semisimpleRightAdjunction S F).unit.app X := by
  change (semisimpleRightAdjunction S F).homEquiv X (F.obj X) (𝟙 _) = _
  rw [Adjunction.homEquiv_unit, (semisimpleRightAdjoint S F).map_id]
  exact Category.comp_id _

lemma adjunction_counit (Y : Image F) :
    (adjunction S F).counit.app Y = (semisimpleRightAdjunction S F).counit.app Y.obj := by
  change ((semisimpleRightAdjunction S F).homEquiv
    ((semisimpleRightAdjoint S F).obj Y.obj) Y.obj).symm (𝟙 _) = _
  rw [Adjunction.homEquiv_counit, F.map_id, Category.id_comp]

/-- Restricting the target to actual summands leaves the actual
adjunction monad unchanged up to a genuine identity-component isomorphism. -/
def originalMonadIso : (adjunction S F).toMonad ≅ (semisimpleRightAdjunction S F).toMonad :=
  MonadIso.mk (Iso.refl _)
    (fun X => by
      change (adjunction S F).unit.app X ≫ 𝟙 _ = (semisimpleRightAdjunction S F).unit.app X
      rw [Category.comp_id, adjunction_unit])
    (fun X => by
      change (semisimpleRightAdjoint S F).map ((adjunction S F).counit.app ((core F).obj X)) ≫
        𝟙 _ = (((semisimpleRightAdjoint S F).map (F.map (𝟙 _))) ≫ 𝟙 _) ≫
          (semisimpleRightAdjoint S F).map ((semisimpleRightAdjunction S F).counit.app (F.obj X))
      rw [F.map_id, (semisimpleRightAdjoint S F).map_id,
        Category.id_comp, Category.comp_id, adjunction_counit]
      exact (Category.id_comp _).symm)

variable {κ : Type w'} [Fintype κ] (T : FiniteSemisimpleSkeleton D κ)

/-- The actual tensor image is the genuine category of internal right
modules over the actual right-adjoint unit algebra. -/
def moduleEquivalence : Image F ≌
    Mod_ Cᴹᵒᵖ (mop (semisimpleAdjointAlgebra S F)) :=
  beckEquivalence S F T |>.trans
    ((Monad.algebraEquivOfIsoMonads (originalMonadIso S F)).trans
      ((Monad.algebraEquivOfIsoMonads (rightTensorMonadIso S F).symm).trans
        (ModuleInternalHom.rightMonadModuleEquivalence (semisimpleAdjointAlgebra S F))))

end Paper18.Category.GraphPicard.MoritaImage
