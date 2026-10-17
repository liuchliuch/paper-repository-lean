import Paper18.Category.ModuleFunctorAdjoint
import Paper18.Category.ModuleAlphaInductionEnd
import Mathlib.CategoryTheory.Monoidal.Rigid.OfEquivalence

/-! # Actual right rigidity of finite semisimple module endofunctors -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
universe v u v' u' w
namespace Paper18.Category.ModuleFunctor
attribute [local instance] endofunctorMonoidalCategory

section Ordinary
variable {M : Type u'} [Category.{v'} M] {F G : M ⥤ M}

/-- An actual ordinary adjunction is an actual exact pairing in the
composition monoidal category of endofunctors. -/
def ordinaryAdjunctionExactPairing (adj : F ⊣ G) : ExactPairing F G where
  coevaluation' := adj.unit
  evaluation' := adj.counit
  coevaluation_evaluation' := by
    ext m
    change adj.unit.app (G.obj m) ≫ 𝟙 _ ≫ G.map (adj.counit.app m) = 𝟙 _ ≫ 𝟙 _
    simpa only [id_comp, comp_id] using adj.right_triangle_components m
  evaluation_coevaluation' := by
    ext m
    change F.map (adj.unit.app m) ≫ 𝟙 _ ≫ adj.counit.app (F.obj m) = 𝟙 _ ≫ 𝟙 _
    simpa only [id_comp, comp_id] using adj.left_triangle_components m
end Ordinary

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  {M : Type u'} [Category.{v'} M] [Preadditive M] [Linear ℂ M]
  [HasKernels M] [HasFiniteBiproducts M] [MonoidalLeftAction C M]
  [∀ X Y : M, FiniteDimensional ℂ (X ⟶ Y)]
  [∀ c : C, (MonoidalLeftAction.actionLeft M c).Additive]
  [∀ c : C, (MonoidalLeftAction.actionLeft M c).Linear ℂ]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton M ι)

/-- The actual unit and counit of the constructed right adjoint give an
actual exact pairing of strong module endofunctors. -/
def endRightAdjointExactPairing (F : ModuleAlphaInduction.End C M) :
    ExactPairing F (semisimpleRightAdjoint S F) := by
  let adj := semisimpleRightAdjunction S F
  let coev : 𝟙_ (ModuleAlphaInduction.End C M) ⟶ F ⊗ semisimpleRightAdjoint S F :=
    ⟨adj.unit, semisimpleRightAdjunction_unit_moduleNatural S F⟩
  let ev : semisimpleRightAdjoint S F ⊗ F ⟶ 𝟙_ (ModuleAlphaInduction.End C M) :=
    ⟨adj.counit, semisimpleRightAdjunction_counit_moduleNatural S F⟩
  letI : ExactPairing
      ((forget (C := C) (M := M) (N := M)).obj F)
      ((forget (C := C) (M := M) (N := M)).obj (semisimpleRightAdjoint S F)) :=
    ordinaryAdjunctionExactPairing adj
  apply exactPairingOfFaithful (forget (C := C) (M := M) (N := M)) ev coev
  · change adj.counit = 𝟙 _ ≫ adj.counit ≫ 𝟙 _
    simp only [id_comp, comp_id]
  · change adj.unit = 𝟙 _ ≫ adj.unit ≫ 𝟙 _
    simp only [id_comp, comp_id]

/-- The genuine monoidal category of actual strong module endofunctors
has chosen actual right duals. Semisimplicity of this endofunctor category
is neither assumed nor used: finite semisimplicity is required only of
the underlying module category. -/
def endRightRigidCategory : RightRigidCategory (ModuleAlphaInduction.End C M) where
  rightDual F :=
    { rightDual := semisimpleRightAdjoint S F
      exact := endRightAdjointExactPairing S F }

end Paper18.Category.ModuleFunctor
