import Paper18.Category.FixedBoundaryModules
import Paper18.Category.RelativeTensorCoherence

/-!
# Actual balanced tensor comparison for transported internal modules

A braided tensor functor transports the balancing relation and the module
linearity equation. Its tensorator therefore descends to an actual map
between the relative tensor products of the transported modules.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped MonObj Obj
universe v u v' u'
namespace Paper18.Category.InternalModule
open RelativeTensor
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [RightRigidCategory C] [HasCoequalizers C]
  {D : Type u'} [Category.{v'} D] [MonoidalCategory D] [BraidedCategory D]
  [RightRigidCategory D] [HasCoequalizers D]
  (F : C ⥤ D) [F.Braided] {A : C} [MonObj A] [IsCommMonObj A]

instance mapModuleAlgebra_comm : IsCommMonObj (F.obj A) := Functor.isCommMonObj_obj

@[simp] theorem mapModule_action (M : Mod_ C A) :
    γ[F.obj A,(mapModuleObj F M).X] =
      Functor.LaxMonoidal.μ F A M.X ≫ F.map γ[A,M.X] := rfl

@[reassoc] theorem mapModule_rightAction (M : Mod_ C A) :
    rightAction (mapModuleObj F M) =
      Functor.LaxMonoidal.μ F M.X A ≫ F.map (rightAction M) := by
  unfold rightAction
  simp only [mapModuleObj_X]
  rw [mapModule_action, ← Functor.LaxBraided.braided_assoc, ← F.map_comp]

/-- The actual three-fold comparison entering the transported balancing
relations. -/
def balancingTensorator (M N : Mod_ C A) :
    ((mapModuleObj F M).X ⊗ F.obj A) ⊗ (mapModuleObj F N).X ⟶
      F.obj ((M.X ⊗ A) ⊗ N.X) :=
  Functor.LaxMonoidal.μ F M.X A ▷ F.obj N.X ≫
    Functor.LaxMonoidal.μ F (M.X ⊗ A) N.X

@[reassoc] theorem mapModule_parallelLeft (M N : Mod_ C A) :
    parallelLeft (mapModuleObj F M) (mapModuleObj F N) ≫
        Functor.LaxMonoidal.μ F M.X N.X =
      balancingTensorator F M N ≫ F.map (parallelLeft M N) := by
  unfold parallelLeft balancingTensorator
  simp only [mapModuleObj_X]
  rw [mapModule_rightAction, comp_whiskerRight]
  simp only [Category.assoc]
  rw [Functor.LaxMonoidal.μ_natural_left]

@[reassoc] theorem mapModule_parallelRight (M N : Mod_ C A) :
    parallelRight (mapModuleObj F M) (mapModuleObj F N) ≫
        Functor.LaxMonoidal.μ F M.X N.X =
      balancingTensorator F M N ≫ F.map (parallelRight M N) := by
  unfold parallelRight balancingTensorator
  simp only [mapModuleObj_X]
  rw [mapModule_action, whiskerLeft_comp]
  simp only [Category.assoc, F.map_comp]
  rw [Functor.LaxMonoidal.μ_natural_right]
  rw [Functor.LaxMonoidal.associativity_assoc]

/-- The transported quotient map is actually balanced. -/
theorem mapModuleTensor_balanced (M N : Mod_ C A) :
    RelativeTensor.Balanced (mapModuleObj F M) (mapModuleObj F N)
      (Functor.LaxMonoidal.μ F M.X N.X ≫ F.map (π M N)) := by
  unfold RelativeTensor.Balanced
  rw [mapModule_parallelLeft_assoc, mapModule_parallelRight_assoc,
    ← F.map_comp, ← F.map_comp, condition M N]

/-- The transported quotient map also intertwines the actual left algebra
action; this is independent of semisimplicity. -/
theorem mapModuleTensor_linear (M N : Mod_ C A) :
    (α_ (F.obj A) (mapModuleObj F M).X (mapModuleObj F N).X).inv ≫
        γ[F.obj A,(mapModuleObj F M).X] ▷ (mapModuleObj F N).X ≫
          (Functor.LaxMonoidal.μ F M.X N.X ≫ F.map (π M N)) =
      (F.obj A ◁ (Functor.LaxMonoidal.μ F M.X N.X ≫ F.map (π M N))) ≫
        γ[F.obj A,(mapModuleObj F (M ⊗ N)).X] := by
  simp only [mapModuleObj_X]
  rw [mapModule_action, mapModule_action]
  simp only [comp_whiskerRight, whiskerLeft_comp, Category.assoc]
  rw [Functor.LaxMonoidal.μ_natural_left_assoc]
  have ha := Functor.LaxMonoidal.associativity F A M.X N.X
  have ha' : (α_ (F.obj A) (F.obj M.X) (F.obj N.X)).inv ≫
      Functor.LaxMonoidal.μ F A M.X ▷ F.obj N.X ≫
        Functor.LaxMonoidal.μ F (A ⊗ M.X) N.X =
    (F.obj A ◁ Functor.LaxMonoidal.μ F M.X N.X) ≫
      Functor.LaxMonoidal.μ F A (M.X ⊗ N.X) ≫ F.map (α_ A M.X N.X).inv := by
    apply (cancel_mono (F.map (α_ A M.X N.X).hom)).mp
    simp only [Category.assoc, ← F.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id,
      Category.comp_id]
    rw [ha]
    simp
  slice_lhs 1 3 => rw [ha']
  simp only [Category.assoc, ← F.map_comp]
  rw [← π_action, F.map_comp, ← Functor.LaxMonoidal.μ_natural_right_assoc]
  rfl

/-- The genuine tensor comparison on internal module categories. -/
def mapModulesTensorHom (M N : Mod_ C A) :
    (mapModules F).obj M ⊗ (mapModules F).obj N ⟶ (mapModules F).obj (M ⊗ N) :=
  descModule (mapModuleObj F M) (mapModuleObj F N) (mapModuleObj F (M ⊗ N))
    (Functor.LaxMonoidal.μ F M.X N.X ≫ F.map (π M N))
    (mapModuleTensor_balanced F M N) (mapModuleTensor_linear F M N)

@[reassoc (attr := simp)] theorem π_mapModulesTensorHom (M N : Mod_ C A) :
    π (mapModuleObj F M) (mapModuleObj F N) ≫ (mapModulesTensorHom F M N).hom =
      Functor.LaxMonoidal.μ F M.X N.X ≫ F.map (π M N) := π_desc _ _ _ _

end Paper18.Category.InternalModule
