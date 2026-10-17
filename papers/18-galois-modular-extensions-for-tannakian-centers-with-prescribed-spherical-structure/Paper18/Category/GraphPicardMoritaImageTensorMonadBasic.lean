import Paper18.Category.GraphPicardMoritaImageBeck
import Paper18.Category.GraphPicardMoritaImageMonoidal
import Paper18.Category.DiagonalAlgebraSemisimpleUnit
import Paper18.Category.NondegenerateBraidedFunctorProjection
import Paper18.Category.ModuleFunctorFiniteInternalHomRightModules

/-! # The genuine adjunction monad is naturally right tensor by its unit

The comparison is the actual rigid projection mate, followed by the actual
target unitor. Its invertibility and unit law are derived without a
braiding on either target or source.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open Functor.LaxMonoidal Functor.OplaxMonoidal
open scoped MonObj
universe v u w u'
namespace Paper18.Category.GraphPicard.MoritaImage
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [HasFiniteBiproducts C] [HasKernels C] [MonoidalCategory C]
  [MonoidalPreadditive C] [MonoidalLinear ℂ C] [RightRigidCategory C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {D : Type u'} [Category.{v} D] [Preadditive D] [Linear ℂ D]
  [HasFiniteBiproducts D] [HasKernels D] [MonoidalCategory D]
  [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  (F : C ⥤ D) [F.Additive] [F.Linear ℂ] [F.Monoidal]
open DiagonalAlgebra NondegenerateBraidedFunctor

/-- The actual projection mate into the actual adjunction monad. -/
def rightTensorComparison (X : C) :
    X ⊗ semisimpleAdjointAlgebra S F ⟶ (semisimpleRightAdjoint S F).obj (F.obj X) :=
  projection F (semisimpleRightAdjunction S F) X (𝟙_ D) ≫
    (semisimpleRightAdjoint S F).map (ρ_ (F.obj X)).hom

@[reassoc] lemma rightTensorComparison_counit (X : C) :
    F.map (rightTensorComparison S F X) ≫ (semisimpleRightAdjunction S F).counit.app (F.obj X) =
      δ F X (semisimpleAdjointAlgebra S F) ≫
        F.obj X ◁ semisimpleAdjointAlgebraCounit S F ≫ (ρ_ (F.obj X)).hom := by
  simp only [rightTensorComparison, F.map_comp, Category.assoc]
  have hn := (semisimpleRightAdjunction S F).counit.naturality (ρ_ (F.obj X)).hom
  simp only [Functor.comp_map, Functor.id_map] at hn
  rw [hn, projection_counit_assoc]
  rfl

instance rightTensorComparison_isIso (X : C) : IsIso (rightTensorComparison S F X) := by
  letI := projection_isIso F (semisimpleRightAdjunction S F) X Xᘁ (𝟙_ D)
  unfold rightTensorComparison
  infer_instance

/-- The actual projection comparisons form a genuine natural isomorphism. -/
def rightTensorComparisonIso :
    (ModuleInternalHom.rightTensorMonad (semisimpleAdjointAlgebra S F) : C ⥤ C) ≅
      (semisimpleRightAdjunction S F).toMonad :=
  NatIso.ofComponents (fun X => asIso (rightTensorComparison S F X)) (fun {X Y} f => by
    apply ((semisimpleRightAdjunction S F).homEquiv _ (F.obj Y)).symm.injective
    change F.map ((f ▷ semisimpleAdjointAlgebra S F) ≫ rightTensorComparison S F Y) ≫
      (semisimpleRightAdjunction S F).counit.app (F.obj Y) =
      F.map (rightTensorComparison S F X ≫ (semisimpleRightAdjoint S F).map (F.map f)) ≫
        (semisimpleRightAdjunction S F).counit.app (F.obj Y)
    simp only [F.map_comp, Category.assoc]
    have hn := (semisimpleRightAdjunction S F).counit.naturality (F.map f)
    simp only [Functor.comp_map, Functor.id_map] at hn
    rw [hn, rightTensorComparison_counit, rightTensorComparison_counit_assoc]
    rw [← δ_natural_left_assoc, ← whisker_exchange_assoc, rightUnitor_naturality (F.map f)])

/-- The genuine monad unit inserts the actual algebra unit, with the
actual source right unitor. -/
lemma rightTensorComparison_unit (X : C) :
    (ρ_ X).inv ≫ (X ◁ η[semisimpleAdjointAlgebra S F]) ≫ rightTensorComparison S F X =
      (semisimpleRightAdjunction S F).unit.app X := by
  let adj := semisimpleRightAdjunction S F
  apply (adj.homEquiv X (F.obj X)).symm.injective
  change F.map ((ρ_ X).inv ≫ (X ◁ η[semisimpleAdjointAlgebra S F]) ≫
      rightTensorComparison S F X) ≫ adj.counit.app (F.obj X) =
      F.map (adj.unit.app X) ≫ adj.counit.app (F.obj X)
  rw [adj.left_triangle_components]
  simp only [F.map_comp, Category.assoc]
  rw [rightTensorComparison_counit,
    ← Category.assoc (F.map (X ◁ η[semisimpleAdjointAlgebra S F]))]
  rw [← δ_natural_right F X η[semisimpleAdjointAlgebra S F]]
  simp only [Category.assoc]
  rw [← MonoidalCategory.whiskerLeft_comp_assoc,
    semisimpleAdjointAlgebra_one_counit, Functor.OplaxMonoidal.right_unitality_hom,
    ← F.map_comp, Iso.inv_hom_id, F.map_id]

end Paper18.Category.GraphPicard.MoritaImage
