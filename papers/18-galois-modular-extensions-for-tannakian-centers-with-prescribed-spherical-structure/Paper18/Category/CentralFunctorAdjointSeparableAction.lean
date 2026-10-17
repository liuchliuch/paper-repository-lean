import Paper18.Category.ModuleFunctorAdjointNaturality
import Paper18.Category.FixedBoundaryModuleStrong
import Paper18.Category.NondegenerateBraidedFunctorProjection

/-! # The native action associated to an actual strong tensor functor

The target is acted on through the actual functor. The original functor
and its actual right adjoint are strong module functors, and their actual
adjunction unit and counit are module natural. This constructs the native
action data used in adjoint-algebra separability arguments without assuming
a splitting of the counit.
-/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open Functor.LaxMonoidal Functor.OplaxMonoidal
open scoped MonoidalLeftAction
universe v u v' u'
namespace Paper18.Category.CentralFunctorAdjointSeparable
open MonoidalLeftAction
attribute [local instance] endofunctorMonoidalCategory
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {D : Type u'} [Category.{v'} D] [MonoidalCategory D]
  (F : C ⥤ D) [F.Monoidal]

/-- The actual left action obtained by pulling back the tensor action. -/
def targetAction : MonoidalLeftAction C D :=
  actionOfMonoidalFunctorToEndofunctorMop (F ⋙ curriedActionMop D D)

section Action

@[simp] lemma targetAction_obj (X : C) (Y : D) :
    letI := targetAction F
    X ⊙ₗ Y = F.obj X ⊗ Y := rfl

@[simp] lemma targetAction_map_left {X X' : C} (f : X ⟶ X') (Y : D) :
    letI := targetAction F
    f ⊵ₗ Y = F.map f ▷ Y := rfl

@[simp] lemma targetAction_map_right (X : C) {Y Y' : D} (f : Y ⟶ Y') :
    letI := targetAction F
    X ⊴ₗ f = F.obj X ◁ f := rfl

@[simp] lemma targetAction_associator (X Y : C) (Z : D) :
    letI := targetAction F
    (αₗ X Y Z).hom = δ F X Y ▷ Z ≫ (α_ (F.obj X) (F.obj Y) Z).hom := by
  dsimp [targetAction, actionOfMonoidalFunctorToEndofunctorMop]
  rfl

@[simp] lemma targetAction_unitor (Z : D) :
    letI := targetAction F
    (λₗ[C] Z).hom = η F ▷ Z ≫ (λ_ Z).hom := by
  dsimp [targetAction, actionOfMonoidalFunctorToEndofunctorMop]
  rfl

/-- The actual tensorator is a genuine native strong module lineator. -/
def functorLaxLeftLinear :
    letI := targetAction F
    F.LaxLeftLinear C := by
  letI := targetAction F
  exact {
    μₗ X Y := μ F X Y
    μₗ_naturality_left {X X'} f Y := Functor.LaxMonoidal.μ_natural_left F f Y
    μₗ_naturality_right X {Y Y'} f := Functor.LaxMonoidal.μ_natural_right F X f
    μₗ_associativity X Y Z := by
      change μ F (X ⊗ Y) Z ≫ F.map (α_ X Y Z).hom = _
      rw [targetAction_associator]
      simp only [targetAction_map_right, Category.assoc]
      change μ F (X ⊗ Y) Z ≫ F.map (α_ X Y Z).hom =
        δ F X Y ▷ F.obj Z ≫ (α_ (F.obj X) (F.obj Y) (F.obj Z)).hom ≫
          F.obj X ◁ μ F Y Z ≫ μ F X (Y ⊗ Z)
      rw [← Functor.LaxMonoidal.associativity, ← comp_whiskerRight_assoc,
      Functor.Monoidal.δ_μ, id_whiskerRight, Category.id_comp]
    μₗ_unitality Y := by
      rw [targetAction_unitor]
      change η F ▷ F.obj Y ≫ (λ_ (F.obj Y)).hom =
        μ F (𝟙_ C) Y ≫ F.map (λ_ Y).hom
      rw [Functor.LaxMonoidal.left_unitality, ← comp_whiskerRight_assoc,
        Functor.Monoidal.η_ε, id_whiskerRight, Category.id_comp]
 }

/-- Both lineators and all their coherence are constructed from the actual
strong tensor structure, without a target braiding. -/
def functorLeftLinear :
    letI := targetAction F
    F.LeftLinear C := by
  letI := targetAction F
  letI := functorLaxLeftLinear F
  letI (X Y : C) : IsIso (Functor.LaxLeftLinear.μₗ F X Y) := by
    change IsIso (μ F X Y)
    infer_instance
  exact ModuleFunctor.leftLinearOfLax F

@[simp] lemma functor_lineator (X Y : C) :
    letI := targetAction F
    letI := functorLeftLinear F
    Functor.LaxLeftLinear.μₗ F X Y = μ F X Y := rfl

section RightAdjoint
variable [RightRigidCategory C] {R : D ⥤ C} (adj : F ⊣ R)

/-- Rigidity constructs the actual strong module structure on the right
adjoint; its inverse lineators are not extra inputs. -/
def rightAdjointLeftLinear :
    letI := targetAction F
    letI := functorLeftLinear F
    R.LeftLinear C := by
  letI := targetAction F
  letI := functorLeftLinear F
  exact ModuleFunctor.rightAdjointLeftLinear (C := C) F adj

/-- The actual unit is module natural for the constructed strong adjoint. -/
theorem unit_moduleNatural :
    letI := targetAction F
    letI := functorLeftLinear F
    letI := rightAdjointLeftLinear F adj
    ModuleFunctor.IsModuleNatural C adj.unit :=
by
  letI := targetAction F
  letI := functorLeftLinear F
  exact ModuleFunctor.rightAdjointUnit_moduleNatural (C := C) F adj

/-- The actual counit is module natural, without assuming a module-natural
section or any form of dominance. -/
theorem counit_moduleNatural :
    letI := targetAction F
    letI := functorLeftLinear F
    letI := rightAdjointLeftLinear F adj
    ModuleFunctor.IsModuleNatural C adj.counit :=
by
  letI := targetAction F
  letI := functorLeftLinear F
  exact ModuleFunctor.rightAdjointCounit_moduleNatural (C := C) F adj

end RightAdjoint
end Action
end Paper18.Category.CentralFunctorAdjointSeparable
