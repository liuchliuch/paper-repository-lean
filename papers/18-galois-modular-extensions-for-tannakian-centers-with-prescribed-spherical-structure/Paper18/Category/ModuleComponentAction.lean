import Paper18.Category.ModuleComponentBasic
import Paper18.Category.FixedBoundaryModuleStrong

/-! # The native action restricted to an actual simple component -/
noncomputable section
open Classical CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped MonoidalLeftAction
universe v u vM uM w
namespace Paper18.Category.ModuleComponent
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {M : Type uM} [Category.{vM} M] [Preadditive M] [Linear ℂ M]
  [HasKernels M] [HasFiniteBiproducts M]
  [∀ X Y : M, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalLeftAction C M]
  [∀ X : C, (MonoidalLeftAction.actionLeft M X).Additive]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton M ι) (i : ι)

/-- Actual component restriction of the native monoidal action. -/
instance leftAction : MonoidalLeftAction C (Component (C := C) S i) where
  actionObj X Y := ⟨X ⊙ₗ Y.obj, action_mem S i X Y.property⟩
  actionHomLeft f Y := f ⊵ₗ Y.obj
  actionHomRight X Y Y' f := X ⊴ₗ (show Y.obj ⟶ Y'.obj from f)
  actionHom {X X'} {Y Y'} f g := f ⊙ₗₘ (show Y.obj ⟶ Y'.obj from g)
  actionAssocIso X Y Z := (property (C := C) S i).isoMk (αₗ X Y Z.obj)
  actionUnitIso Y := (property (C := C) S i).isoMk (λₗ[C] Y.obj)
  actionHom_def {X X'} {Y Y'} f g :=
    MonoidalLeftAction.actionHom_def f (show Y.obj ⟶ Y'.obj from g)
  actionHomRight_id X Y := MonoidalLeftAction.actionHomRight_id X Y.obj
  id_actionHomLeft X Y := MonoidalLeftAction.id_actionHomLeft X Y.obj
  actionHom_comp {X X' X''} {Y Y' Y''} f₁ f₂ g₁ g₂ :=
    MonoidalLeftAction.actionHom_comp f₁ f₂
      (show Y.obj ⟶ Y'.obj from g₁) (show Y'.obj ⟶ Y''.obj from g₂)
  actionAssocIso_hom_naturality {X X' Y Y'} {Z Z'} f g h :=
    MonoidalLeftAction.actionAssocIso_hom_naturality f g (show Z.obj ⟶ Z'.obj from h)
  actionUnitIso_hom_naturality {Y Y'} f :=
    MonoidalLeftAction.actionUnitIso_hom_naturality (show Y.obj ⟶ Y'.obj from f)
  whiskerLeft_actionHomLeft X _ _ f Y :=
    MonoidalLeftAction.whiskerLeft_actionHomLeft X f Y.obj
  whiskerRight_actionHomLeft X f Y :=
    MonoidalLeftAction.whiskerRight_actionHomLeft X f Y.obj
  associator_actionHom X Y Z W := MonoidalLeftAction.associator_actionHom X Y Z W.obj
  leftUnitor_actionHom X Y := MonoidalLeftAction.leftUnitor_actionHom X Y.obj
  rightUnitor_actionHom X Y := MonoidalLeftAction.rightUnitor_actionHom X Y.obj

instance actionLeft_additive (X : C) :
    (MonoidalLeftAction.actionLeft (Component (C := C) S i) X).Additive where
  map_add {Y Z} f g := by
    change X ⊴ₗ ((f : Y.obj ⟶ Z.obj) + g) = X ⊴ₗ (f : Y.obj ⟶ Z.obj) + X ⊴ₗ (g : Y.obj ⟶ Z.obj)
    exact (MonoidalLeftAction.actionLeft M X).map_add

instance actionLeft_linear [∀ X : C, (MonoidalLeftAction.actionLeft M X).Linear ℂ]
    (X : C) : (MonoidalLeftAction.actionLeft (Component (C := C) S i) X).Linear ℂ where
  map_smul {Y Z} f r := by
    change X ⊴ₗ (r • (f : Y.obj ⟶ Z.obj)) = r • (X ⊴ₗ (f : Y.obj ⟶ Z.obj))
    exact (MonoidalLeftAction.actionLeft M X).map_smul r f

/-- The actual inclusion has identity lax module lineators. -/
def inclusionLaxLeftLinear : ((property (C := C) S i).ι).LaxLeftLinear C where
  μₗ _ _ := 𝟙 _
  μₗ_naturality_left {X X'} f Y := by
    change f ⊵ₗ Y.obj ≫ 𝟙 _ = 𝟙 _ ≫ f ⊵ₗ Y.obj
    simp
  μₗ_naturality_right X Y Y' f := by
    change X ⊴ₗ (f : Y.obj ⟶ Y'.obj) ≫ 𝟙 _ = 𝟙 _ ≫ X ⊴ₗ (f : Y.obj ⟶ Y'.obj)
    simp
  μₗ_associativity X Y Z := by
    change 𝟙 _ ≫ (αₗ X Y Z.obj).hom =
      (αₗ X Y Z.obj).hom ≫ (X ⊴ₗ 𝟙 _) ≫ 𝟙 _
    simp
  μₗ_unitality Y := by
    change (λₗ[C] Y.obj).hom = 𝟙 _ ≫ (λₗ[C] Y.obj).hom
    simp

/-- The actual inclusion is a strong native module functor. -/
def inclusionLeftLinear : ((property (C := C) S i).ι).LeftLinear C := by
  letI := inclusionLaxLeftLinear (C := C) S i
  letI (X : C) (Y : Component (C := C) S i) :
      IsIso (Functor.LaxLeftLinear.μₗ ((property (C := C) S i).ι) X Y) :=
    inferInstanceAs (IsIso (𝟙 (X ⊙ₗ Y.obj)))
  exact ModuleFunctor.leftLinearOfLax (C := C) ((property (C := C) S i).ι)

section ActingLinearity
variable [Preadditive C]
  [∀ Y : M, (MonoidalLeftAction.actionRight C Y).Additive]

instance actionRight_additive (Y : Component (C := C) S i) :
    (MonoidalLeftAction.actionRight C Y).Additive where
  map_add {X Z} f g := by
    change (f + g) ⊵ₗ Y.obj = f ⊵ₗ Y.obj + g ⊵ₗ Y.obj
    exact (MonoidalLeftAction.actionRight C Y.obj).map_add

instance actionRight_linear [Linear ℂ C]
    [∀ Y : M, (MonoidalLeftAction.actionRight C Y).Linear ℂ]
    (Y : Component (C := C) S i) :
    (MonoidalLeftAction.actionRight C Y).Linear ℂ where
  map_smul f r := by
    change (r • f) ⊵ₗ Y.obj = r • (f ⊵ₗ Y.obj)
    exact (MonoidalLeftAction.actionRight C Y.obj).map_smul r f

end ActingLinearity

end Paper18.Category.ModuleComponent
