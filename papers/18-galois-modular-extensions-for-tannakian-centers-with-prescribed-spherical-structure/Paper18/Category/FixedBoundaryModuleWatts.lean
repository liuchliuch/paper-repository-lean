import Paper18.Category.FixedBoundaryModuleRegular

/-!
# Actual Hom equivalence for regular module functors

Evaluation at the tensor unit identifies actual module natural
transformations with actual morphisms between the representing objects.
The inverse is constructed by right tensoring and the actual representing
isomorphisms.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open scoped MonoidalLeftAction
universe v u v' u' v'' u''
namespace Paper18.Category.ModuleFunctor

section Inverse
variable (C : Type u) [Category.{v} C] [MonoidalCategory C]
  {M : Type u'} [Category.{v'} M] [MonoidalLeftAction C M]
  {N : Type u''} [Category.{v''} N] [MonoidalLeftAction C N]
  {F H : M ⥤ N} [F.LeftLinear C] [H.LeftLinear C]

instance moduleNatural_inv (e : F ≅ H) [IsModuleNatural C e.hom] :
    IsModuleNatural C e.inv where
  lineator X Y := by
    apply (cancel_mono (e.hom.app (X ⊙ₗ Y))).mp
    simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
    rw [IsModuleNatural.lineator,
      ← MonoidalLeftAction.actionHomRight_comp_assoc, Iso.inv_hom_id_app,
      MonoidalLeftAction.actionHomRight_id, Category.id_comp]

end Inverse

section Regular
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- The actual module natural transformation induced by a morphism between
right tensor factors. -/
def tensorRightTransformation {U V : C} (f : U ⟶ V) : tensorRight U ⟶ tensorRight V where
  app X := X ◁ f
  naturality {X Y} g := by
    change (g ▷ U) ≫ (Y ◁ f) = (X ◁ f) ≫ (g ▷ V)
    exact (whisker_exchange g f).symm

instance tensorRightTransformation_moduleNatural {U V : C} (f : U ⟶ V) :
    IsModuleNatural C (tensorRightTransformation f) where
  lineator X Y := by
    change (α_ X Y U).inv ≫ ((X ⊗ Y) ◁ f) =
      (X ◁ (Y ◁ f)) ≫ (α_ X Y V).inv
    monoidal

variable (F H : C ⥤ C) [F.LeftLinear C] [H.LeftLinear C]

@[simp] theorem regularRepresentationIso_hom_unit :
    (regularRepresentationIso F).hom.app (𝟙_ C) = (λ_ (F.obj (𝟙_ C))).inv := by
  rw [regularRepresentationIso_hom]
  have hu : (ρ_ (𝟙_ C)).inv = (λ_ (𝟙_ C)).inv := by monoidal
  rw [hu]
  exact (Functor.OplaxLeftLinear.δₗ_unitality_inv F (C := C) (𝟙_ C)).symm

@[simp] theorem regularRepresentationIso_inv_unit :
    (regularRepresentationIso F).inv.app (𝟙_ C) = (λ_ (F.obj (𝟙_ C))).hom := by
  have he : (regularRepresentationIso F).app (𝟙_ C) = (λ_ (F.obj (𝟙_ C))).symm :=
    Iso.ext (regularRepresentationIso_hom_unit F)
  change ((regularRepresentationIso F).app (𝟙_ C)).inv = _
  rw [he]
  rfl

/-- Extend an actual map between unit values to an actual module natural
transformation on every object of the regular module category. -/
def transformationOfUnit (f : F.obj (𝟙_ C) ⟶ H.obj (𝟙_ C)) : F ⟶ H :=
  (regularRepresentationIso F).hom ≫ tensorRightTransformation f ≫
    (regularRepresentationIso H).inv

instance transformationOfUnit_moduleNatural (f : F.obj (𝟙_ C) ⟶ H.obj (𝟙_ C)) :
    IsModuleNatural C (transformationOfUnit F H f) := by
  dsimp [transformationOfUnit]
  infer_instance

@[simp] theorem transformationOfUnit_app_unit (f : F.obj (𝟙_ C) ⟶ H.obj (𝟙_ C)) :
    (transformationOfUnit F H f).app (𝟙_ C) = f := by
  simp only [transformationOfUnit, NatTrans.comp_app, regularRepresentationIso_hom_unit,
    regularRepresentationIso_inv_unit, tensorRightTransformation]
  monoidal

/-- An actual categorical Eilenberg--Watts Hom equivalence, with no
classification of module functors or scalar-coordinate fields assumed. -/
def regularModuleHomEquiv :
    {τ : F ⟶ H // IsModuleNatural C τ} ≃ (F.obj (𝟙_ C) ⟶ H.obj (𝟙_ C)) where
  toFun τ := τ.val.app (𝟙_ C)
  invFun f := ⟨transformationOfUnit F H f, inferInstance⟩
  left_inv τ := by
    apply Subtype.ext
    letI := τ.property
    apply moduleNatTrans_ext
    exact transformationOfUnit_app_unit F H _
  right_inv f := transformationOfUnit_app_unit F H f

end Regular
end Paper18.Category.ModuleFunctor
