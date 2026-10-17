import Paper18.Category.ModuleAlphaInductionEnd
import Paper18.Category.ModuleAlphaInductionCentral
import Paper18.Category.DrinfeldLinear

/-! # Actual positive and negative alpha-induction functors -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open MonoidalLeftAction MonoidalOpposite
universe v u vM uM
namespace Paper18.Category.ModuleAlphaInduction
variable (C : Type u) [Category.{v} C] [MonoidalCategory C]
  (M : Type uM) [Category.{vM} M] [Preadditive M] [Linear ℂ M]
  [MonoidalLeftAction C M]
  [∀ X : C, (MonoidalLeftAction.actionLeft M X).Additive]
  [∀ X : C, (MonoidalLeftAction.actionLeft M X).Linear ℂ]

/-- Actual central module endofunctors carry the genuine native strong
lineator together with actual additivity and complex linearity. -/
def centralEnd (Z : Center C) : End C M where
  toFunctor := centralFunctor Z
  leftLinear := inferInstance
  additive := inferInstanceAs ((MonoidalLeftAction.actionLeft M Z.1).Additive)
  linear := inferInstanceAs ((MonoidalLeftAction.actionLeft M Z.1).Linear ℂ)

/-- The actual central action on the actual category of module endofunctors. -/
def centralAction : Center C ⥤ End C M where
  obj := centralEnd C M
  map f := ⟨centralMap f,
    show ModuleFunctor.IsModuleNatural C (centralMap f) from inferInstance⟩
  map_id Z := by
    apply Subtype.ext
    ext m
    change (𝟙 Z.1) ⊵ₗ m = 𝟙 _
    simp
  map_comp f g := by
    apply Subtype.ext
    ext m
    change (f.f ≫ g.f) ⊵ₗ m = (f.f ⊵ₗ m) ≫ (g.f ⊵ₗ m)
    exact comp_actionHomLeft _ _ _

/-- The composition convention for native endofunctors makes the actual
central action covariantly strong monoidal in the monoidal opposite. -/
def centralActionMop : Center C ⥤ (End C M)ᴹᵒᵖ :=
  centralAction C M ⋙ mopFunctor _

@[simp] theorem centralAction_forget :
    centralAction C M ⋙ ModuleFunctor.forget = Center.forget C ⋙ MonoidalLeftAction.curriedAction C M := rfl

section Linear
variable [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [∀ m : M, (MonoidalLeftAction.actionRight C m).Additive]
  [∀ m : M, (MonoidalLeftAction.actionRight C m).Linear ℂ]

instance centralAction_additive : (centralAction C M).Additive where
  map_add {Z W} f g := by
    apply Subtype.ext
    ext m
    change (f.f + g.f) ⊵ₗ m = (f.f ⊵ₗ m) + (g.f ⊵ₗ m)
    exact (MonoidalLeftAction.actionRight C m).map_add

instance centralAction_linear : (centralAction C M).Linear ℂ where
  map_smul f r := by
    apply Subtype.ext
    ext m
    change (r • f.f) ⊵ₗ m = r • (f.f ⊵ₗ m)
    exact (MonoidalLeftAction.actionRight C m).map_smul _ _

end Linear

variable [BraidedCategory C]

/-- Positive alpha induction uses the actual positive half-braiding. -/
def positive : C ⥤ End C M := Drinfeld.positive C ⋙ centralAction C M

/-- Negative alpha induction uses the actual negative half-braiding. -/
def negative : C ⥤ End C M := Drinfeld.negative C ⋙ centralAction C M

/-- Positive alpha induction with the actual covariant composition tensor convention. -/
def positiveMop : C ⥤ (End C M)ᴹᵒᵖ := positive C M ⋙ mopFunctor _

/-- Negative alpha induction with the actual covariant composition tensor convention. -/
def negativeMop : C ⥤ (End C M)ᴹᵒᵖ := negative C M ⋙ mopFunctor _

@[simp] theorem positive_obj (X : C) (m : M) :
    ((positive C M).obj X).toFunctor.obj m = X ⊙ₗ m := rfl
@[simp] theorem negative_obj (X : C) (m : M) :
    ((negative C M).obj X).toFunctor.obj m = X ⊙ₗ m := rfl
@[simp] theorem positive_map {X Y : C} (f : X ⟶ Y) (m : M) :
    ((positive C M).map f).val.app m = f ⊵ₗ m := rfl
@[simp] theorem negative_map {X Y : C} (f : X ⟶ Y) (m : M) :
    ((negative C M).map f).val.app m = f ⊵ₗ m := rfl

@[simp] theorem positive_δ (X Y : C) (m : M) :
    Functor.OplaxLeftLinear.δₗ ((positive C M).obj X).toFunctor Y m =
      (αₗ X Y m).inv ≫ (β_ X Y).hom ⊵ₗ m ≫ (αₗ Y X m).hom := rfl
@[simp] theorem negative_δ (X Y : C) (m : M) :
    Functor.OplaxLeftLinear.δₗ ((negative C M).obj X).toFunctor Y m =
      (αₗ X Y m).inv ≫ (β_ Y X).inv ⊵ₗ m ≫ (αₗ Y X m).hom := rfl

@[simp] theorem positive_μ (X Y : C) (m : M) :
    Functor.LaxLeftLinear.μₗ ((positive C M).obj X).toFunctor Y m =
      (αₗ Y X m).inv ≫ (β_ X Y).inv ⊵ₗ m ≫ (αₗ X Y m).hom := by
  simpa only [centralLineator, Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv,
    actionRight_map, Category.assoc] using central_μ ((Drinfeld.positive C).obj X) Y m
@[simp] theorem negative_μ (X Y : C) (m : M) :
    Functor.LaxLeftLinear.μₗ ((negative C M).obj X).toFunctor Y m =
      (αₗ Y X m).inv ≫ (β_ Y X).hom ⊵ₗ m ≫ (αₗ X Y m).hom := by
  simpa only [centralLineator, Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv,
    actionRight_map, Category.assoc] using central_μ ((Drinfeld.negative C).obj X) Y m

@[simp] theorem positive_forget :
    positive C M ⋙ ModuleFunctor.forget = MonoidalLeftAction.curriedAction C M := rfl
@[simp] theorem negative_forget :
    negative C M ⋙ ModuleFunctor.forget = MonoidalLeftAction.curriedAction C M := rfl

section Linear
variable [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [∀ m : M, (MonoidalLeftAction.actionRight C m).Additive]
  [∀ m : M, (MonoidalLeftAction.actionRight C m).Linear ℂ]
instance positive_additive : (positive C M).Additive := by unfold positive; infer_instance
instance positive_linear : (positive C M).Linear ℂ := by unfold positive; infer_instance
instance negative_additive : (negative C M).Additive := by unfold negative; infer_instance
instance negative_linear : (negative C M).Linear ℂ := by unfold negative; infer_instance
end Linear

end Paper18.Category.ModuleAlphaInduction
