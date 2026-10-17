import Paper18.Category.ModuleFunctorDiagonalLinearEnd

/-! # The actual postcomposition and precomposition pair action -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits MonoidalLeftAction MonoidalOpposite
open scoped BigOperators MonoidalLeftAction
universe v u vM uM vN uN
namespace Paper18.Category.ModuleFunctor.DiagonalAction
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  {M : Type uM} [Category.{vM} M] [Preadditive M] [Linear ℂ M]
  [MonoidalLeftAction C M]
  {N : Type uN} [Category.{vN} N] [Preadditive N] [Linear ℂ N]
  [MonoidalLeftAction C N]
  [∀ X : C, (actionLeft M X).Additive] [∀ X : C, (actionLeft M X).Linear ℂ]
  [∀ X : C, (actionLeft N X).Additive] [∀ X : C, (actionLeft N X).Linear ℂ]

/-- Genuine module structures are retained on the objects, though the
action accepts every ordinary transformation. -/
def pairObject (X Y : C) (F : Ordinary C M N) : Ordinary C M N :=
  ofBundled {
    toFunctor := actionLeft M Y ⋙ toFunctor F ⋙ actionLeft N X
    leftLinear := by
      change (((ModuleAlphaInduction.positive C M).obj Y).toFunctor ⋙
        toFunctor F ⋙ ((ModuleAlphaInduction.positive C N).obj X).toFunctor).LeftLinear C
      infer_instance
    additive := inferInstance
    linear := inferInstance }

@[simp] lemma pairObject_obj (X Y : C) (F : Ordinary C M N) (m : M) :
    (toFunctor (pairObject X Y F)).obj m = X ⊙ₗ (toFunctor F).obj (Y ⊙ₗ m) := rfl

/-- The actual ordinary endofunctor underlying an external pair. -/
def pairEnd (X Y : C) : Ordinary C M N ⥤ Ordinary C M N where
  obj := pairObject X Y
  map τ := Functor.whiskerRight (Functor.whiskerLeft (actionLeft M Y) τ)
    (actionLeft N X)
  map_id F := by
    apply ordinary_hom_ext (F := pairObject X Y F) (G := pairObject X Y F)
    intro m
    change X ⊴ₗ (𝟙 ((toFunctor F).obj (Y ⊙ₗ m))) = 𝟙 _
    exact actionHomRight_id _ _
  map_comp {F G H} τ σ := by
    apply ordinary_hom_ext (F := pairObject X Y F) (G := pairObject X Y H)
    intro m
    change X ⊴ₗ (τ.app (Y ⊙ₗ m) ≫ σ.app (Y ⊙ₗ m)) = _
    exact actionHomRight_comp _ _ _

instance pairEnd_additive (X Y : C) : (pairEnd (M := M) (N := N) X Y).Additive where
  map_add {F G} τ σ := by
    ext m
    exact (actionLeft N X).map_add

instance pairEnd_linear (X Y : C) : (pairEnd (M := M) (N := N) X Y).Linear ℂ where
  map_smul τ r := by
    ext m
    exact (actionLeft N X).map_smul _ _

/-- Ordinary naturality in the precomposition object. -/
def pairMapRight (X : C) {Y Z : C} (f : Y ⟶ Z) :
    pairEnd (M := M) (N := N) X Y ⟶ pairEnd X Z where
  app F := Functor.whiskerRight
    (Functor.whiskerRight ((curriedAction C M).map f) (toFunctor F)) (actionLeft N X)
  naturality {F G} τ := by
    ext m
    change X ⊴ₗ τ.app (Y ⊙ₗ m) ≫ X ⊴ₗ (toFunctor G).map (f ⊵ₗ m) =
      X ⊴ₗ (toFunctor F).map (f ⊵ₗ m) ≫ X ⊴ₗ τ.app (Z ⊙ₗ m)
    rw [← actionHomRight_comp, ← actionHomRight_comp]
    exact congrArg (fun k => X ⊴ₗ k)
      ((show toFunctor F ⟶ toFunctor G from τ).naturality (f ⊵ₗ m)).symm

/-- Ordinary naturality in the postcomposition object. -/
def pairMapLeft {X Z : C} (f : X ⟶ Z) (Y : C) :
    pairEnd (M := M) (N := N) X Y ⟶ pairEnd Z Y where
  app F := Functor.whiskerLeft (actionLeft M Y ⋙ toFunctor F)
    ((curriedAction C N).map f)
  naturality {F G} τ := by
    ext m
    change X ⊴ₗ τ.app (Y ⊙ₗ m) ≫ f ⊵ₗ (toFunctor G).obj (Y ⊙ₗ m) =
      f ⊵ₗ (toFunctor F).obj (Y ⊙ₗ m) ≫ Z ⊴ₗ τ.app (Y ⊙ₗ m)
    exact action_exchange _ _

/-- The pair functor in the precomposition variable, with its actual
complex-linear endofunctor objects. -/
def pairRight (X : C) : Cᴹᵒᵖ ⥤ LinearEnd.Cat (Ordinary C M N) where
  obj Y := LinearEnd.ofFunctor (pairEnd X Y.unmop)
  map f := pairMapRight X f.unmop
  map_id Y := by
    apply LinearEnd.hom_ext
      (F := LinearEnd.ofFunctor (pairEnd X Y.unmop))
      (G := LinearEnd.ofFunctor (pairEnd X Y.unmop))
    intro F
    apply ordinary_hom_ext (C := C) (M := M) (N := N)
    intro m
    change X ⊴ₗ (toFunctor F).map ((𝟙 Y.unmop) ⊵ₗ m) = 𝟙 _
    simp
  map_comp {Y Z W} f g := by
    apply LinearEnd.hom_ext
      (F := LinearEnd.ofFunctor (pairEnd X Y.unmop))
      (G := LinearEnd.ofFunctor (pairEnd X W.unmop))
    intro F
    apply ordinary_hom_ext (C := C) (M := M) (N := N)
    intro m
    change X ⊴ₗ (toFunctor F).map ((f.unmop ≫ g.unmop) ⊵ₗ m) = _
    simp only [comp_actionHomLeft, Functor.map_comp, actionHomRight_comp]
    rfl

/-- Actual separately linear post/precomposition before the Deligne lift. -/
def pairFunctor : C ⥤ Cᴹᵒᵖ ⥤ LinearEnd.Cat (Ordinary C M N) where
  obj X := pairRight X
  map f := {
    app Y := pairMapLeft f Y.unmop
    naturality {Y Z} g := by
      ext F m
      exact action_exchange _ _ }
  map_id X := by
    ext Y F m
    change (𝟙 X) ⊵ₗ (toFunctor F).obj (Y.unmop ⊙ₗ m) = 𝟙 _
    simp
  map_comp f g := by
    ext Y F m
    exact comp_actionHomLeft _ _ _

end Paper18.Category.ModuleFunctor.DiagonalAction
