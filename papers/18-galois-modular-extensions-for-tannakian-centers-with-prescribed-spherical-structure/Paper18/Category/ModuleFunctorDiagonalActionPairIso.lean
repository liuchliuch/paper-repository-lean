import Paper18.Category.ModuleFunctorDiagonalActionPair

/-! # Actual unit and tensor comparisons for the post/precomposition action -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits MonoidalLeftAction MonoidalOpposite
open Paper18.Category.ModuleAlphaInduction
open scoped MonoidalLeftAction
universe v u vM uM vN uN
namespace Paper18.Category.ModuleFunctor.DiagonalAction
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  {M : Type uM} [Category.{vM} M] [Preadditive M] [Linear ℂ M]
  [MonoidalLeftAction C M]
  {N : Type uN} [Category.{vN} N] [Preadditive N] [Linear ℂ N]
  [MonoidalLeftAction C N]
  [∀ X : C, (actionLeft M X).Additive] [∀ X : C, (actionLeft M X).Linear ℂ]
  [∀ X : C, (actionLeft N X).Additive] [∀ X : C, (actionLeft N X).Linear ℂ]

/-- The inverse native action associator as an ordinary natural isomorphism. -/
def nativeTensorIso (D : Type*) [Category D] [MonoidalLeftAction C D] (X Y : C) :
    actionLeft D Y ⋙ actionLeft D X ≅ actionLeft D (X ⊗ Y) :=
  NatIso.ofComponents (fun d => (αₗ X Y d).symm)
    (fun f => actionAssoc_inv_naturality_right X Y f)

/-- The tensor comparison is derived solely from the two native actions. -/
def pairTensorComponent (X Y X' Y' : C) (F : Ordinary C M N) :
    pairObject X Y (pairObject X' Y' F) ≅ pairObject (X ⊗ X') (Y' ⊗ Y) F :=
  InducedCategory.isoMk (
    Functor.isoWhiskerRight
      (Functor.isoWhiskerRight (nativeTensorIso M Y' Y) (toFunctor F))
      (actionLeft N X' ⋙ actionLeft N X) ≪≫
    Functor.isoWhiskerLeft (actionLeft M (Y' ⊗ Y) ⋙ toFunctor F)
      (nativeTensorIso N X X'))

@[simp] lemma pairTensorComponent_hom_app (X Y X' Y' : C)
    (F : Ordinary C M N) (m : M) :
    (forget.map (pairTensorComponent X Y X' Y' F).hom).app m =
      X ⊴ₗ X' ⊴ₗ (toFunctor F).map (αₗ Y' Y m).inv ≫
        (αₗ X X' ((toFunctor F).obj ((Y' ⊗ Y) ⊙ₗ m))).inv := rfl

/-- The actual inverse unitors give the ordinary unit comparison. -/
def pairUnitComponent (F : Ordinary C M N) :
    F ≅ pairObject (𝟙_ C) (𝟙_ C) F :=
  InducedCategory.isoMk (
    Functor.isoWhiskerRight
      (Functor.isoWhiskerRight (actionUnitNatIso C M).symm (toFunctor F)) (𝟭 N) ≪≫
    Functor.isoWhiskerLeft (actionLeft M (𝟙_ C) ⋙ toFunctor F)
      (actionUnitNatIso C N).symm)

@[simp] lemma pairUnitComponent_hom_app (F : Ordinary C M N) (m : M) :
    (forget.map (pairUnitComponent F).hom).app m =
      (toFunctor F).map (λₗ[C] m).inv ≫
        (λₗ[C] ((toFunctor F).obj ((𝟙_ C) ⊙ₗ m))).inv := rfl

def pairTensorIso (X Y X' Y' : C) :
    pairEnd (M := M) (N := N) X' Y' ⋙ pairEnd X Y ≅
      pairEnd (X ⊗ X') (Y' ⊗ Y) :=
  NatIso.ofComponents (pairTensorComponent X Y X' Y') (by
    intro F G τ
    apply ordinary_hom_ext (F := pairObject X Y (pairObject X' Y' F))
      (G := pairObject (X ⊗ X') (Y' ⊗ Y) G)
    intro m
    change (X ⊴ₗ X' ⊴ₗ τ.app (Y' ⊙ₗ Y ⊙ₗ m)) ≫
        (X ⊴ₗ X' ⊴ₗ (toFunctor G).map (αₗ Y' Y m).inv ≫
          (αₗ X X' ((toFunctor G).obj ((Y' ⊗ Y) ⊙ₗ m))).inv) =
      (X ⊴ₗ X' ⊴ₗ (toFunctor F).map (αₗ Y' Y m).inv ≫
        (αₗ X X' ((toFunctor F).obj ((Y' ⊗ Y) ⊙ₗ m))).inv) ≫
          (X ⊗ X') ⊴ₗ τ.app ((Y' ⊗ Y) ⊙ₗ m)
    rw [← assoc, ← actionHomRight_comp, ← actionHomRight_comp]
    rw [((show toFunctor F ⟶ toFunctor G from τ).naturality (αₗ Y' Y m).inv).symm]
    rw [actionHomRight_comp, actionHomRight_comp]
    simp only [assoc]
    rw [actionAssoc_inv_naturality_right])

def pairUnitIso : 𝟭 (Ordinary C M N) ≅ pairEnd (𝟙_ C) (𝟙_ C) :=
  NatIso.ofComponents pairUnitComponent (by
    intro F G τ
    apply ordinary_hom_ext (F := F) (G := pairObject (𝟙_ C) (𝟙_ C) G)
    intro m
    change τ.app m ≫ ((toFunctor G).map (λₗ[C] m).inv ≫
      (λₗ[C] ((toFunctor G).obj ((𝟙_ C) ⊙ₗ m))).inv) =
      ((toFunctor F).map (λₗ[C] m).inv ≫
        (λₗ[C] ((toFunctor F).obj ((𝟙_ C) ⊙ₗ m))).inv) ≫
          (𝟙_ C) ⊴ₗ τ.app ((𝟙_ C) ⊙ₗ m)
    rw [← assoc, ((show toFunctor F ⟶ toFunctor G from τ).naturality (λₗ[C] m).inv).symm]
    simp only [assoc]
    rw [actionUnitIso_inv_naturality]
    rfl)

end Paper18.Category.ModuleFunctor.DiagonalAction
