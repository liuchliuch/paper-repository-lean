import Paper18.Category.ModuleFunctorDiagonalActionPairIso
import Mathlib.CategoryTheory.Functor.Currying

/-! # Separate complex linearity of the actual pair action -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits MonoidalLeftAction MonoidalOpposite
open scoped MonoidalLeftAction
universe v u vM uM vN uN
namespace Paper18.Category.ModuleFunctor.DiagonalAction
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [Preadditive C] [Linear ℂ C]
  {M : Type uM} [Category.{vM} M] [Preadditive M] [Linear ℂ M]
  [MonoidalLeftAction C M]
  {N : Type uN} [Category.{vN} N] [Preadditive N] [Linear ℂ N]
  [MonoidalLeftAction C N]
  [∀ X : C, (actionLeft M X).Additive] [∀ X : C, (actionLeft M X).Linear ℂ]
  [∀ X : C, (actionLeft N X).Additive] [∀ X : C, (actionLeft N X).Linear ℂ]
  [∀ m : M, (actionRight C m).Additive] [∀ m : M, (actionRight C m).Linear ℂ]
  [∀ n : N, (actionRight C n).Additive] [∀ n : N, (actionRight C n).Linear ℂ]

instance pairRight_additive (X : C) : (pairRight (M := M) (N := N) X).Additive where
  map_add {Y Z} f g := by
    ext F m
    change X ⊴ₗ (toFunctor F).map ((f.unmop + g.unmop) ⊵ₗ m) =
      X ⊴ₗ (toFunctor F).map (f.unmop ⊵ₗ m) + X ⊴ₗ (toFunctor F).map (g.unmop ⊵ₗ m)
    have h : (f.unmop + g.unmop) ⊵ₗ m = (f.unmop ⊵ₗ m) + (g.unmop ⊵ₗ m) :=
      (actionRight C m).map_add
    rw [h, (toFunctor F).map_add]
    exact (actionLeft N X).map_add

instance pairRight_linear (X : C) : (pairRight (M := M) (N := N) X).Linear ℂ where
  map_smul f r := by
    ext F m
    change X ⊴ₗ (toFunctor F).map ((r • f.unmop) ⊵ₗ m) =
      r • (X ⊴ₗ (toFunctor F).map (f.unmop ⊵ₗ m))
    have h : (r • f.unmop) ⊵ₗ m = r • (f.unmop ⊵ₗ m) :=
      (actionRight C m).map_smul _ _
    rw [h, (toFunctor F).map_smul]
    exact (actionLeft N X).map_smul _ _

instance pairFunctor_additive : (pairFunctor (C := C) (M := M) (N := N)).Additive where
  map_add {X Z} f g := by
    ext Y F m
    exact (actionRight C ((toFunctor F).obj (Y.unmop ⊙ₗ m))).map_add

instance pairFunctor_linear : (pairFunctor (C := C) (M := M) (N := N)).Linear ℂ where
  map_smul f r := by
    ext Y F m
    exact (actionRight C ((toFunctor F).obj (Y.unmop ⊙ₗ m))).map_smul _ _

/-- Mopping gives the conventional covariant order of a left action. -/
def pairMopFunctor : C ⥤ Cᴹᵒᵖ ⥤ (LinearEnd.Cat (Ordinary C M N))ᴹᵒᵖ :=
  pairFunctor ⋙ (Functor.whiskeringRight Cᴹᵒᵖ
    (LinearEnd.Cat (Ordinary C M N)) (LinearEnd.Cat (Ordinary C M N))ᴹᵒᵖ).obj
      (mopFunctor _)

instance pairMopFunctor_additive :
    (pairMopFunctor (C := C) (M := M) (N := N)).Additive where
  map_add {X Z} f g := by
    apply NatTrans.ext
    funext Y
    apply Quiver.Hom.unmop_inj
    ext F m
    exact (actionRight C ((toFunctor F).obj (Y.unmop ⊙ₗ m))).map_add
instance pairMopFunctor_linear :
    (pairMopFunctor (C := C) (M := M) (N := N)).Linear ℂ where
  map_smul f r := by
    apply NatTrans.ext
    funext Y
    apply Quiver.Hom.unmop_inj
    ext F m
    exact (actionRight C ((toFunctor F).obj (Y.unmop ⊙ₗ m))).map_smul _ _
instance pairMopFunctor_obj_additive (X : C) :
    ((pairMopFunctor (M := M) (N := N)).obj X).Additive := by
  change (pairRight X ⋙ mopFunctor _).Additive
  infer_instance
instance pairMopFunctor_obj_linear (X : C) :
    ((pairMopFunctor (M := M) (N := N)).obj X).Linear ℂ := by
  change (pairRight X ⋙ mopFunctor _).Linear ℂ
  infer_instance

def pairBifunctor : C × Cᴹᵒᵖ ⥤ (LinearEnd.Cat (Ordinary C M N))ᴹᵒᵖ :=
  Functor.uncurry.obj pairMopFunctor

end Paper18.Category.ModuleFunctor.DiagonalAction
