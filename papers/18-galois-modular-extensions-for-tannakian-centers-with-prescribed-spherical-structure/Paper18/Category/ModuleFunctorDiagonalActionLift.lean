import Paper18.Category.ModuleFunctorDiagonalActionPairLinear
import Paper18.Category.LinearMatLiftFullyFaithful
import Paper18.Category.DeligneProductEmbeddingBasic

/-! # The actual additive Deligne action functor at a module functor -/
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

def pairAt (F : Ordinary C M N) : C ⥤ C ⥤ Ordinary C M N where
  obj X := {
    obj Y := pairObject X Y F
    map f := (pairMapRight X f).app F
    map_id Y := by
      ext m
      change X ⊴ₗ (toFunctor F).map ((𝟙 Y) ⊵ₗ m) = 𝟙 _
      simp
    map_comp f g := by
      ext m
      change X ⊴ₗ (toFunctor F).map ((f ≫ g) ⊵ₗ m) = _
      simp only [comp_actionHomLeft, Functor.map_comp, actionHomRight_comp]
      rfl }
  map f := {
    app Y := (pairMapLeft f Y).app F
    naturality {Y Z} g := by ext m; exact action_exchange _ _ }
  map_id X := by ext Y m; exact id_actionHomLeft _ _
  map_comp f g := by ext Y m; exact comp_actionHomLeft _ _ _

instance pairAt_obj_additive (F : Ordinary C M N) (X : C) :
    ((pairAt F).obj X).Additive where
  map_add {Y Z} f g := by
    ext m
    change X ⊴ₗ (toFunctor F).map ((f + g) ⊵ₗ m) = _
    have h : (f + g) ⊵ₗ m = (f ⊵ₗ m) + (g ⊵ₗ m) := (actionRight C m).map_add
    rw [h, (toFunctor F).map_add]
    exact (actionLeft N X).map_add
instance pairAt_obj_linear (F : Ordinary C M N) (X : C) :
    ((pairAt F).obj X).Linear ℂ where
  map_smul f r := by
    ext m
    change X ⊴ₗ (toFunctor F).map ((r • f) ⊵ₗ m) = _
    have h : (r • f) ⊵ₗ m = r • (f ⊵ₗ m) := (actionRight C m).map_smul _ _
    rw [h, (toFunctor F).map_smul]
    exact (actionLeft N X).map_smul _ _
instance pairAt_additive (F : Ordinary C M N) : (pairAt F).Additive where
  map_add {X Z} f g := by ext Y m; exact (actionRight C ((toFunctor F).obj (Y ⊙ₗ m))).map_add
instance pairAt_linear (F : Ordinary C M N) : (pairAt F).Linear ℂ where
  map_smul f r := by ext Y m; exact (actionRight C ((toFunctor F).obj (Y ⊙ₗ m))).map_smul _ _

variable [HasFiniteBiproducts N]

def deligneAt (F : Ordinary C M N) : DeligneProduct C C ⥤ Ordinary C M N :=
  DeligneProduct.lift (pairAt F)
instance deligneAt_additive (F : Ordinary C M N) : (deligneAt F).Additive :=
  inferInstanceAs ((DeligneProduct.lift (pairAt F)).Additive)
instance deligneAt_linear (F : Ordinary C M N) : (deligneAt F).Linear ℂ :=
  inferInstanceAs ((DeligneProduct.lift (pairAt F)).Linear ℂ)

/-- The true external pair has the required post/precomposition value. -/
def deligneAtPairIso (F : Ordinary C M N) (X Y : C) :
    (deligneAt F).obj ((Mat_.embedding (LinearTensor C C)).obj ⟨X, Y⟩) ≅
      pairObject X Y F :=
  linearMatLiftSingletonIso (LinearTensor.lift (pairAt F)) ⟨X, Y⟩

end Paper18.Category.ModuleFunctor.DiagonalAction
