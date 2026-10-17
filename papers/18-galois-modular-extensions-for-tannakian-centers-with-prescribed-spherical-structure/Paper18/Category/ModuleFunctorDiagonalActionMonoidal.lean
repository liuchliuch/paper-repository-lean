import Paper18.Category.ModuleFunctorDiagonalActionPairMonoidal
import Paper18.Category.LinearTensorUncurryMonoidal
import Paper18.Category.LinearMatLiftFullyFaithful
import Paper18.Category.DeligneProductEmbeddingBasic
import Paper18.Category.MonoidalOppositeFusion

/-! # The genuine strong monoidal Deligne diagonal action functor

The second factor is first sent to the monoidal opposite by the actual
braided strong monoidal mop functor. Its positive tensor crossing is
retained in the actual tensorator.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits MonoidalLeftAction MonoidalOpposite
open scoped MonoidalLeftAction
universe v u vM uM vN uN
namespace Paper18.Category.ModuleFunctor.DiagonalAction
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  {M : Type uM} [Category.{vM} M] [Preadditive M] [Linear ℂ M] [MonoidalLeftAction C M]
  {N : Type uN} [Category.{vN} N] [Preadditive N] [Linear ℂ N] [MonoidalLeftAction C N]
  [∀ X : C, (actionLeft M X).Additive] [∀ X : C, (actionLeft M X).Linear ℂ]
  [∀ X : C, (actionLeft N X).Additive] [∀ X : C, (actionLeft N X).Linear ℂ]
  [∀ m : M, (actionRight C m).Additive] [∀ m : M, (actionRight C m).Linear ℂ]
  [∀ n : N, (actionRight C n).Additive] [∀ n : N, (actionRight C n).Linear ℂ]

/-- Both factors now have source C; the second tensor order is reversed
by the genuine strong braided mop functor. -/
def sameFunctor : C ⥤ C ⥤ (LinearEnd.Cat (Ordinary C M N))ᴹᵒᵖ :=
  (mopFunctor C ⋙ (pairMopFunctor (C := C) (M := M) (N := N)).flip).flip

instance sameFunctor_obj_additive (X : C) : ((sameFunctor (M := M) (N := N)).obj X).Additive := by
  change (mopFunctor C ⋙ (pairMopFunctor (M := M) (N := N)).obj X).Additive
  infer_instance
instance sameFunctor_obj_linear (X : C) : ((sameFunctor (M := M) (N := N)).obj X).Linear ℂ := by
  change (mopFunctor C ⋙ (pairMopFunctor (M := M) (N := N)).obj X).Linear ℂ
  infer_instance
instance sameFunctor_additive : (sameFunctor (C := C) (M := M) (N := N)).Additive where
  map_add {X Z} f g := by
    apply NatTrans.ext
    funext Y
    exact congrArg (fun t => t.app (mop Y)) ((pairMopFunctor (M := M) (N := N)).map_add (f := f) (g := g))
instance sameFunctor_linear : (sameFunctor (C := C) (M := M) (N := N)).Linear ℂ where
  map_smul f z := by
    apply NatTrans.ext
    funext Y
    exact congrArg (fun t => t.app (mop Y)) (Functor.Linear.map_smul (F := pairMopFunctor (M := M) (N := N)) f z)

instance sameBifunctorMonoidal :
    (Functor.uncurry.obj (sameFunctor (C := C) (M := M) (N := N))).Monoidal := by
  change (((𝟭 C).prod (mopFunctor C)) ⋙ (pairBifunctor (M := M) (N := N))).Monoidal
  infer_instance

/-- The genuine linear tensor lift retains the actual strong structure. -/
def linearActionEnd : LinearTensor C C ⥤ (LinearEnd.Cat (Ordinary C M N))ᴹᵒᵖ :=
  LinearTensor.lift sameFunctor
instance linearActionEndMonoidal : (linearActionEnd (C := C) (M := M) (N := N)).Monoidal :=
  inferInstanceAs ((LinearTensor.lift (sameFunctor (M := M) (N := N))).Monoidal)

variable [HasFiniteBiproducts N]

/-- The true additive Deligne lift, with actual strong monoidal data. -/
def deligneActionEnd : DeligneProduct C C ⥤ (LinearEnd.Cat (Ordinary C M N))ᴹᵒᵖ :=
  DeligneProduct.lift sameFunctor
instance deligneActionEndMonoidal : (deligneActionEnd (C := C) (M := M) (N := N)).Monoidal :=
  inferInstanceAs ((DeligneProduct.lift (sameFunctor (M := M) (N := N))).Monoidal)
instance deligneActionEndAdditive : (deligneActionEnd (C := C) (M := M) (N := N)).Additive :=
  inferInstanceAs ((DeligneProduct.lift (sameFunctor (M := M) (N := N))).Additive)
instance deligneActionEndLinear : (deligneActionEnd (C := C) (M := M) (N := N)).Linear ℂ :=
  inferInstanceAs ((DeligneProduct.lift (sameFunctor (M := M) (N := N))).Linear ℂ)

/-- Exact external-pair normalization of the actual Deligne endofunctor. -/
def deligneActionEndPairIso (X Y : C) :
    (deligneActionEnd (M := M) (N := N)).obj
      ((Mat_.embedding (LinearTensor C C)).obj ⟨X, Y⟩) ≅
        mop (LinearEnd.ofFunctor (pairEnd (M := M) (N := N) X Y)) :=
  linearMatLiftSingletonIso (LinearTensor.lift (sameFunctor (M := M) (N := N))) ⟨X, Y⟩

end Paper18.Category.ModuleFunctor.DiagonalAction
