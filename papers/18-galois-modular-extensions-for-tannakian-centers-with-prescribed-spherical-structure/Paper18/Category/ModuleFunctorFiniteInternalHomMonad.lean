import Paper18.Category.ModuleFunctorFiniteInternalHomBasic
import Paper18.Category.ModuleFunctorFiniteInternalHomMonoidal
import Mathlib.CategoryTheory.Monad.Adjunction
import Mathlib.CategoryTheory.Monad.EquivMon

/-! # The actual internal endomorphism algebra from the actual adjunction monad -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped MonoidalLeftAction
universe v u vM uM w
namespace Paper18.Category.ModuleInternalHom
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  {M : Type uM} [Category.{vM} M] [Preadditive M] [Linear ℂ M]
  [HasFiniteBiproducts M] [∀ X Y : M, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalLeftAction C M]
  [∀ X : C, (MonoidalLeftAction.actionLeft M X).Additive]
  [∀ X : C, (MonoidalLeftAction.actionLeft M X).Linear ℂ]
  [∀ n : M, (MonoidalLeftAction.actionRight C n).Additive]
  [∀ n : M, (MonoidalLeftAction.actionRight C n).Linear ℂ]

/-- The actual adjunction monad, with its derived native strong module structure. -/
def monadEnd (n : M) : ModuleAlphaInduction.End C C where
  toFunctor := MonoidalLeftAction.actionRight C n ⋙ (internalHomFunctor S n).toFunctor
  leftLinear := inferInstance
  additive := inferInstance
  linear := inferInstance

/-- The genuine module-natural monad unit. -/
def monadUnit (n : M) : 𝟙_ (ModuleAlphaInduction.End C C) ⟶ monadEnd S n :=
  ⟨(adjunction S n).unit,
    ModuleFunctor.semisimpleRightAdjunction_unit_moduleNatural S (ModuleFunctor.actionObject n)⟩

/-- The genuine module-natural monad multiplication. -/
def monadMul (n : M) : monadEnd S n ⊗ monadEnd S n ⟶ monadEnd S n := by
  let F := MonoidalLeftAction.actionRight C n
  let R := (internalHomFunctor S n).toFunctor
  letI : ModuleFunctor.IsModuleNatural C (adjunction S n).counit :=
    ModuleFunctor.semisimpleRightAdjunction_counit_moduleNatural S (ModuleFunctor.actionObject n)
  refine ⟨(adjunction S n).toMonad.μ, { lineator := ?_ }⟩
  intro X Y
  change ((Functor.LaxLeftLinear.μₗ R X (F.obj (R.obj (F.obj Y))) ≫
      R.map (Functor.LaxLeftLinear.μₗ F X (R.obj (F.obj Y)))) ≫
      R.map (F.map (Functor.LaxLeftLinear.μₗ R X (F.obj Y) ≫
        R.map (Functor.LaxLeftLinear.μₗ F X Y)))) ≫
      R.map ((adjunction S n).counit.app (F.obj (X ⊗ Y))) =
    X ⊴ₗ R.map ((adjunction S n).counit.app (F.obj Y)) ≫
      Functor.LaxLeftLinear.μₗ R X (F.obj Y) ≫ R.map (Functor.LaxLeftLinear.μₗ F X Y)
  erw [Functor.LaxLeftLinear.μₗ_naturality_right_assoc R X
    ((adjunction S n).counit.app (F.obj Y))]
  simp only [Category.assoc, F.map_comp, ← R.map_comp]
  erw [(adjunction S n).counit.naturality]
  simp only [← Category.assoc]
  have hc := ModuleFunctor.IsModuleNatural.lineator (C := C) (τ := (adjunction S n).counit) X (F.obj Y)
  change (Functor.LaxLeftLinear.μₗ F X (R.obj (F.obj Y)) ≫
      F.map (Functor.LaxLeftLinear.μₗ R X (F.obj Y))) ≫
      (adjunction S n).counit.app (X ⊙ₗ F.obj Y) =
    (X ⊴ₗ (adjunction S n).counit.app (F.obj Y)) ≫ 𝟙 _ at hc
  simpa only [Category.assoc, Category.comp_id, Functor.id_map, Functor.comp_obj] using congrArg
    (fun z => Functor.LaxLeftLinear.μₗ R X (F.obj (R.obj (F.obj Y))) ≫
      R.map (z ≫ Functor.LaxLeftLinear.μₗ F X Y)) hc

/-- The actual adjunction monad is an actual internal monoid in strong
module endofunctors; its algebra laws are the actual monad laws. -/
instance monadEndMonObj (n : M) : MonObj (monadEnd S n) where
  one := monadUnit S n
  mul := monadMul S n
  one_mul := by
    apply ModuleFunctor.bundled_hom_ext
    ext X
    change (adjunction S n).toMonad.map ((adjunction S n).toMonad.η.app X) ≫
      (adjunction S n).toMonad.μ.app X = 𝟙 _
    exact (adjunction S n).toMonad.right_unit X
  mul_one := by
    apply ModuleFunctor.bundled_hom_ext
    ext X
    change (adjunction S n).toMonad.η.app ((adjunction S n).toMonad.obj X) ≫
      (adjunction S n).toMonad.μ.app X = 𝟙 _
    exact (adjunction S n).toMonad.left_unit X
  mul_assoc := by
    apply ModuleFunctor.bundled_hom_ext
    ext X
    change (adjunction S n).toMonad.map ((adjunction S n).toMonad.μ.app X) ≫
      (adjunction S n).toMonad.μ.app X = 𝟙 _ ≫
        (adjunction S n).toMonad.μ.app ((adjunction S n).toMonad.obj X) ≫
          (adjunction S n).toMonad.μ.app X
    simpa only [Category.id_comp] using (adjunction S n).toMonad.assoc X

/-- The actual internal algebra on the monad's value at the actual unit,
with all algebra laws derived from the genuine adjunction monad. -/
def endMonoidAtUnit (n : M) : MonObj ((monadEnd S n).toFunctor.obj (𝟙_ C)) :=
  Functor.monObjObj (F := ModuleFunctor.evaluationUnit (C := C) (M := C)) (monadEnd S n)

/-- The actual action unitor identifies the monad's unit value with the
specified actual internal endomorphism object. -/
def endUnitIso (n : M) : (monadEnd S n).toFunctor.obj (𝟙_ C) ≅ endObject S n :=
  (internalHomFunctor S n).toFunctor.mapIso (λₗ[C] n)

/-- The actual internal endomorphism algebra. No multiplication or
algebra law is a field: it is transported from the constructed monad. -/
def endMonoid (n : M) : MonObj (endObject S n) := by
  letI := endMonoidAtUnit S n
  exact MonObj.ofIso (endUnitIso S n)

end Paper18.Category.ModuleInternalHom
