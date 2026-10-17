import Paper18.Category.ModuleFunctorFiniteInternalHomMonad
import Mathlib.CategoryTheory.Monad.Algebra

/-! # Actual internal-Hom monad and the genuine right-tensor algebra monad -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped MonoidalLeftAction MonObj Obj
attribute [local instance] endofunctorMonoidalCategory
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

/-- The actual ordinary monoid obtained by forgetting the genuine
strong-module structure of the actual adjunction monad. -/
def ordinaryMonadMonoid (n : M) : Mon (C ⥤ C) :=
  (ModuleFunctor.forget (C := C) (M := C) (N := C)).mapMon.obj ⟨monadEnd S n⟩

/-- Forgetting the actual module structure retains exactly the genuine
adjunction monad up to the actual identity-component monad isomorphism. -/
def ordinaryMonadIso (n : M) :
    (adjunction S n).toMonad ≅ Monad.ofMon (ordinaryMonadMonoid S n) :=
  MonadIso.mk (Iso.refl _)
    (fun X => by
      change (adjunction S n).unit.app X ≫ 𝟙 _ = 𝟙 _ ≫ (adjunction S n).unit.app X
      simp)
    (fun X => by
      change (adjunction S n).toMonad.μ.app X ≫ 𝟙 _ =
        ((adjunction S n).toMonad.map (𝟙 _) ≫ 𝟙 _) ≫
          (𝟙 _ ≫ (adjunction S n).toMonad.μ.app X)
      simp)

/-- Actual regular-module monoidal Eilenberg--Watts, including genuine
unit and counit monoidality. -/
def regularMonoidalEquivalence : C ≌ ModuleAlphaInduction.End C C :=
  (ModuleFunctor.regularEquivalence (C := C) (M := C)).symm

instance regularMonoidalEquivalence_functor :
    (regularMonoidalEquivalence (C := C)).functor.Monoidal := regularActionMonoidal

instance regularMonoidalEquivalence_inverse :
    (regularMonoidalEquivalence (C := C)).inverse.Monoidal := regularEvaluationMonoidal

instance regularMonoidalEquivalence_coherence :
    (regularMonoidalEquivalence (C := C)).IsMonoidal := by
  let e := regularMonoidalEquivalence (C := C)
  letI : e.inverse.Monoidal := e.inverseMonoidal
  infer_instance

/-- The actual right-tensor monad on the actual internal algebra at the
unit, obtained by mapping the algebra through genuine right tensoring. -/
def tensorMonadAtUnit (n : M) : Monad C := by
  letI := endMonoidAtUnit S n
  exact Monad.ofMon ((ModuleFunctor.forget (C := C) (M := C) (N := C)).mapMon.obj
    ((ModuleFunctor.actionFunctor (C := C) (M := C)).mapMon.obj
      ⟨(monadEnd S n).toFunctor.obj (𝟙_ C)⟩))

/-- Actual monoidal Eilenberg--Watts identifies the genuine adjunction
monad with right tensoring by its actual internal algebra. -/
def monadTensorIsoAtUnit (n : M) : (adjunction S n).toMonad ≅ tensorMonadAtUnit S n := by
  let E := regularMonoidalEquivalence (C := C)
  let j := (E.mapMon).counitIso.app (⟨monadEnd S n⟩ : Mon (ModuleAlphaInduction.End C C))
  let k := (ModuleFunctor.forget (C := C) (M := C) (N := C)).mapMon.mapIso j
  exact ordinaryMonadIso S n ≪≫ (Monad.monadMonEquiv C).inverse.mapIso k.symm

/-- The actual right-tensor monad of the specified internal algebra R_n(n). -/
def tensorMonad (n : M) : Monad C := by
  letI := endMonoid S n
  exact Monad.ofMon ((ModuleFunctor.forget (C := C) (M := C) (N := C)).mapMon.obj
    ((ModuleFunctor.actionFunctor (C := C) (M := C)).mapMon.obj ⟨endObject S n⟩))

/-- Transport from the monad's unit value to the actual internal-end
object is an actual algebra isomorphism and hence an actual monad isomorphism. -/
def tensorMonadTransportIso (n : M) : tensorMonadAtUnit S n ≅ tensorMonad S n := by
  letI := endMonoidAtUnit S n
  letI := endMonoid S n
  letI : IsMonHom (endUnitIso S n).hom := isMonHom_ofIso (endUnitIso S n)
  let q := Mon.mkIso' (endUnitIso S n)
  let j := (ModuleFunctor.forget (C := C) (M := C) (N := C)).mapMon.mapIso
    ((ModuleFunctor.actionFunctor (C := C) (M := C)).mapMon.mapIso q)
  exact (Monad.monadMonEquiv C).inverse.mapIso j

/-- The genuine adjunction monad is genuinely isomorphic to right
tensoring by the constructed actual internal endomorphism algebra. -/
def monadTensorIso (n : M) : (adjunction S n).toMonad ≅ tensorMonad S n :=
  monadTensorIsoAtUnit S n ≪≫ tensorMonadTransportIso S n

@[simp] theorem tensorMonad_obj (n : M) (X : C) :
    (tensorMonad S n).obj X = X ⊗ endObject S n := rfl

end Paper18.Category.ModuleInternalHom
