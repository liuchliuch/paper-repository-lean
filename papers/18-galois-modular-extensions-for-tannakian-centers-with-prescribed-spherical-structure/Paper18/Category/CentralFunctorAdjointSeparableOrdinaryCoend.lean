import Paper18.Category.CentralFunctorAdjointSeparableOrdinaryCap
import Paper18.Category.DrinfeldCoendModulesDesc
import Paper18.Category.ModuleFunctorFinite

/-! # Actual preservation of diagonal cap coends in the ordinary category

Finite simple evaluation gives finite ordinary Hom spaces. The actual
semisimple right adjoint therefore proves coend preservation for every
actual additive linear functor from the Deligne category. No semisimplicity
of the ordinary module-functor category is assumed.
-/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped MonoidalLeftAction
universe v u vM uM vN uN w wM
namespace Paper18.Category.CentralFunctorAdjointSeparable
open MonoidalLeftAction ModuleFunctor.DiagonalAction
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [RightRigidCategory C] [Preadditive C] [Linear ℂ C]
  [MonoidalPreadditive C] [MonoidalLinear ℂ C] [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ C)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  {M : Type uM} [Category.{vM} M] [Preadditive M] [Linear ℂ M]
  [HasFiniteBiproducts M] [MonoidalLeftAction C M]
  {κ : Type wM} [Fintype κ] (T : FiniteSemisimpleSkeleton M κ)
  {N : Type uN} [Category.{vN} N] [Preadditive N] [Linear ℂ N]
  [HasFiniteBiproducts N] [MonoidalLeftAction C N]
  [∀ X Y : N, FiniteDimensional ℂ (X ⟶ Y)]
  [∀ X : C, (actionLeft N X).Additive] [∀ X : C, (actionLeft N X).Linear ℂ]

include T
omit [MonoidalCategory C] [BraidedCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C] [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  [Simple (𝟙_ C)] in
/-- Ordinary transformations between actual additive module functors have
finite-dimensional actual Hom spaces. -/
def ordinaryFiniteDimensionalHom (F G : Ordinary C M N) :
    FiniteDimensional ℂ (F ⟶ G) :=
  ModuleFunctor.finiteDimensionalNatTrans T (toFunctor F) (toFunctor G)

/-- Actual right-adjoint existence proves preservation of the full cap
coend, even though its raw diagram has arbitrarily many object labels. -/
def ordinaryFunctor_preservesCapCoend
    (G : DeligneProduct C C ⥤ Ordinary C M N) [G.Additive] [G.Linear ℂ] :
    PreservesColimit
      (multispanIndexCoend (DrinfeldCoendModules.capDiagram (D := C))).multispan G := by
  letI := DeligneProduct.hasKernels S S
  letI (F H : Ordinary C M N) := ordinaryFiniteDimensionalHom T F H
  letI := (DiagonalAlgebra.semisimpleRightAdjunction (DeligneProduct.skeleton S S) G).isLeftAdjoint
  infer_instance

omit [∀ X : C, (actionLeft N X).Linear ℂ] in
/-- The two actual cap-generator families determine ordinary maps from
the tensor square of the actual diagonal algebra after an actual additive
linear functor. The two coend-preservation claims are derived internally. -/
theorem ordinaryFunctor_capTensor_hom_ext
    (G : DeligneProduct C C ⥤ Ordinary C M N) [G.Additive] [G.Linear ℂ]
    {W : Ordinary C M N}
    {f g : G.obj (DiagonalAlgebra.canonicalAlgebra S ⊗
        DiagonalAlgebra.canonicalAlgebra S) ⟶ W}
    (h : ∀ X Y : C,
      G.map (DiagonalAlgebra.capGenerator S X ⊗ₘ DiagonalAlgebra.capGenerator S Y) ≫ f =
        G.map (DiagonalAlgebra.capGenerator S X ⊗ₘ DiagonalAlgebra.capGenerator S Y) ≫ g) :
    f = g := by
  let L := DiagonalAlgebra.canonicalAlgebra S
  let G₁ := tensorRight L ⋙ G
  letI := ordinaryFunctor_preservesCapCoend S T G₁
  apply DrinfeldCoendModules.capGenerator_hom_ext S G₁
  intro X
  let Q := DeligneProduct.externalObject (dual C X) X
  let G₂ := tensorLeft Q ⋙ G
  letI := ordinaryFunctor_preservesCapCoend S T G₂
  apply DrinfeldCoendModules.capGenerator_hom_ext S G₂
  intro Y
  change G.map (Q ◁ DiagonalAlgebra.capGenerator S Y) ≫
      (G.map (DiagonalAlgebra.capGenerator S X ▷ L) ≫ f) =
    G.map (Q ◁ DiagonalAlgebra.capGenerator S Y) ≫
      (G.map (DiagonalAlgebra.capGenerator S X ▷ L) ≫ g)
  rw [← G.map_comp_assoc, ← G.map_comp_assoc, ← tensorHom_def']
  exact h X Y

end Paper18.Category.CentralFunctorAdjointSeparable
