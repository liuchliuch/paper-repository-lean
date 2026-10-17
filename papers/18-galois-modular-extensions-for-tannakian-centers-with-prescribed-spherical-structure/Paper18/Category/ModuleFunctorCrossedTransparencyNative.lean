import Paper18.Category.ModuleFunctorCrossedTransparencyTannakian
import Paper18.Category.FixedBoundaryTensoratorNativeModule

/-! # The constructed native odd comparison has its actual module law

The module law is the genuine morphism property in the actual bundled
module-endofunctor category. Forgetting the bundle preserves precisely
that law for the subsequent scalar tensorator correction.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped MonObj Obj MonoidalLeftAction
universe v u w v' u' w'
namespace Paper18.Category.FixedBoundary
variable {A : Type u} [Category.{v} A] [Preadditive A] [Linear ℂ A]
  [MonoidalCategory A] [BraidedCategory A] [MonoidalPreadditive A] [MonoidalLinear ℂ A]
  [HasKernels A] [HasFiniteBiproducts A] [RightRigidCategory A] [HasCoequalizers A]
  [∀ X Y : A, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type w} [Fintype ι] (SA : FiniteSemisimpleSkeleton A ι)
  (TC : TannakianCenter A RepresentationZ2.H)
  {N : Type u'} [Category.{v'} N] [Preadditive N] [Linear ℂ N]
  [MonoidalCategory N] [BraidedCategory N] [MonoidalPreadditive N] [MonoidalLinear ℂ N]
  [RightRigidCategory N] [HasCoequalizers N] [HasKernels N] [HasFiniteBiproducts N]
  (i : A ⥤ N) [i.Braided] [i.Full] [i.Faithful] [i.Additive] [i.Linear ℂ]
  (P : BoundaryAutoequivalence i)
local instance nativeImageTannakianMonObj : MonObj (i.obj TC.regularAlgebra) := Functor.monObjObj (F := i) TC.regularAlgebra
local instance nativeImageTannakianCommMonObj : IsCommMonObj (i.obj TC.regularAlgebra) := Functor.isCommMonObj_obj
variable (B : TensorInverse (i.obj (TC.c2Generator)))
  (himage : ∀ X : A, Centralizes (i.obj (TC.c2Generator)) (i.obj X))
  (hfull : ∀ Y : N, Centralizes (i.obj (TC.c2Generator)) Y →
    ∃ X : A, Nonempty (i.obj X ≅ Y))
  (e : P.functor.obj (i.obj (TC.c2Generator)) ≅
    i.obj (TC.c2Generator))

local notation "s" => TC.regularAlgebraSeparable
local notation "hR" => TC.regularAlgebra_transparent
local notation "chi" => neutralModuleCharacter i TC.regularAlgebra B himage
local notation "Pos" => SignKernel.Positive chi
local notation "Odd" => HomogeneousCategory chi 1
local notation "G" => oddBoundaryModuleEnd SA i P TC.regularAlgebra B himage s hfull e

/-- The actual odd comparison obtained from a genuine native isomorphism
has the actual native module law used by monoidal scalar correction. -/
theorem tannakianOddComparison_native
    (b : G ≅ 𝟙_ (ModuleAlphaInduction.End Pos Odd)) :
    NativeOddComparisonNatural SA i P TC.regularAlgebra B himage s hfull e
      (tannakianOddComparison SA TC i P B himage hfull e b) := by
  dsimp only [NativeOddComparisonNatural]
  change ModuleFunctor.IsModuleNatural Pos b.hom.val
  exact b.hom.property

end Paper18.Category.FixedBoundary
