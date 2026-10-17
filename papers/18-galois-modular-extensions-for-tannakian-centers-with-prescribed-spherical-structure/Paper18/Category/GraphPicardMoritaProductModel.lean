import Paper18.Category.GraphPicardMoritaProductOpposite

/-! # An actual category model for the braided product of algebra modules

The second actual left-module category is converted to right modules over
the actual braided opposite algebra. The category model is then the
genuine category of two-sided modules representing the balanced product.
Its finite semisimplicity is derived by two actual separable splittings.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits MonoidalOpposite
open scoped MonObj
universe v u w vE uE
namespace Paper18.Category.GraphPicard.MoritaProduct
attribute [local instance] InternalModule.ambientMonoidalOppositeLeftAction
variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]

/-- The original left module category, with its original algebra structure
fixed before installing the opposite algebra on the same carrier. -/
abbrev LeftModules (A : Mon D) := Mod_ D A.X

/-- The actual two-sided-module model. The right algebra is the actual
braided opposite, and is not assumed to equal the original algebra. -/
abbrev Model (A B : Mon D) :=
  letI := (oppositeAlgebra B).mon
  BimoduleRelativeTensor.Native A.X (oppositeAlgebra B).X

/-- The actual external pair of two original left modules. -/
def external (A B : Mon D) : LeftModules A × LeftModules B ⥤ Model A B := by
  letI := (oppositeAlgebra B).mon
  exact (𝟭 (LeftModules A)).prod (leftToRight B) ⋙ BalancedModuleCategory.external

@[simp] theorem external_obj_X (A B : Mon D) (M : LeftModules A) (N : LeftModules B) :
    ((external A B).obj (M,N)).X.X = M.X ⊗ N.X := rfl

@[simp] theorem external_map (A B : Mon D) {M M' : LeftModules A} {N N' : LeftModules B}
    (f : M ⟶ M') (g : N ⟶ N') :
    ((external A B).map (CategoryTheory.Prod.mkHom f g)).hom.hom = f.hom ⊗ₘ g.hom := rfl

/-- Coherent balanced functors on the original first module category and
the actual right-module presentation of the second. -/
abbrev Balanced (A B : Mon D) (E : Type uE) [Category.{vE} E] :=
  letI := (oppositeAlgebra B).mon
  BalancedModuleCategory.BalancedFunctor (A := A.X) (B := (oppositeAlgebra B).X) E

namespace Balanced
variable {A B : Mon D} {E : Type uE} [Category.{vE} E]

/-- The actual bifunctor on the two original left-module categories. -/
def onLeftModules (F : Balanced A B E) : LeftModules A × LeftModules B ⥤ E :=
  (𝟭 (LeftModules A)).prod (leftToRight B) ⋙ F.toFunctor

end Balanced

variable [Preadditive D] [Linear ℂ D] [MonoidalPreadditive D] [MonoidalLinear ℂ D]

attribute [local instance] InternalModule.ambientMonoidalOppositeLeftAction

variable (A B : Mon D) (SA : SeparableAlgebra A.X) (SB : SeparableAlgebra B.X)

/-- The actual universal equivalence of functor categories comes from
the constructed balanced-product universal property. -/
def balancedEquivalence {E : Type uE} [Category.{vE} E] [HasCoequalizers E] :
    (Model A B ⥤ E) ≌ Balanced A B E := by
  letI := (oppositeAlgebra B).mon
  exact BalancedModuleCategory.balancedEquivalence SA (oppositeSeparable B SB)

namespace Balanced
variable {A B} {E : Type uE} [Category.{vE} E] [HasCoequalizers E]
  (F : Balanced A B E)

/-- An actual coequalizer construction extends every coherent balanced
bifunctor to the actual two-sided-module category. -/
def extension : Model A B ⥤ E :=
  BalancedModuleCategory.BalancedFunctor.extension F

/-- The extension agrees with the given bifunctor on the two original
left-module categories, through an actual natural isomorphism. -/
def externalExtensionIso : external A B ⋙ extension F ≅ onLeftModules F := by
  letI := (oppositeAlgebra B).mon
  exact Functor.isoWhiskerLeft ((𝟭 (LeftModules A)).prod (leftToRight B))
    (F.extensionExternalNatIso (oppositeSeparable B SB))

end Balanced

variable [HasKernels D] [HasFiniteBiproducts D]
  [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton D ι)

/-- The derived finite label set of actual simple two-sided modules. -/
def ModelSimpleIndex :=
  letI := (oppositeAlgebra B).mon
  ModuleFunctor.SeparableAction.SimpleIndex
    (ModuleFunctor.separableMop (oppositeSeparable B SB)) (SA.skeleton S)

instance modelSimpleIndex_fintype : Fintype (ModelSimpleIndex A B SA SB S) := by
  unfold ModelSimpleIndex
  infer_instance

/-- Actual finite semisimplicity of the balanced-product category model,
derived from the two actual separable algebra sections. -/
def modelSkeleton : FiniteSemisimpleSkeleton (Model A B) (ModelSimpleIndex A B SA SB S) := by
  letI := (oppositeAlgebra B).mon
  exact ModuleFunctor.SeparableAction.skeleton
    (ModuleFunctor.separableMop (oppositeSeparable B SB)) (SA.skeleton S)

/-- The actual kernels of the actual two-sided-module category are
inherited twice from the actual ambient kernel construction. -/
def modelHasKernels : HasKernels (Model A B) := by
  letI := (oppositeAlgebra B).mon
  infer_instance

end Paper18.Category.GraphPicard.MoritaProduct
