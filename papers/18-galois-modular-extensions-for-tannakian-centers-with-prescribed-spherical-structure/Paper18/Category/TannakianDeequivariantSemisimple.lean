import Paper18.Category.TannakianDeequivariantization
import Paper18.Category.SeparableModulesSemisimple

/-!
# Actual finite semisimplicity of Tannakian de-equivariant modules

The explicit separable regular algebra and the proved averaging construction
produce all additive finiteness data and a genuine finite simple skeleton.
No module semisimplicity assertion is supplied as a hypothesis.
-/
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
universe v u w
namespace Paper18.Category
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalCategory C] [BraidedCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  {G : Type} [Group G] [Fintype G] (T : TannakianCenter C G)

/-- The actual finite set of simple modules over the Tannakian regular
algebra, obtained from free modules on actual ambient simples. -/
abbrev TannakianCenter.DeequivariantSimpleIndex := T.regularAlgebraSeparable.SimpleIndex S

/-- The actual finite semisimple skeleton of Tannakian de-equivariant
modules, constructed by separable averaging. -/
def TannakianCenter.deequivariantSkeleton :
    FiniteSemisimpleSkeleton T.Deequivariantization (T.DeequivariantSimpleIndex S) :=
  T.regularAlgebraSeparable.skeleton S

/-- The actual additive complex-linear free-module functor underlying
Tannakian de-equivariantization. -/
def TannakianCenter.deequivariantFree : C ⥤ T.Deequivariantization :=
  InternalModule.freeFunctor

instance TannakianCenter.deequivariantFreeAdditive : T.deequivariantFree.Additive := by
  dsimp [TannakianCenter.deequivariantFree]
  infer_instance

instance TannakianCenter.deequivariantFreeLinear : T.deequivariantFree.Linear ℂ := by
  dsimp [TannakianCenter.deequivariantFree]
  infer_instance

omit [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalPreadditive C] [MonoidalLinear ℂ C] in
/-- Every actual de-equivariant module is a retract of a free module, via
the explicit separable section of its action. -/
theorem TannakianCenter.deequivariantFree_retract_dominant
    (M : T.Deequivariantization) :
    ∃ X : C, Nonempty (Retract M (T.deequivariantFree.obj X)) :=
  T.regularAlgebraSeparable.free_retract_dominant M

end Paper18.Category
