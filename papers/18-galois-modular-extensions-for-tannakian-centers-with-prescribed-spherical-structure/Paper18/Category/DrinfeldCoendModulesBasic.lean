import Paper18.Category.GraphLagrangianNoPivotal
import Paper18.Category.DiagonalAlgebraCapGeneratorDinatural
import Paper18.Category.SeparableModulesSemisimple

/-! # The actual internal coend algebra obtained from the diagonal

The multiplication here is the actual transported canonical multiplication.
Its separability is derived without a pivotal structure. The cap generators
are fixed by their actual adjunction evaluations, so later comparisons must
respect their normalization.
-/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped MonObj
universe v u w
namespace Paper18.Category.DrinfeldCoendModules
attribute [local instance 2000] RightRigidCategory.rightDual
open DiagonalAlgebra
variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
  [RightRigidCategory D] [Preadditive D] [Linear ℂ D]
  [MonoidalPreadditive D] [MonoidalLinear ℂ D] [HasKernels D] [HasFiniteBiproducts D]
  [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ D)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton D ι)

/-- The actual internal algebra is the strong-monoidal tensor-product
image of the actual canonical diagonal algebra. -/
def algebra : D := (tensorProductFunctor (C := D)).obj (canonicalAlgebra S)

instance algebraMonObj : MonObj (algebra S) :=
  Functor.monObjObj (F := tensorProductFunctor (C := D)) (canonicalAlgebra S)

/-- An actual bimodule splitting of the transported multiplication,
constructed without a pivotal or spherical input. -/
def separable : SeparableAlgebra (algebra S) :=
  (canonicalSeparableNoPivotal S).map (tensorProductFunctor (C := D))

/-- The fixed actual rigid cap generator of the internal algebra. -/
def injection (X : D) : dual D X ⊗ X ⟶ algebra S :=
  (capPairIso (dual D X) X).inv ≫
    (tensorProductFunctor (C := D)).map (capGenerator S X)

/-- The internal generators retain the chosen actual rigid cap under the
canonical tensor-product counit. -/
lemma injection_counit (X : D) :
    injection S X ≫ canonicalAlgebraCounit S = ε_ X (dual D X) := by
  dsimp only [injection]
  rw [assoc, capGenerator_counit, Iso.inv_hom_id_assoc]

/-- The actual internal cap family is dinatural. -/
lemma injection_dinaturality {X Y : D} (f : X ⟶ Y) :
    dualMap D f ▷ X ≫ injection S X =
      dual D Y ◁ f ≫ injection S Y := by
  have h := congrArg (tensorProductFunctor (C := D)).map (capGenerator_dinaturality S f)
  simp only [Functor.map_comp] at h
  apply (cancel_epi (capPairIso (dual D Y) X).hom).mp
  dsimp only [injection]
  have h₁ := capPairIso_naturality (dualMap D f) (𝟙 X)
  have h₂ := capPairIso_naturality (𝟙 (dual D Y)) f
  simp only [tensorHom_id, id_tensorHom] at h₁ h₂
  rw [← reassoc_of% h₁, ← reassoc_of% h₂]
  simpa only [assoc, Iso.hom_inv_id_assoc] using h

/-- Actual modules over the proved separable internal algebra form an
actual finite semisimple category. -/
def moduleSkeleton := (separable S).skeleton S

end Paper18.Category.DrinfeldCoendModules
