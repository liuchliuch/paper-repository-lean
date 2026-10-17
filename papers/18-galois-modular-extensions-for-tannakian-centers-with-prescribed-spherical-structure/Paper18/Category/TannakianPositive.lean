import Paper18.Category.RepresentationPivotalEvaluation
import Paper18.Category.PivotalPullback
import Paper18.Category.TannakianDeequivariantization

/-!
# Positive pivotal structures on actual Tannakian images

The pivotal structure pulled back through a fully faithful braided inclusion
has positive actual traces. Uniqueness identifies it with the canonical
representation pivotal structure, and the canonical rigid comparison then
proves that every representation in the image has identity twist.
-/
noncomputable section
open Classical
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
universe v u w
namespace Paper18.Category
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [RightRigidCategory C] [Preadditive C] [Linear ℂ C]
  [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ C)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  (J : PivotalStructure C) (hJ : J.Positive)
  {G : Type} [Group G] [Fintype G]

include S hJ

namespace Representation
variable (F : FDRep ℂ G ⥤ C) [F.Braided] [F.Full] [F.Faithful]
  [F.Additive] [F.Linear ℂ]

/-- The actual pivotal structure pulled back through the given inclusion
is the canonical evaluation-to-double-dual structure on representations. -/
lemma pivotalPullback_eq_canonical :
    pivotalPullback F J = pivotalStructure (G := G) :=
  PivotalStructure.eq_of_positive _ _ (skeleton G)
    (pivotalPullback_positive F J S hJ) pivotalStructure_positive

/-- A fully faithful braided complex-linear inclusion into a positive
pivotal fusion category preserves the canonical representation pivotal
structure. Its trace preservation is a consequence of the actual rigid
comparison, rather than an additional premise. -/
lemma preservesPivotal_of_positive :
    PreservesPivotal F (pivotalStructure (G := G)) J := by
  have h := pivotalPullback_preserves F J
  rw [pivotalPullback_eq_canonical S J hJ F] at h
  exact h

/-- Every actual representation in the image has identity induced twist. -/
lemma image_twist_of_positive (V : FDRep ℂ G) :
    (J.twistIso (F.obj V)).hom = 𝟙 (F.obj V) := by
  rw [J.twistIso_hom, ← preservesPivotal_of_positive S J hJ F V]
  change (F.map (drinfeldIso V).hom ≫ (doubleDualComparison F V).hom) ≫
    (drinfeldIso (F.obj V)).inv = 𝟙 (F.obj V)
  rw [doubleDualComparison_drinfeld]
  exact (drinfeldIso (F.obj V)).hom_inv_id

end Representation

/-- In a positive pivotal category, the actual Tannakian regular function
algebra has identity twist. This supplies the balancing premise for the
actual pivotal construction on its local modules. -/
lemma TannakianCenter.regularAlgebra_twist (T : TannakianCenter C G) :
    (J.twistIso T.regularAlgebra).hom = 𝟙 T.regularAlgebra :=
  Representation.image_twist_of_positive S J hJ T.inclusion _

end Paper18.Category
