import Paper18.Category.CrossedBraidedGaugingNeutralCrossing
import Paper18.Category.FusionSubcategoryBasic

/-! # The actual braided neutral full subcategory of a crossed category -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
universe v u w
namespace Paper18.Category.CrossedBraidedGauging
variable {G : Type w} [Group G] [Fintype G]
  {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]
  [MonoidalPreadditive C] [HasFiniteBiproducts C]
  (P : Grading G C)

/-- The actual degree-one object property. -/
def neutralProperty : ObjectProperty C := P.Homogeneous 1

abbrev Neutral := (neutralProperty P).FullSubcategory

instance neutralProperty_monoidal : (neutralProperty P).IsMonoidal where
  prop_unit := P.homogeneous_unit
  prop_tensor X Y hX hY := by
    simpa only [neutralProperty, one_mul] using P.homogeneous_tensor hX hY

instance neutralProperty_additive : IsAdditiveFullProperty (neutralProperty P) where
  of_retract r hY := P.homogeneous_retract r hY
  biproduct f hf := P.homogeneous_biproduct f 1 hf

/-- The genuine strong monoidal inclusion of the neutral full category. -/
abbrev neutralInclusion : Neutral P ⥤ C := (neutralProperty P).ι

namespace CrossedBraiding
variable {P} {A : WeakAction G C}
  [∀ g : G, (A.ρ g).Monoidal] [A.IsMonoidal]
  [∀ g : G, (A.ρ g).Additive]
  {Q : GradedAction P A} (B : CrossedBraiding P A Q)

/-- The neutral braiding is the actual neutral crossed isomorphism. -/
def neutralBraiding (X Y : Neutral P) : X ⊗ Y ≅ Y ⊗ X :=
  (neutralProperty P).isoMk (B.neutralIso X.obj X.property Y.obj)

/-- The actual neutral category is braided. This is derived from the
crossed hexagons, not assumed as an extra structure on the graded category. -/
def neutralBraidedCategory : BraidedCategory (Neutral P) where
  braiding := B.neutralBraiding
  braiding_naturality_right X {Y Z} f := by
    exact B.neutralIso_naturality_right X.obj X.property f
  braiding_naturality_left {X Y} f Z := by
    exact B.neutralIso_naturality_left X.property Y.property f Z.obj
  hexagon_forward X Y Z := by
    change (α_ X.obj Y.obj Z.obj).hom ≫
      (B.neutralIso X.obj X.property (Y.obj ⊗ Z.obj)).hom ≫
        (α_ Y.obj Z.obj X.obj).hom = _
    rw [B.neutralIso_tensor_right]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Iso.hom_inv_id_assoc]
    rfl
  hexagon_reverse X Y Z := by
    change (α_ X.obj Y.obj Z.obj).inv ≫
      (B.neutralIso (X.obj ⊗ Y.obj) (X ⊗ Y).property Z.obj).hom ≫
        (α_ Z.obj X.obj Y.obj).inv = _
    rw [B.neutralIso_tensor_left]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.inv_hom_id_assoc]
    rfl

end CrossedBraiding
end Paper18.Category.CrossedBraidedGauging
