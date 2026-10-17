import Paper18.Category.TannakianBasic
import Paper18.Category.FunctorImage
import Paper18.Category.RepresentationFunctionSeparable

/-!
# The actual regular algebra for Tannakian de-equivariantization

Strong monoidal transport preserves actual bimodule splittings of
multiplication. Applying it to `Fun(G)` constructs the actual transparent
separable commutative algebra of a specified Tannakian center, and hence
its category of internal modules.
-/
noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.Functor.LaxMonoidal CategoryTheory.Functor.OplaxMonoidal
open CategoryTheory.Functor.Monoidal
open scoped MonObj Obj
universe v u v' u'
namespace Paper18.Category
namespace SeparableAlgebra
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {D : Type u'} [Category.{v'} D] [MonoidalCategory D]
  {A : C} [MonObj A] (S : SeparableAlgebra A)
  (F : C ⥤ D) [F.Monoidal]

/-- Strong monoidal functors transport the actual bimodule section of
multiplication, with the inverse tensorator providing its target. -/
def map : SeparableAlgebra (F.obj A) where
  section_ := F.map S.section_ ≫ δ F A A
  section_mul := by
    change (F.map S.section_ ≫ δ F A A) ≫ (Functor.LaxMonoidal.μ F A A ≫ F.map μ[A]) = 𝟙 _
    simp [Category.assoc, ← F.map_comp, S.section_mul]
  left_linear := by
    change (Functor.LaxMonoidal.μ F A A ≫ F.map μ[A]) ≫ (F.map S.section_ ≫ δ F A A) =
      (F.obj A ◁ (F.map S.section_ ≫ δ F A A)) ≫
        (α_ (F.obj A) (F.obj A) (F.obj A)).inv ≫
        ((Functor.LaxMonoidal.μ F A A ≫ F.map μ[A]) ▷ F.obj A)
    simp only [Category.assoc]
    rw [← F.map_comp_assoc, S.left_linear]
    simp only [F.map_comp,
      Functor.Monoidal.map_whiskerLeft, Functor.Monoidal.map_whiskerRight,
      Functor.Monoidal.map_associator_inv]
    simp only [Category.assoc, MonoidalCategory.whiskerLeft_comp,
      MonoidalCategory.comp_whiskerRight, Functor.Monoidal.μ_δ_assoc,
      Functor.Monoidal.μ_δ, Category.comp_id]
  right_linear := by
    change (Functor.LaxMonoidal.μ F A A ≫ F.map μ[A]) ≫ (F.map S.section_ ≫ δ F A A) =
      ((F.map S.section_ ≫ δ F A A) ▷ F.obj A) ≫
        (α_ (F.obj A) (F.obj A) (F.obj A)).hom ≫
        (F.obj A ◁ (Functor.LaxMonoidal.μ F A A ≫ F.map μ[A]))
    simp only [Category.assoc]
    rw [← F.map_comp_assoc, S.right_linear]
    simp only [F.map_comp,
      Functor.Monoidal.map_whiskerLeft, Functor.Monoidal.map_whiskerRight,
      Functor.Monoidal.map_associator]
    simp only [Category.assoc, MonoidalCategory.whiskerLeft_comp,
      MonoidalCategory.comp_whiskerRight, Functor.Monoidal.μ_δ_assoc,
      Functor.Monoidal.μ_δ, Category.comp_id]

end SeparableAlgebra

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [Preadditive C] [Linear ℂ C]
  {G : Type} [Group G] [Fintype G] (T : TannakianCenter C G)

/-- The actual regular function algebra of the specified Tannakian center. -/
def TannakianCenter.regularAlgebra : C := T.inclusion.obj (Representation.functions (G := G))

instance TannakianCenter.regularAlgebraMonObj : MonObj T.regularAlgebra :=
  Functor.monObjObj _

instance TannakianCenter.regularAlgebraCommMonObj : IsCommMonObj T.regularAlgebra :=
  Functor.isCommMonObj_obj

/-- Separability of the actual transparent regular algebra is proved from
the explicit equivariant diagonal splitting on `Fun(G)`. -/
def TannakianCenter.regularAlgebraSeparable : SeparableAlgebra T.regularAlgebra :=
  Representation.functionsSeparable.map T.inclusion

lemma TannakianCenter.regularAlgebra_transparent : T.regularAlgebra ∈ mugerCenter (C := C) :=
  T.transparent _

/-- The actual regular algebra is connected: its invariant Hom space is
one dimensional, by full faithfulness of the specified Tannakian inclusion. -/
theorem TannakianCenter.regularAlgebra_connected :
    Module.finrank ℂ (𝟙_ C ⟶ T.regularAlgebra) = 1 := by
  change Module.finrank ℂ (𝟙_ C ⟶ T.inclusion.obj (Representation.functions (G := G))) = 1
  rw [finrank_hom_iso (Functor.Monoidal.εIso T.inclusion) (Iso.refl _)]
  rw [← (fullyFaithfulHomLinearEquiv T.inclusion
    (𝟙_ (FDRep ℂ G)) (Representation.functions (G := G))).finrank_eq]
  exact Representation.functions_connected

/-- The actual category of internal modules over the Tannakian regular
function algebra; this is the object-and-morphism construction underlying
de-equivariantization. Its tensor and fusion properties are proved separately. -/
abbrev TannakianCenter.Deequivariantization := Mod_ C T.regularAlgebra

/-- The actual forgetful functor from the de-equivariant module category. -/
def TannakianCenter.deequivariantForget : T.Deequivariantization ⥤ C :=
  Mod_.forget _

end Paper18.Category
