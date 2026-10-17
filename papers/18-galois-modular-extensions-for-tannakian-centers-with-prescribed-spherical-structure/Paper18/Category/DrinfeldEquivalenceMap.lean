import Paper18.Category.DrinfeldEquivalenceMapHexagon
import Paper18.Category.DrinfeldEquivalenceMapDensity

/-! # The actual functor between centers induced by a tensor equivalence -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Functor.LaxMonoidal CategoryTheory.Functor.OplaxMonoidal CategoryTheory.Functor.Monoidal
universe v u v' u'
namespace Paper18.Category.DrinfeldEquivalence
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {D : Type u'} [Category.{v'} D] [MonoidalCategory D]
  (E : C ≌ D) [E.functor.Monoidal]

lemma halfIso_monoidal (Z : Center C) (U V : D) :
    (halfIso E Z (U ⊗ V)).hom =
      (α_ _ _ _).inv ≫ (halfIso E Z U).hom ▷ V ≫
        (α_ _ _ _).hom ≫ U ◁ (halfIso E Z V).hom ≫ (α_ _ _ _).inv := by
  have h : (halfNatIso E Z).hom.app
      (E.functor.obj (E.inverse.obj U) ⊗ E.functor.obj (E.inverse.obj V)) =
      hexagonRHS (halfNatIso E Z) (E.functor.obj (E.inverse.obj U))
        (E.functor.obj (E.inverse.obj V)) :=
    halfIso_image_monoidal E Z (E.inverse.obj U) (E.inverse.obj V)
  exact hexagon_of_iso_right (halfNatIso E Z) U (E.counitIso.app V)
    (hexagon_of_iso_left (halfNatIso E Z) (E.counitIso.app U)
      (E.functor.obj (E.inverse.obj V)) h)

/-- The half-braiding is constructed from actual inverse transport; its
naturality and hexagon are proved, not supplied as additional data. -/
def halfBraiding (Z : Center C) : HalfBraiding (E.functor.obj Z.1) where
  β := halfIso E Z
  monoidal := halfIso_monoidal E Z
  naturality := halfIso_naturality E Z

lemma map_comm {Z W : Center C} (f : Z ⟶ W) (U : D) :
    E.functor.map f.f ▷ U ≫ (halfIso E W U).hom =
      (halfIso E Z U).hom ≫ U ◁ E.functor.map f.f := by
  simp only [halfIso_hom, assoc]
  rw [← whisker_exchange_assoc]
  simp only [Functor.comp_obj]
  rw [μ_natural_left_assoc E.functor f.f (E.inverse.obj U),
    ← E.functor.map_comp_assoc, f.comm, E.functor.map_comp_assoc,
    ← δ_natural_right_assoc E.functor (E.inverse.obj U) f.f]
  rw [whisker_exchange]
  rfl

variable (F : C ⥤ D) [F.Monoidal] [F.IsEquivalence]

instance equivalenceFunctorMonoidal : F.asEquivalence.functor.Monoidal :=
  inferInstanceAs F.Monoidal

/-- The crossing on an actual object in the original functor's image. -/
@[reassoc] lemma halfIso_functor_image (Z : Center C) (U : C) :
    (halfIso F.asEquivalence Z (F.obj U)).hom =
      μ F Z.1 U ≫ F.map (Z.2.β U).hom ≫ δ F U Z.1 :=
  halfIso_image F.asEquivalence Z U

@[reassoc] lemma halfIso_functor_naturality (Z : Center C) {U V : D} (f : U ⟶ V) :
    F.obj Z.1 ◁ f ≫ (halfIso F.asEquivalence Z V).hom =
      (halfIso F.asEquivalence Z U).hom ≫ f ▷ F.obj Z.1 :=
  halfIso_naturality F.asEquivalence Z f

/-- The actual center functor induced by an actual strong tensor
equivalence, with the original functor on every underlying object and map. -/
def map : Center C ⥤ Center D where
  obj Z := ⟨F.obj Z.1, halfBraiding F.asEquivalence Z⟩
  map f := ⟨F.map f.f, map_comm F.asEquivalence f⟩
  map_id Z := by apply Center.Hom.ext; exact F.map_id Z.1
  map_comp f g := by apply Center.Hom.ext; exact F.map_comp f.f g.f

@[simp] lemma map_obj_fst (Z : Center C) : ((map F).obj Z).1 = F.obj Z.1 := rfl
@[simp] lemma map_map_f {Z W : Center C} (f : Z ⟶ W) : ((map F).map f).f = F.map f.f := rfl

/-- The induced center functor agrees strictly with the underlying
functor after forgetting the half-braiding. -/
def forgetIso : map F ⋙ Center.forget D ≅ Center.forget C ⋙ F := Iso.refl _

end Paper18.Category.DrinfeldEquivalence
