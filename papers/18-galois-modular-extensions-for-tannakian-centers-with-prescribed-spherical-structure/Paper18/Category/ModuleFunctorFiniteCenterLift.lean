import Paper18.Category.ModuleFunctorFiniteBasic
import Mathlib.CategoryTheory.Monoidal.Center

/-! # Actual transport of central lifts to prescribed underlying objects

Conjugating a genuine half-braiding along an actual isomorphism provides
the same genuine central object on the specified carrier. This will let
actual neutral-category equivalences supply crossings on the actual
graded objects, without a braiding on the whole graded category.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
universe v u vA uA
namespace Paper18.Category.ModuleFunctor
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- Transport a genuine central object along an actual carrier isomorphism. -/
def transportCenter (Z : Center C) {X : C} (e : X ≅ Z.1) : Center C :=
  ⟨X, {
    β U := whiskerRightIso e U ≪≫ Z.2.β U ≪≫ whiskerLeftIso U e.symm
    naturality {U V} f := by
      dsimp only [Iso.trans_hom, whiskerRightIso_hom, whiskerLeftIso_hom, Iso.symm_hom]
      simp only [Category.assoc]
      rw [whisker_exchange_assoc, Z.2.naturality_assoc, ← whisker_exchange]
    monoidal U V := by
      dsimp only [Iso.trans_hom, whiskerRightIso_hom, whiskerLeftIso_hom, Iso.symm_hom]
      rw [Z.2.monoidal]
      simp only [comp_whiskerRight, whiskerLeft_comp, Category.assoc]
      monoidal
      simp only [Iso.trans_hom, Iso.refl_hom, whiskerRightIso_hom, whiskerLeftIso_hom,
        Iso.symm_hom, id_whiskerRight, whiskerLeft_id, Category.id_comp,
        Category.comp_id, Category.assoc]
      simp only [Iso.inv_hom_id_assoc]
      simp only [← whiskerLeft_comp_assoc, ← comp_whiskerRight_assoc,
        Iso.inv_hom_id, id_whiskerRight, Category.id_comp] }⟩

@[simp] lemma transportCenter_obj (Z : Center C) {X : C} (e : X ≅ Z.1) :
    (transportCenter Z e).1 = X := rfl

@[simp] lemma transportCenter_β (Z : Center C) {X : C} (e : X ≅ Z.1) (U : C) :
    ((transportCenter Z e).2.β U).hom =
      e.hom ▷ U ≫ (Z.2.β U).hom ≫ U ◁ e.inv := rfl

@[simp] lemma transportCenter_refl_β (Z : Center C) (U : C) :
    ((transportCenter Z (Iso.refl Z.1)).2.β U).hom = (Z.2.β U).hom := by
  simp only [transportCenter_β, Iso.refl_hom, Iso.refl_inv, id_whiskerRight,
    whiskerLeft_id, Category.id_comp, Category.comp_id]

/-- The actual carrier isomorphism lifts to a genuine isomorphism in the center. -/
def transportCenterIso (Z : Center C) {X : C} (e : X ≅ Z.1) : transportCenter Z e ≅ Z :=
  Center.isoMk {
    f := e.hom
    comm U := by simp [transportCenter_β, Category.assoc, ← whiskerLeft_comp] }

@[simp] lemma transportCenterIso_hom_f (Z : Center C) {X : C} (e : X ≅ Z.1) :
    (transportCenterIso Z e).hom.f = e.hom := rfl

@[simp] lemma transportCenterIso_inv_f (Z : Center C) {X : C} (e : X ≅ Z.1) :
    (transportCenterIso Z e).inv.f = e.inv := by
  change inv e.hom = e.inv
  simp

section Functor
variable {A : Type uA} [Category.{vA} A]
  (L : A ⥤ Center C) (F : A ⥤ C) (e : F ≅ L ⋙ Center.forget C)

/-- Reindex an actual central lift onto the exact prescribed underlying
objects, using the given actual natural isomorphism. -/
def strictCenterFunctor : A ⥤ Center C where
  obj X := transportCenter (L.obj X) (e.app X)
  map {X Y} f := (transportCenterIso (L.obj X) (e.app X)).hom ≫ L.map f ≫
    (transportCenterIso (L.obj Y) (e.app Y)).inv
  map_id X := by simp
  map_comp f g := by simp [Category.assoc]

@[simp] lemma strictCenterFunctor_obj (X : A) :
    ((strictCenterFunctor L F e).obj X).1 = F.obj X := rfl

/-- The reindexed central map has exactly the prescribed actual
underlying morphism. -/
@[simp] lemma strictCenterFunctor_map_f {X Y : A} (f : X ⟶ Y) :
    ((strictCenterFunctor L F e).map f).f = F.map f := by
  simp only [strictCenterFunctor, Center.comp_f,
    transportCenterIso_hom_f, transportCenterIso_inv_f]
  change e.hom.app X ≫ (L ⋙ Center.forget C).map f ≫ e.inv.app Y = F.map f
  rw [← e.hom.naturality_assoc]
  simp

/-- Reindexing retains the actual central functor up to a genuine natural
isomorphism in the actual Drinfeld center. -/
def strictCenterFunctorIso : strictCenterFunctor L F e ≅ L :=
  NatIso.ofComponents (fun X => transportCenterIso (L.obj X) (e.app X))
    (fun f => by simp [strictCenterFunctor, Category.assoc])

/-- The underlying reindexed central lift recovers the original actual
underlying functor through identity component maps. -/
def strictCenterFunctorForgetIso : strictCenterFunctor L F e ⋙ Center.forget C ≅ F :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun f => by
    change ((strictCenterFunctor L F e).map f).f ≫ 𝟙 _ = 𝟙 _ ≫ F.map f
    simp)

instance strictCenterFunctor_forget_full [F.Full] :
    (strictCenterFunctor L F e ⋙ Center.forget C).Full :=
  Functor.Full.of_iso (strictCenterFunctorForgetIso L F e).symm

instance strictCenterFunctor_forget_faithful [F.Faithful] :
    (strictCenterFunctor L F e ⋙ Center.forget C).Faithful :=
  Functor.Faithful.of_iso (strictCenterFunctorForgetIso L F e).symm

end Functor

end Paper18.Category.ModuleFunctor
