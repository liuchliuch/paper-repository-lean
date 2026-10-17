import Paper18.Category.LocalModulesCenterBasic

/-! # The actual fully faithful local-module functor to the Drinfeld center -/
noncomputable section
open Classical CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open CategoryTheory.BraidedCategory
open scoped MonObj
universe v u
namespace Paper18.Category.SeparableAlgebra
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [RightRigidCategory C] [HasCoequalizers C] {A : C} [MonObj A] [IsCommMonObj A]
  (S : SeparableAlgebra A)
open RelativeTensor

/-- An actual local module with its constructed central half-braiding. -/
def localCenterObj (M : LocalModules A) : Center (Mod_ C A) :=
  ⟨M.obj, S.localHalfBraiding M.obj M.property⟩

/-- Every actual map of local modules intertwines the constructed central
half-braidings. -/
def localCenterMap {M N : LocalModules A} (f : M ⟶ N) :
    S.localCenterObj M ⟶ S.localCenterObj N where
  f := f
  comm P := by
    apply (cancel_epi (S.localCrossingIso M.obj P M.property).hom).mp
    apply (cancel_mono (S.localCrossingIso N.obj P N.property).hom).mp
    change ((S.localCrossingIso M.obj P M.property).hom ≫ (show M.obj ⟶ N.obj from f) ▷ P ≫
        (S.localCrossingIso N.obj P N.property).inv) ≫
        (S.localCrossingIso N.obj P N.property).hom =
      ((S.localCrossingIso M.obj P M.property).hom ≫
        (S.localCrossingIso M.obj P M.property).inv ≫ P ◁ (show M.obj ⟶ N.obj from f)) ≫
        (S.localCrossingIso N.obj P N.property).hom
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Iso.hom_inv_id_assoc]
    exact (localBraiding_naturality_right P f M.property N.property).symm

/-- Local modules embed fully faithfully into the actual Drinfeld center
using the inverse positive crossing. -/
def localCenterFunctor : LocalModules A ⥤ Center (Mod_ C A) where
  obj := S.localCenterObj
  map := S.localCenterMap
  map_id M := by apply Center.ext; rfl
  map_comp f g := by apply Center.ext; rfl

instance localCenterFunctorFaithful : S.localCenterFunctor.Faithful where
  map_injective h := congrArg Center.Hom.f h

instance localCenterFunctorFull : S.localCenterFunctor.Full where
  map_surjective f := ⟨f.f, by apply Center.ext; rfl⟩

/-- The local crossing with a free module is the actual free central
half-braiding, as an equality of isomorphisms. -/
theorem localCrossingIso_free (M : Mod_ C A) (hM : IsLocalModule M) (X : C) :
    S.localCrossingIso M (InternalModule.free A X) hM = freeCentralIso X M := by
  apply Iso.ext
  exact localBraidingHom_free X M hM

/-- The actual central free image centralizes the actual local-module image. -/
theorem centralFree_centralizes_local (X : C) (M : LocalModules A) :
    Centralizes ((centralFreeFunctor (A := A)).obj X) (S.localCenterFunctor.obj M) := by
  rw [centralizes_iff]
  apply Center.ext
  change (freeCentralIso X M.obj).hom ≫
      (S.localCrossingIso M.obj (InternalModule.free A X) M.property).inv = 𝟙 _
  rw [S.localCrossingIso_free, Iso.hom_inv_id]

/-- The constructed local center image lies in the actual centralizer of
the whole central free image. -/
theorem localCenter_mem_centralizer (M : LocalModules A) :
    S.localCenterFunctor.obj M ∈
      centralizer (Set.range (centralFreeFunctor (A := A)).obj) := by
  rintro _ ⟨X, rfl⟩
  exact (S.centralFree_centralizes_local X M).symm

end Paper18.Category.SeparableAlgebra
