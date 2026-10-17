import Paper18.Category.FixedBoundaryCrossedFunctor
import Paper18.Category.FixedBoundaryNeutralAction

/-!
# Both genuine crossing comparisons retain the specified neutral alpha

The actual extended neutral comparison respects algebra translation.
Inserting it into the actual crossed-functor equation therefore gives the
comparison on the second crossing with its prescribed neutral component.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped MonObj Obj
universe v u v' u'
namespace Paper18.Category.FixedBoundary
variable {A : Type u} [Category.{v} A] [Preadditive A] [Linear ℂ A]
  [MonoidalCategory A] [BraidedCategory A] [MonoidalPreadditive A] [MonoidalLinear ℂ A]
  [HasKernels A] [HasFiniteBiproducts A] [RightRigidCategory A] [HasCoequalizers A]
  [∀ X Y : A, FiniteDimensional ℂ (X ⟶ Y)]
  {N : Type u'} [Category.{v'} N] [Preadditive N] [Linear ℂ N]
  [MonoidalCategory N] [BraidedCategory N] [MonoidalPreadditive N] [MonoidalLinear ℂ N]
  [RightRigidCategory N] [HasCoequalizers N]
  (i : A ⥤ N) [i.Braided] [i.Full] [i.Faithful] [i.Additive] [i.Linear ℂ]
  (P : BoundaryAutoequivalence i) (R : A) [MonObj R] [IsCommMonObj R]
  {T : N} (B : TensorInverse T)
  (himage : ∀ X : A, Centralizes T (i.obj X))
  (S : SeparableAlgebra R)
  (hfull : ∀ Y : N, Centralizes T Y → ∃ X : A, Nonempty (i.obj X ≅ Y))
  (e : P.functor.obj T ≅ T)
  (t : R ≅ R) [IsMonHom t.hom]

local instance imageAlgebraTranslation : IsMonHom (i.mapIso t).hom := by
  change IsMonHom (i.map t.hom)
  infer_instance

/-- The other actual crossed map intertwines the actual left and right
lineators formed from the specified neutral alpha. -/
theorem neutralComparison_translatedBraiding
    (M : SignKernel.Positive (neutralModuleCharacter i R B himage))
    (Y : Mod_ N (i.obj R))
    (hY : (doubleBraiding (i.obj R) Y.X).hom = i.map t.hom ▷ Y.X) :
    ((neutralComparisonUnderlying i P R B himage S hfull e).inv.app M ▷
        (P.moduleFunctor R).obj Y) ≫
      Functor.LaxMonoidal.μ (P.moduleFunctor R) M.obj Y ≫
        (P.moduleFunctor R).map (translatedBraidingHom (i.mapIso t) M.obj Y hY) =
      translatedBraidingHom (i.mapIso t) M.obj ((P.moduleFunctor R).obj Y)
        (P.moduleFunctor_translated_monodromy R t Y hY) ≫
          ((P.moduleFunctor R).obj Y ◁
            (neutralComparisonUnderlying i P R B himage S hfull e).inv.app
              ((neutralModuleComap i R B himage t.hom).obj M)) ≫
                Functor.LaxMonoidal.μ (P.moduleFunctor R) Y
                  ((Mod_.comap (i.map t.hom)).obj M.obj) := by
  rw [P.moduleFunctor_translatedBraiding]
  erw [translatedBraiding_naturality_left_assoc]
  erw [← whiskerLeft_comp_assoc, neutralComparison_comap_inv]
  rfl

end Paper18.Category.FixedBoundary
