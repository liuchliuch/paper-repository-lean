import Paper18.Category.FusionSubcategoryIntegral

/-! # Actual tensor functors between inherited full fusion subcategories -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Functor.LaxMonoidal CategoryTheory.Functor.Monoidal
universe v u v' u'
namespace Paper18.Category
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {D : Type u'} [Category.{v'} D] [MonoidalCategory D]
  (P : ObjectProperty C) [P.IsMonoidal] (Q : ObjectProperty D) [Q.IsMonoidal]
  (F : C ⥤ D) [F.Monoidal] (hF : ∀ X : C, P X → Q (F.obj X))

/-- Restrict the source and target of an actual functor to the indicated
full subcategories. The object condition is the actual image property. -/
def fullSubcategoryFunctor : P.FullSubcategory ⥤ Q.FullSubcategory where
  obj X := ⟨F.obj X.obj, hF X.obj X.property⟩
  map f := F.map f
  map_id X := F.map_id X.obj
  map_comp f g := F.map_comp f g

instance fullSubcategoryFunctor_monoidal : (fullSubcategoryFunctor P Q F hF).Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := Q.isoMk (εIso F)
      μIso X Y := Q.isoMk (μIso F X.obj Y.obj)
      μIso_hom_natural_left := fun f Z => Functor.LaxMonoidal.μ_natural_left F f Z.obj
      μIso_hom_natural_right := fun X f => Functor.LaxMonoidal.μ_natural_right F X.obj f
      associativity X Y Z := Functor.LaxMonoidal.associativity F X.obj Y.obj Z.obj
      left_unitality X := Functor.LaxMonoidal.left_unitality F X.obj
      right_unitality X := Functor.LaxMonoidal.right_unitality F X.obj }

variable [Preadditive C] [Preadditive D]

instance fullSubcategoryFunctor_additive [F.Additive] :
    (fullSubcategoryFunctor P Q F hF).Additive where
  map_add := by intros; exact F.map_add

instance fullSubcategoryFunctor_linear [Linear ℂ C] [Linear ℂ D] [F.Linear ℂ] :
    (fullSubcategoryFunctor P Q F hF).Linear ℂ where
  map_smul f c := F.map_smul c f

variable (G : C ⥤ D) [G.Monoidal] (hG : ∀ X : C, Q (G.obj X))

/-- Lift an actual tensor functor into an actual full tensor subcategory. -/
def fullSubcategoryLift : C ⥤ Q.FullSubcategory := ObjectProperty.lift Q G hG

instance fullSubcategoryLift_monoidal : (fullSubcategoryLift Q G hG).Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := Q.isoMk (εIso G)
      μIso X Y := Q.isoMk (μIso G X Y)
      μIso_hom_natural_left := fun f Z => Functor.LaxMonoidal.μ_natural_left G f Z
      μIso_hom_natural_right := fun X f => Functor.LaxMonoidal.μ_natural_right G X f
      associativity X Y Z := Functor.LaxMonoidal.associativity G X Y Z
      left_unitality X := Functor.LaxMonoidal.left_unitality G X
      right_unitality X := Functor.LaxMonoidal.right_unitality G X }

instance fullSubcategoryLift_additive [G.Additive] : (fullSubcategoryLift Q G hG).Additive where
  map_add := by intros; exact G.map_add

instance fullSubcategoryLift_linear [Linear ℂ C] [Linear ℂ D] [G.Linear ℂ] :
    (fullSubcategoryLift Q G hG).Linear ℂ where
  map_smul f c := G.map_smul c f

instance fullSubcategoryLift_full [G.Full] : (fullSubcategoryLift Q G hG).Full := by
  dsimp [fullSubcategoryLift]; infer_instance

instance fullSubcategoryLift_faithful [G.Faithful] : (fullSubcategoryLift Q G hG).Faithful := by
  dsimp [fullSubcategoryLift]; infer_instance

omit [G.Monoidal] in
instance fullSubcategoryLift_braided [BraidedCategory C] [BraidedCategory D] [G.Braided] :
    (fullSubcategoryLift Q G hG).Braided := by
  letI : G.Monoidal := (inferInstance : G.Braided).toMonoidal
  exact {
  braided X Y := by
    apply Q.ι.map_injective
    simpa only [Functor.map_comp, fullSubcategoryLift_monoidal,
      Functor.CoreMonoidal.toMonoidal, Functor.CoreMonoidal.toLaxMonoidal,
      Functor.LaxMonoidal.μ, fullSubcategoryLift, ObjectProperty.lift,
      ObjectProperty.ι, ObjectProperty.isoMk, ObjectProperty.fullBraidedSubcategory,
      BraidedCategory.ofFaithful, inducedFunctor, μIso_hom] using
        (Functor.LaxBraided.braided (F := G) X Y) }

end Paper18.Category
