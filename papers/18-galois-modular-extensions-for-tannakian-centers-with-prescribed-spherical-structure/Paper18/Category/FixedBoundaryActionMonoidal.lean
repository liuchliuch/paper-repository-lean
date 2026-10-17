import Paper18.Category.FixedBoundaryActionTransport
import Paper18.Category.FixedBoundaryRegularMonoidal
import Paper18.Category.FixedBoundaryModuleFunctorMonoidal

/-!
# Actual monoidal compatibility with the regular action

The specified algebra comparison α_R intertwines regular translations by
naturality. Its induced comparisons on modules respect both actual tensor
and unit comparisons, as proved before the balancing quotient.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped MonObj Obj
universe v u v' u' w
namespace Paper18.Category.WeakAction.Intertwiner
variable {G : Type w} [Group G]
  {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {D : Type u'} [Category.{v'} D] [MonoidalCategory D]
  {A : WeakAction G C} {B : WeakAction G D}
  [∀ g, (A.ρ g).Monoidal] [∀ g, (B.ρ g).Monoidal]
  (F : A.Intertwiner B) [F.functor.Monoidal]

/-- Monoidality of an action intertwiner means that its actual comparison
isomorphisms are monoidal natural isomorphisms. -/
class IsMonoidal : Prop where
  comparison_monoidal : ∀ g, NatTrans.IsMonoidal (F.comparison g).hom

attribute [instance] IsMonoidal.comparison_monoidal
end Paper18.Category.WeakAction.Intertwiner

namespace Paper18.Category
open RelativeTensor FixedBoundary
variable {G : Type} [Group G] [Fintype G]
  {N : Type u} [Category.{v} N] [Preadditive N] [Linear ℂ N]
  [MonoidalCategory N] [BraidedCategory N]
  [MonoidalPreadditive N] [MonoidalLinear ℂ N]
  [RightRigidCategory N] [HasCoequalizers N]
  {i : FDRep ℂ G ⥤ N} [i.Braided] (P : BoundaryAutoequivalence i)

/-- Expose the strong tensor structure at the regular-algebra specialization. -/
instance BoundaryAutoequivalence.regularModuleFunctorMonoidal :
    (P.moduleFunctor (Representation.functions (G := G))).Monoidal :=
  P.moduleFunctorMonoidal Representation.functions

/-- The intertwiner retains exactly the derived regular-module tensor structure. -/
instance BoundaryAutoequivalence.regularActionIntertwinerFunctorMonoidal :
    P.regularActionIntertwiner.functor.Monoidal := by
  change (P.moduleFunctor (Representation.functions (G := G))).Monoidal
  exact P.moduleFunctorMonoidal Representation.functions

instance BoundaryAutoequivalence.translatedModuleFunctorMonoidalLeft (g : G) :
    (moduleTranslation i g ⋙ P.moduleFunctor Representation.functions).Monoidal := by
  letI : (P.moduleFunctor (Representation.functions (G := G))).Monoidal :=
    P.moduleFunctorMonoidal Representation.functions
  letI : (moduleTranslation i g).Monoidal := moduleTranslationMonoidal i g
  infer_instance

instance BoundaryAutoequivalence.translatedModuleFunctorMonoidalRight (g : G) :
    (P.moduleFunctor Representation.functions ⋙ moduleTranslation i g).Monoidal := by
  letI : (P.moduleFunctor (Representation.functions (G := G))).Monoidal :=
    P.moduleFunctorMonoidal Representation.functions
  letI : (moduleTranslation i g).Monoidal := moduleTranslationMonoidal i g
  infer_instance

instance BoundaryAutoequivalence.translatedModuleFunctorLaxLeft (g : G) :
    (moduleTranslation i g ⋙ P.moduleFunctor Representation.functions).LaxMonoidal :=
  (P.translatedModuleFunctorMonoidalLeft g).toLaxMonoidal

instance BoundaryAutoequivalence.translatedModuleFunctorLaxRight (g : G) :
    (P.moduleFunctor Representation.functions ⋙ moduleTranslation i g).LaxMonoidal :=
  (P.translatedModuleFunctorMonoidalRight g).toLaxMonoidal

local instance boundaryModuleFunctorMonoidalLocal :
    (P.moduleFunctor (Representation.functions (G := G))).Monoidal :=
  P.moduleFunctorMonoidal Representation.functions

local instance translationFunctorMonoidalLocal (g : G) :
    (moduleTranslation i g).Monoidal := moduleTranslationMonoidal i g

/-- The actual identity underlying comparison commutes with tensorators
and unit comparisons; no monoidal action comparison is assumed. -/
instance BoundaryAutoequivalence.moduleTranslationComparisonMonoidal (g : G) :
    @NatTrans.IsMonoidal (Modules i) _ _ (Modules i) _ _
      (moduleTranslation i g ⋙ P.moduleFunctor Representation.functions)
      (P.moduleFunctor Representation.functions ⋙ moduleTranslation i g)
      (P.moduleTranslationComparison g).hom
      (P.translatedModuleFunctorLaxLeft g) (P.translatedModuleFunctorLaxRight g) := by
  letI : (moduleTranslation i g ⋙ P.moduleFunctor Representation.functions).LaxMonoidal :=
    P.translatedModuleFunctorLaxLeft g
  letI : (P.moduleFunctor Representation.functions ⋙ moduleTranslation i g).LaxMonoidal :=
    P.translatedModuleFunctorLaxRight g
  constructor
  ·
    simp only [Functor.LaxMonoidal.comp_ε]
    apply Mod_.Hom.ext
    simp only [Mod_.comp_hom', Category.assoc]
    change (Functor.LaxMonoidal.ε (P.moduleFunctor Representation.functions)).hom ≫
        P.functor.map (Functor.LaxMonoidal.ε (moduleTranslation i g)).hom ≫ 𝟙 _ =
      (Functor.LaxMonoidal.ε (moduleTranslation i g)).hom ≫
        (Functor.LaxMonoidal.ε (P.moduleFunctor Representation.functions)).hom
    rw [P.moduleFunctor_ε_hom, moduleTranslation_ε_hom, Category.comp_id]
    exact P.inverse_algebra_translation g⁻¹
  · intro M N
    simp only [Functor.LaxMonoidal.comp_μ]
    apply module_hom_ext
    simp only [Mod_.comp_hom', Category.assoc]
    change π ((P.moduleFunctor Representation.functions).obj ((moduleTranslation i g).obj M))
        ((P.moduleFunctor Representation.functions).obj ((moduleTranslation i g).obj N)) ≫
        (Functor.LaxMonoidal.μ (P.moduleFunctor Representation.functions)
          ((moduleTranslation i g).obj M) ((moduleTranslation i g).obj N)).hom ≫
        P.functor.map (Functor.LaxMonoidal.μ (moduleTranslation i g) M N).hom ≫ 𝟙 _ =
      π ((P.moduleFunctor Representation.functions).obj ((moduleTranslation i g).obj M))
        ((P.moduleFunctor Representation.functions).obj ((moduleTranslation i g).obj N)) ≫
        ((P.moduleTranslationComparison g).hom.app M ⊗ₘ
          (P.moduleTranslationComparison g).hom.app N).hom ≫
        (Functor.LaxMonoidal.μ (moduleTranslation i g)
          ((P.moduleFunctor Representation.functions).obj M)
          ((P.moduleFunctor Representation.functions).obj N)).hom ≫
        (Functor.LaxMonoidal.μ (P.moduleFunctor Representation.functions) M N).hom
    rw [π_tensorHom_assoc]
    simp only [P.moduleTranslationComparison_hom, id_tensorHom_id, Category.id_comp,
      Category.comp_id]
    erw [P.π_moduleFunctor_μ_assoc, ← P.functor.map_comp, π_moduleTranslation_μ,
      π_moduleTranslation_μ_assoc, P.π_moduleFunctor_μ]
    erw [MonoidalCategory.id_tensorHom_id, Category.id_comp]
    rfl

/-- The genuine action intertwiner constructed from a boundary pair is
monoidal with its actual relative tensor structures. -/
instance BoundaryAutoequivalence.regularActionIntertwinerMonoidal :
    P.regularActionIntertwiner.IsMonoidal where
  comparison_monoidal g := P.moduleTranslationComparisonMonoidal g

end Paper18.Category
