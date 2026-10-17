import Paper18.Category.FixedBoundaryAlgebra
import Paper18.Category.FixedBoundaryRegularAction

/-!
# Actual action transport with the specified boundary

The comparison `α_R` intertwines every regular translation by naturality.
This gives an actual coherent intertwiner for the regular group action on
modules. In particular the chosen identification of the categorical action
is retained, rather than discarded before applying a cochain calculation.
-/
noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped MonObj Obj
universe v u v' u' w
namespace Paper18.Category
namespace WeakAction
variable {G : Type w} [Group G]
  {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

/-- A genuine functor intertwining two weak actions, with actual natural
comparison isomorphisms and their unit and multiplication coherences. -/
structure Intertwiner (A : WeakAction G C) (B : WeakAction G D) where
  functor : C ⥤ D
  comparison : ∀ g, A.ρ g ⋙ functor ≅ functor ⋙ B.ρ g
  unit : ∀ X, (comparison 1).hom.app X ≫ B.unitIso.hom.app (functor.obj X) =
    functor.map (A.unitIso.hom.app X)
  mul : ∀ g h X,
    functor.map ((A.mulIso g h).hom.app X) ≫ (comparison (g * h)).hom.app X =
      (comparison g).hom.app ((A.ρ h).obj X) ≫
        (B.ρ g).map ((comparison h).hom.app X) ≫
          (B.mulIso g h).hom.app (functor.obj X)

end WeakAction

section Boundary
variable {G : Type} [Group G] [Fintype G]
  {N : Type u} [Category.{v} N] [Preadditive N] [Linear ℂ N]
  [MonoidalCategory N] [BraidedCategory N]
  {i : FDRep ℂ G ⥤ N} [i.Monoidal] (P : BoundaryAutoequivalence i)

open FixedBoundary

/-- Naturality of the specified `α` forces its actual inverse algebra
comparison to commute with every regular translation. -/
theorem BoundaryAutoequivalence.inverse_algebra_translation (g : G) :
    (P.boundaryAlgebraIso (Representation.functions (G := G))).inv ≫
        P.functor.map (regularTranslation i g) =
      regularTranslation i g ≫ (P.boundaryAlgebraIso (Representation.functions (G := G))).inv := by
  let e := P.boundaryAlgebraIso (Representation.functions (G := G))
  apply (cancel_mono e.hom).mp
  have hn := P.boundary.hom.naturality (Representation.rightTranslation g)
  change P.functor.map (regularTranslation i g) ≫ P.boundary.hom.app _ =
    P.boundary.hom.app _ ≫ regularTranslation i g at hn
  rw [← P.boundaryAlgebraIso_hom] at hn
  change (e.inv ≫ P.functor.map (regularTranslation i g)) ≫ e.hom =
    (regularTranslation i g ≫ e.inv) ≫ e.hom
  rw [Category.assoc, hn, ← Category.assoc, e.inv_hom_id, Category.id_comp,
    Category.assoc, e.inv_hom_id]
  exact (Category.comp_id _).symm

/-- The identity underlying map is an actual module intertwiner between
translation before and after the fixed-boundary functor. -/
def BoundaryAutoequivalence.moduleTranslationComparisonHom (g : G) (M : Modules i) :
    (moduleTranslation i g ⋙ P.moduleFunctor (Representation.functions (G := G))).obj M ⟶
      (P.moduleFunctor (Representation.functions (G := G)) ⋙ moduleTranslation i g).obj M :=
  Mod_.Hom.mk' (𝟙 (P.functor.obj M.X)) (by
    change ((P.boundaryAlgebraIso (Representation.functions (G := G))).inv ▷ P.functor.obj M.X ≫
        Functor.LaxMonoidal.μ P.functor (regularAlgebra i) M.X ≫
          P.functor.map ((regularTranslation i g⁻¹ ▷ M.X) ≫ γ[regularAlgebra i,M.X])) ≫ 𝟙 _ =
      (regularAlgebra i ◁ 𝟙 _) ≫ (regularTranslation i g⁻¹ ▷ P.functor.obj M.X) ≫
        (P.boundaryAlgebraIso (Representation.functions (G := G))).inv ▷ P.functor.obj M.X ≫
          Functor.LaxMonoidal.μ P.functor (regularAlgebra i) M.X ≫ P.functor.map γ[regularAlgebra i,M.X]
    simp only [Functor.map_comp, Category.comp_id,
      MonoidalCategory.whiskerLeft_id, Category.id_comp]
    rw [← Functor.LaxMonoidal.μ_natural_left_assoc,
      ← comp_whiskerRight_assoc, P.inverse_algebra_translation,
      comp_whiskerRight_assoc])

/-- The actual comparison isomorphism commutes naturally with all module
maps; the underlying ambient morphism is the identity. -/
def BoundaryAutoequivalence.moduleTranslationComparison (g : G) :
    moduleTranslation i g ⋙ P.moduleFunctor (Representation.functions (G := G)) ≅
      P.moduleFunctor (Representation.functions (G := G)) ⋙ moduleTranslation i g :=
  NatIso.ofComponents (fun M => by
    let f := P.moduleTranslationComparisonHom g M
    letI : IsIso f.hom := inferInstanceAs (IsIso (𝟙 (P.functor.obj M.X)))
    letI := internalModule_isIso_of_underlying f
    exact asIso f) (fun {M L} f => by
      apply Mod_.Hom.ext
      change P.functor.map f.hom ≫ 𝟙 _ = 𝟙 _ ≫ P.functor.map f.hom
      rw [Category.comp_id, Category.id_comp])

@[simp] theorem BoundaryAutoequivalence.moduleTranslationComparison_hom (g : G) (M : Modules i) :
    ((P.moduleTranslationComparison g).hom.app M).hom = 𝟙 (P.functor.obj M.X) := rfl

/-- The specified boundary gives a genuine coherent action intertwiner on
the actual module category used in de-equivariantization. -/
def BoundaryAutoequivalence.regularActionIntertwiner :
    (regularAction i).Intertwiner (regularAction i) where
  functor := P.moduleFunctor (Representation.functions (G := G))
  comparison := P.moduleTranslationComparison
  unit M := by
    apply Mod_.Hom.ext
    change 𝟙 (P.functor.obj M.X) ≫ 𝟙 _ = P.functor.map (𝟙 M.X)
    rw [Category.id_comp, P.functor.map_id]
  mul g h M := by
    apply Mod_.Hom.ext
    change P.functor.map (𝟙 M.X) ≫ 𝟙 _ = 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 (P.functor.obj M.X)
    rw [P.functor.map_id]
    simp only [Category.id_comp]

end Boundary
end Paper18.Category
