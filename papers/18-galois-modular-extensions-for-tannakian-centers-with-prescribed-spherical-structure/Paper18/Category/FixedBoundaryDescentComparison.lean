import Paper18.Category.FixedBoundaryFreeComparison
import Paper18.Category.FixedBoundaryDescentMonoidal
import Paper18.Category.FixedBoundaryEquivariantMonoidal

/-! # The actual free comparison in regular descent

The specified algebra component intertwines regular translations. Hence
the free-module comparison is an actual equivariant isomorphism. An
actual translation-compatible module comparison then gives an ordinary
comparison after the fully faithful regular descent functor.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open scoped MonObj Obj
universe v u
namespace Paper18.Category
open FixedBoundary
variable {G : Type} [Group G] [Fintype G]
  {N : Type u} [Category.{v} N] [Preadditive N] [Linear ℂ N]
  [MonoidalCategory N] [BraidedCategory N]
  [MonoidalPreadditive N] [MonoidalLinear ℂ N]
  [RightRigidCategory N] [Limits.HasCoequalizers N]
  {i : FDRep ℂ G ⥤ N} [i.Braided] [i.Additive] [i.Linear ℂ]
  (P : BoundaryAutoequivalence i)

@[simp] theorem BoundaryAutoequivalence.moduleTranslationComparison_inv_hom (g : G) (M : Modules i) :
    ((P.moduleTranslationComparison g).inv.app M).hom = 𝟙 (P.functor.obj M.X) := by
  have h := congrArg (fun f => f.hom) ((P.moduleTranslationComparison g).hom_inv_id_app M)
  change 𝟙 _ ≫ ((P.moduleTranslationComparison g).inv.app M).hom = 𝟙 _ at h
  simpa only [Category.id_comp] using h

/-- The actual free comparison respects the regular equivariant structures. -/
def BoundaryAutoequivalence.descentFreeIso (X : N) :
    (descentComparison i).obj (P.functor.obj X) ≅
      P.regularActionIntertwiner.equivariantFunctor.obj ((descentComparison i).obj X) :=
  WeakAction.Equivariant.mkIso (regularAction i)
    (P.moduleFreeIso (Representation.functions (G := G)) X) (by
      intro g
      apply Mod_.Hom.ext
      change (P.moduleFreeIso (Representation.functions (G := G)) X).hom.hom ≫
          ((P.moduleTranslationComparison g).inv.app ((regularFree i).obj X)).hom ≫
            P.functor.map (regularTranslation i g ▷ X) = _
      rw [P.moduleTranslationComparison_inv_hom]
      change ((P.boundaryAlgebraIso _).inv ▷ P.functor.obj X ≫
          Functor.LaxMonoidal.μ P.functor (regularAlgebra i) X) ≫
          𝟙 _ ≫ P.functor.map (regularTranslation i g ▷ X) =
        (regularTranslation i g ▷ P.functor.obj X) ≫
          (P.boundaryAlgebraIso _).inv ▷ P.functor.obj X ≫
          Functor.LaxMonoidal.μ P.functor (regularAlgebra i) X
      simp only [Category.comp_id, Category.id_comp, Category.assoc]
      rw [← Functor.LaxMonoidal.μ_natural_left,
        ← comp_whiskerRight_assoc, P.inverse_algebra_translation,
        comp_whiskerRight_assoc])

/-- Naturality retains the actual free comparison, now including the
regular equivariant structure. -/
def BoundaryAutoequivalence.descentFreeNatIso :
    P.functor ⋙ descentComparison i ≅
      descentComparison i ⋙ P.regularActionIntertwiner.equivariantFunctor :=
  NatIso.ofComponents P.descentFreeIso (by
    intro X Y f
    apply WeakAction.Equivariant.Hom.ext
    exact (P.moduleFreeNatIso (Representation.functions (G := G))).hom.naturality f)

variable (β : P.moduleFunctor (Representation.functions (G := G)) ≅ 𝟭 (Modules i))
  (hβ : ∀ g M, (P.moduleTranslationComparison g).hom.app M ≫
    (moduleTranslation i g).map (β.hom.app M) = β.hom.app ((moduleTranslation i g).obj M))

/-- An actual comparison respecting translations is an isomorphism of the
actual transported equivariant objects. -/
def BoundaryAutoequivalence.moduleEquivariantIso
    (X : (regularAction i).Equivariant) :
    P.regularActionIntertwiner.equivariantFunctor.obj X ≅ X :=
  WeakAction.Equivariant.mkIso (regularAction i) (β.app X.obj) (by
    intro g
    change (moduleTranslation i g).map (β.hom.app X.obj) ≫ (X.structureIso g).hom =
      ((P.moduleTranslationComparison g).inv.app X.obj ≫
        (P.moduleFunctor _).map (X.structureIso g).hom) ≫ β.hom.app X.obj
    apply (cancel_epi ((P.moduleTranslationComparison g).hom.app X.obj)).mp
    simp only [← Category.assoc]
    rw [hβ]
    simp only [Iso.hom_inv_id_app, Category.id_comp, Category.assoc]
    exact (β.hom.naturality (X.structureIso g).hom).symm)

/-- Actual translation-compatible module comparisons descend to natural
isomorphisms of the genuine equivariantization. -/
def BoundaryAutoequivalence.moduleEquivariantNatIso :
    P.regularActionIntertwiner.equivariantFunctor ≅ 𝟭 (regularAction i).Equivariant :=
  NatIso.ofComponents (P.moduleEquivariantIso β hβ) (by
    intro X Y f
    apply WeakAction.Equivariant.Hom.ext
    exact β.hom.naturality f.hom)

/-- The specified free comparison followed by the actual equivariant
module comparison gives a comparison after genuine regular descent. -/
def BoundaryAutoequivalence.descentComparisonNatIso :
    P.functor ⋙ descentComparison i ≅ descentComparison i :=
  P.descentFreeNatIso ≪≫
    Functor.isoWhiskerLeft (descentComparison i) (P.moduleEquivariantNatIso β hβ) ≪≫
      Functor.rightUnitor (descentComparison i)

@[simp] theorem BoundaryAutoequivalence.descentComparisonNatIso_hom (X : N) :
    ((P.descentComparisonNatIso β hβ).hom.app X).hom =
      (P.moduleFreeIso (Representation.functions (G := G)) X).hom ≫
        β.hom.app ((regularFree i).obj X) := by
  simp only [descentComparisonNatIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Functor.rightUnitor_hom_app,
    Category.comp_id]
  change (P.moduleFreeIso (Representation.functions (G := G)) X).hom ≫
      β.hom.app ((regularFree i).obj X) ≫ 𝟙 _ = _
  simp only [Category.comp_id]

end Paper18.Category
