import Paper18.Category.FixedBoundaryInvariantFree
import Paper18.Category.FixedBoundaryFreeComparisonMonoidal
import Paper18.Category.FixedBoundaryAlgebraTranslation
import Paper18.Category.FixedBoundaryRestrictBoundary

/-! # The specified boundary gives genuinely invariant free comparisons -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open scoped MonObj Obj
universe v u v' u'
namespace Paper18.Category
open FixedBoundary
variable {G : Type} [Group G] [Fintype G]
  {A : Type u} [Category.{v} A] [Preadditive A] [Linear ℂ A]
  [MonoidalCategory A] [BraidedCategory A]
  {N : Type u'} [Category.{v'} N] [Preadditive N] [Linear ℂ N]
  [MonoidalCategory N] [BraidedCategory N]
  [MonoidalPreadditive N] [MonoidalLinear ℂ N]
  [RightRigidCategory N] [Limits.HasCoequalizers N]
  (F0 : FDRep ℂ G ⥤ A) [F0.Braided] [F0.Additive] [F0.Linear ℂ]
  {i : A ⥤ N} [i.Braided] [i.Additive] [i.Linear ℂ]
  (P : BoundaryAutoequivalence i)
local instance invariantBoundaryImageMonObj : MonObj (i.obj (regularAlgebra F0)) :=
  Functor.monObjObj (F := i) (regularAlgebra F0)
local instance invariantBoundaryImageCommMonObj : IsCommMonObj (i.obj (regularAlgebra F0)) :=
  Functor.isCommMonObj_obj

variable (β : P.moduleFunctor (regularAlgebra F0) ≅ 𝟭 (Mod_ N (i.obj (regularAlgebra F0))))

/-- The actual free comparison followed by the actual all-module
comparison is an ordinary natural isomorphism of staged free functors. -/
def BoundaryAutoequivalence.moduleFreeComparisonNatIso :
    P.functor ⋙ InternalModule.freeFunctor (A := i.obj (regularAlgebra F0)) ≅
      InternalModule.freeFunctor (A := i.obj (regularAlgebra F0)) :=
  P.moduleFreeNatIso (regularAlgebra F0) ≪≫
    Functor.isoWhiskerLeft (InternalModule.freeFunctor (A := i.obj (regularAlgebra F0))) β ≪≫
      Functor.rightUnitor (InternalModule.freeFunctor (A := i.obj (regularAlgebra F0)))

@[simp] theorem BoundaryAutoequivalence.moduleFreeComparisonNatIso_hom (X : N) :
    (P.moduleFreeComparisonNatIso F0 β).hom.app X =
      (P.moduleFreeIso (regularAlgebra F0) X).hom ≫
        β.hom.app (InternalModule.free (i.obj (regularAlgebra F0)) X) := by
  simp only [BoundaryAutoequivalence.moduleFreeComparisonNatIso, Iso.trans_hom,
    NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Functor.rightUnitor_hom_app, Category.comp_id]
  change ((P.moduleFreeIso (regularAlgebra F0) X).hom ≫
    β.hom.app (InternalModule.free (i.obj (regularAlgebra F0)) X) ≫ 𝟙 _) = _
  simp only [Category.comp_id]

instance BoundaryAutoequivalence.moduleFreeComparisonNatIsoMonoidal
    [NatTrans.IsMonoidal β.hom] :
    NatTrans.IsMonoidal (P.moduleFreeComparisonNatIso F0 β).hom := by
  let K := InternalModule.freeFunctor (A := i.obj (regularAlgebra F0))
  letI : NatTrans.IsMonoidal (Functor.whiskerLeft K β.hom) :=
    fixedBoundaryWhiskerLeftMonoidal K β.hom
  letI : NatTrans.IsMonoidal (P.moduleFreeNatIso (regularAlgebra F0)).hom :=
    P.moduleFreeNatIsoMonoidal (regularAlgebra F0)
  change NatTrans.IsMonoidal ((P.moduleFreeNatIso (regularAlgebra F0)).hom ≫
    Functor.whiskerLeft K β.hom ≫ (Functor.rightUnitor K).hom)
  infer_instance

/-- Naturality of the specified alpha makes the free comparison commute
with every actual regular translation. -/
theorem BoundaryAutoequivalence.moduleFreeIso_translation (g : G) (X : N) :
    (P.moduleFreeIso (regularAlgebra F0) X).hom.hom ≫
        P.functor.map (i.map (regularTranslation F0 g) ▷ X) =
      (i.map (regularTranslation F0 g) ▷ P.functor.obj X) ≫
        (P.moduleFreeIso (regularAlgebra F0) X).hom.hom := by
  rw [P.moduleFreeIso_hom]
  simp only [Category.assoc]
  rw [← Functor.LaxMonoidal.μ_natural_left,
    ← comp_whiskerRight_assoc, P.inverse_algebra_endomorphism (regularAlgebra F0) (regularTranslation F0 g),
    comp_whiskerRight_assoc]

/-- Actual translation compatibility of beta implies actual invariance
of the free comparison, including the specified algebra component. -/
theorem BoundaryAutoequivalence.moduleFreeComparison_invariant
    (hβ : ∀ (g : G) (M : Mod_ N (i.obj (regularAlgebra F0))),
      (β.hom.app ((Mod_.comap (i.map (regularTranslation F0 g))).obj M)).hom =
        (β.hom.app M).hom)
    (X : N) (g : G) :
    ((P.moduleFreeComparisonNatIso F0 β).app X).hom.hom ≫
        (i.map (regularTranslation F0 g) ▷ X) =
      (i.map (regularTranslation F0 g) ▷ P.functor.obj X) ≫
        ((P.moduleFreeComparisonNatIso F0 β).app X).hom.hom := by
  let e := i.mapIso (regularTranslationIso F0 g)
  letI : IsMonHom e.hom := by
    change IsMonHom (i.map (regularTranslation F0 g))
    infer_instance
  let q := InternalModule.comapFreeIso e X
  have hn := congrArg (fun f => f.hom) (β.hom.naturality q.hom)
  change P.functor.map (i.map (regularTranslation F0 g) ▷ X) ≫
      (β.hom.app ((Mod_.comap (i.map (regularTranslation F0 g))).obj
        (InternalModule.free (i.obj (regularAlgebra F0)) X))).hom =
    (β.hom.app (InternalModule.free (i.obj (regularAlgebra F0)) X)).hom ≫
      (i.map (regularTranslation F0 g) ▷ X) at hn
  rw [hβ] at hn
  change ((P.moduleFreeComparisonNatIso F0 β).hom.app X).hom ≫ _ =
    _ ≫ ((P.moduleFreeComparisonNatIso F0 β).hom.app X).hom
  rw [BoundaryAutoequivalence.moduleFreeComparisonNatIso_hom]
  change ((P.moduleFreeIso (regularAlgebra F0) X).hom.hom ≫
      (β.hom.app (InternalModule.free (i.obj (regularAlgebra F0)) X)).hom) ≫
      (i.map (regularTranslation F0 g) ▷ X) =
    (i.map (regularTranslation F0 g) ▷ P.functor.obj X) ≫
      (P.moduleFreeIso (regularAlgebra F0) X).hom.hom ≫
        (β.hom.app (InternalModule.free (i.obj (regularAlgebra F0)) X)).hom
  simp only [Category.assoc]
  rw [← hn, ← Category.assoc, P.moduleFreeIso_translation F0 g X]
  simp only [Category.assoc]

end Paper18.Category
