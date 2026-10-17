import Paper18.Category.FixedBoundaryNeutral
import Paper18.Category.FixedBoundaryModuleGrading

/-!
# Actual algebra translations retain the specified boundary comparison

Restriction along any actual boundary algebra endomorphism commutes with
transport of modules. Naturality of the original specified alpha gives the
corresponding comparison for its module functor. All comparison maps are
actual module maps with identity underlying morphism.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open scoped MonObj Obj
universe v u v' u'
namespace Paper18.Category
variable {A : Type u} [Category.{v} A] [Preadditive A] [Linear ℂ A]
  [MonoidalCategory A] [BraidedCategory A]
  {N : Type u'} [Category.{v'} N] [Preadditive N] [Linear ℂ N]
  [MonoidalCategory N] [BraidedCategory N]
  (i : A ⥤ N) [i.Monoidal] (R : A) [MonObj R]
  (t : R ⟶ R) [IsMonHom t]

/-- Restriction of scalars and actual module transport commute. -/
def InternalModule.mapModulesComapIso :
    Mod_.comap t ⋙ InternalModule.mapModules i ≅
      InternalModule.mapModules i ⋙ Mod_.comap (i.map t) :=
  NatIso.ofComponents (fun M => by
    let f : (InternalModule.mapModules i).obj ((Mod_.comap t).obj M) ⟶
        (Mod_.comap (i.map t)).obj ((InternalModule.mapModules i).obj M) :=
      Mod_.Hom.mk' (𝟙 (i.obj M.X)) (by
        change (Functor.LaxMonoidal.μ i R M.X ≫
            i.map ((t ▷ M.X) ≫ γ[R,M.X])) ≫ 𝟙 _ =
          (i.obj R ◁ 𝟙 _) ≫ (i.map t ▷ i.obj M.X) ≫
            Functor.LaxMonoidal.μ i R M.X ≫ i.map γ[R,M.X]
        simp only [Category.comp_id, whiskerLeft_id, Category.id_comp, i.map_comp]
        rw [Functor.LaxMonoidal.μ_natural_left_assoc])
    letI : IsIso f.hom := inferInstanceAs (IsIso (𝟙 (i.obj M.X)))
    letI := internalModule_isIso_of_underlying f
    exact asIso f) (by
      intro M L f
      apply Mod_.Hom.ext
      change i.map f.hom ≫ 𝟙 _ = 𝟙 _ ≫ i.map f.hom
      rw [Category.comp_id, Category.id_comp])

@[simp] theorem InternalModule.mapModulesComapIso_hom (M : Mod_ A R) :
    ((mapModulesComapIso i R t).hom.app M).hom = 𝟙 (i.obj M.X) := rfl

variable {i} (P : BoundaryAutoequivalence i)

/-- Naturality of the specified boundary identification is exactly the
algebra-translation compatibility of its inverse algebra component. -/
theorem BoundaryAutoequivalence.inverse_algebra_endomorphism :
    (P.boundaryAlgebraIso R).inv ≫ P.functor.map (i.map t) =
      i.map t ≫ (P.boundaryAlgebraIso R).inv := by
  have hn := P.boundary.inv.naturality t
  simpa only [BoundaryAutoequivalence.boundaryAlgebraIso_inv, Functor.comp_map] using hn.symm

/-- The actual fixed-boundary module functor commutes with every actual
boundary algebra translation. -/
def BoundaryAutoequivalence.moduleComapComparison :
    Mod_.comap (i.map t) ⋙ P.moduleFunctor R ≅
      P.moduleFunctor R ⋙ Mod_.comap (i.map t) :=
  NatIso.ofComponents (fun M => by
    let f : (P.moduleFunctor R).obj ((Mod_.comap (i.map t)).obj M) ⟶
        (Mod_.comap (i.map t)).obj ((P.moduleFunctor R).obj M) :=
      Mod_.Hom.mk' (𝟙 (P.functor.obj M.X)) (by
        change ((P.boundaryAlgebraIso R).inv ▷ P.functor.obj M.X ≫
            Functor.LaxMonoidal.μ P.functor (i.obj R) M.X ≫
              P.functor.map ((i.map t ▷ M.X) ≫ γ[i.obj R,M.X])) ≫ 𝟙 _ =
          (i.obj R ◁ 𝟙 _) ≫ (i.map t ▷ P.functor.obj M.X) ≫
            (P.boundaryAlgebraIso R).inv ▷ P.functor.obj M.X ≫
              Functor.LaxMonoidal.μ P.functor (i.obj R) M.X ≫ P.functor.map γ[i.obj R,M.X]
        simp only [P.functor.map_comp, Category.comp_id, whiskerLeft_id, Category.id_comp]
        rw [← Functor.LaxMonoidal.μ_natural_left_assoc,
          ← comp_whiskerRight_assoc, P.inverse_algebra_endomorphism R t,
          comp_whiskerRight_assoc])
    letI : IsIso f.hom := inferInstanceAs (IsIso (𝟙 (P.functor.obj M.X)))
    letI := internalModule_isIso_of_underlying f
    exact asIso f) (by
      intro M L f
      apply Mod_.Hom.ext
      change P.functor.map f.hom ≫ 𝟙 _ = 𝟙 _ ≫ P.functor.map f.hom
      rw [Category.comp_id, Category.id_comp])

@[simp] theorem BoundaryAutoequivalence.moduleComapComparison_hom (M : Mod_ N (i.obj R)) :
    ((P.moduleComapComparison R t).hom.app M).hom = 𝟙 (P.functor.obj M.X) := rfl

@[simp] theorem BoundaryAutoequivalence.moduleComapComparison_inv_hom (M : Mod_ N (i.obj R)) :
    ((P.moduleComapComparison R t).inv.app M).hom = 𝟙 (P.functor.obj M.X) := by
  have h := congrArg (fun f => f.hom) ((P.moduleComapComparison R t).inv_hom_id_app M)
  change ((P.moduleComapComparison R t).inv.app M).hom ≫ 𝟙 _ = 𝟙 _ at h
  simpa only [Category.comp_id] using h

/-- On actual boundary modules the prescribed comparison commutes with
actual translations; the underlying original alpha component is retained. -/
theorem BoundaryAutoequivalence.moduleBoundary_comap (M : Mod_ A R) :
    (P.moduleFunctor R).map ((InternalModule.mapModulesComapIso i R t).hom.app M) ≫
        (P.moduleComapComparison R t).hom.app ((InternalModule.mapModules i).obj M) ≫
          (Mod_.comap (i.map t)).map ((P.moduleBoundaryNatIso R).hom.app M) =
      (P.moduleBoundaryNatIso R).hom.app ((Mod_.comap t).obj M) ≫
        (InternalModule.mapModulesComapIso i R t).hom.app M := by
  apply Mod_.Hom.ext
  change P.functor.map (𝟙 _) ≫ 𝟙 _ ≫ P.boundary.hom.app M.X =
    P.boundary.hom.app M.X ≫ 𝟙 _
  rw [P.functor.map_id, Category.id_comp, Category.id_comp, Category.comp_id]

end Paper18.Category
