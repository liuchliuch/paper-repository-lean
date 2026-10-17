import Paper18.Category.FixedBoundaryAlgebra

/-!
# The prescribed boundary comparison survives actual de-equivariantization

The induced module functor restricts to the identity on the image of the
boundary module category, with the comparison given by the original `α`
component at every module's underlying object.
-/
noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped MonObj Obj
universe v u v' u'
namespace Paper18.Category
variable {A : Type u} [Category.{v} A] [Preadditive A] [Linear ℂ A]
  [MonoidalCategory A] [BraidedCategory A]
  {N : Type u'} [Category.{v'} N] [Preadditive N] [Linear ℂ N]
  [MonoidalCategory N] [BraidedCategory N]
  {i : A ⥤ N} [i.Monoidal] (P : BoundaryAutoequivalence i) (R : A) [MonObj R]

/-- The specified `α` components are actual module intertwiners after
transport of the boundary algebra. -/
def BoundaryAutoequivalence.moduleBoundaryHom (M : Mod_ A R) :
    ((InternalModule.mapModules i) ⋙ P.moduleFunctor R).obj M ⟶
      (InternalModule.mapModules i).obj M :=
  Mod_.Hom.mk' (P.boundary.hom.app M.X) (by
    change ((P.boundaryAlgebraIso R).inv ▷ P.functor.obj (i.obj M.X) ≫
        Functor.LaxMonoidal.μ P.functor (i.obj R) (i.obj M.X) ≫
          P.functor.map (Functor.LaxMonoidal.μ i R M.X ≫ i.map γ[R,M.X])) ≫
            P.boundary.hom.app M.X =
      (i.obj R ◁ P.boundary.hom.app M.X) ≫
        Functor.LaxMonoidal.μ i R M.X ≫ i.map γ[R,M.X]
    rw [P.functor.map_comp]
    simp only [Category.assoc]
    slice_lhs 2 3 => rw [← Functor.LaxMonoidal.comp_μ]
    simp only [Category.assoc]
    change (P.boundaryAlgebraIso R).inv ▷ P.functor.obj (i.obj M.X) ≫
        Functor.LaxMonoidal.μ (i ⋙ P.functor) R M.X ≫
          (i ⋙ P.functor).map γ[R,M.X] ≫ P.boundary.hom.app M.X = _
    rw [P.boundary.hom.naturality, NatTrans.IsMonoidal.tensor_assoc]
    simp only [MonoidalCategory.tensorHom_def, Functor.comp_obj, Category.assoc]
    rw [← comp_whiskerRight_assoc, ← P.boundaryAlgebraIso_hom R, Iso.inv_hom_id,
      id_whiskerRight, Category.id_comp])

/-- The comparison is an actual module isomorphism. -/
def BoundaryAutoequivalence.moduleBoundaryIso (M : Mod_ A R) :
    ((InternalModule.mapModules i) ⋙ P.moduleFunctor R).obj M ≅
      (InternalModule.mapModules i).obj M := by
  let f := P.moduleBoundaryHom R M
  letI : IsIso f.hom := (P.boundary.app M.X).isIso_hom
  letI := internalModule_isIso_of_underlying f
  exact asIso f

/-- The actual neutral-boundary identification induced by the given `α`.
No choice of a replacement boundary identification is made. -/
def BoundaryAutoequivalence.moduleBoundaryNatIso :
    InternalModule.mapModules i ⋙ P.moduleFunctor R ≅ InternalModule.mapModules i :=
  NatIso.ofComponents (P.moduleBoundaryIso R) (fun {M L} f => by
    apply Mod_.Hom.ext
    exact P.boundary.hom.naturality f.hom)

omit [Preadditive A] [Linear ℂ A] [BraidedCategory A] in
@[simp] theorem BoundaryAutoequivalence.moduleBoundaryNatIso_hom
    (M : Mod_ A R) :
    ((P.moduleBoundaryNatIso R).hom.app M).hom = P.boundary.hom.app M.X := rfl

end Paper18.Category
