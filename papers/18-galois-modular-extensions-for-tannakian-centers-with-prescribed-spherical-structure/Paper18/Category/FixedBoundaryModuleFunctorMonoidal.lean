import Paper18.Category.FixedBoundaryModuleMonoidal
import Paper18.Category.FixedBoundaryModuleRestriction
import Paper18.Category.FixedBoundaryAlgebra

/-! # The actual strong tensor functor attached to a specified boundary pair -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped MonObj Obj
universe v u v' u'
namespace Paper18.Category
open RelativeTensor
variable {A : Type u} [Category.{v} A] [Preadditive A] [Linear ℂ A]
  [MonoidalCategory A] [BraidedCategory A]
  {N : Type u'} [Category.{v'} N] [Preadditive N] [Linear ℂ N]
  [MonoidalCategory N] [BraidedCategory N]
  [RightRigidCategory N] [HasCoequalizers N]
  {i : A ⥤ N} [i.Braided] (P : BoundaryAutoequivalence i) (R : A)
  [MonObj R] [IsCommMonObj R]

instance boundaryImageAlgebra_comm : IsCommMonObj (i.obj R) := Functor.isCommMonObj_obj

/-- The specified α_R is used in the strong tensor structure on the actual
module functor, rather than merely in its underlying object map. -/
instance BoundaryAutoequivalence.moduleFunctorMonoidal : (P.moduleFunctor R).Monoidal := by
  let e := P.boundaryAlgebraIso R
  letI : IsMonHom e.symm.hom := inferInstanceAs (IsMonHom e.inv)
  exact inferInstanceAs
    ((InternalModule.mapModules P.functor ⋙ InternalModule.algebraComap e.symm).Monoidal)

/-- Its actual tensor comparison is determined before the balancing
quotient by the original ambient tensorator of F. -/
@[reassoc] theorem BoundaryAutoequivalence.π_moduleFunctor_μ (M N : Mod_ N (i.obj R)) :
    π ((P.moduleFunctor R).obj M) ((P.moduleFunctor R).obj N) ≫
      (Functor.LaxMonoidal.μ (P.moduleFunctor R) M N).hom =
      Functor.LaxMonoidal.μ P.functor M.X N.X ≫ P.functor.map (π M N) := by
  let e := P.boundaryAlgebraIso R
  letI : IsMonHom e.symm.hom := inferInstanceAs (IsMonHom e.inv)
  change π ((InternalModule.algebraComap e.symm).obj (InternalModule.mapModuleObj P.functor M))
      ((InternalModule.algebraComap e.symm).obj (InternalModule.mapModuleObj P.functor N)) ≫
      (InternalModule.algebraComapTensorHom e.symm
        (InternalModule.mapModuleObj P.functor M) (InternalModule.mapModuleObj P.functor N)).hom ≫
      (InternalModule.mapModulesTensorHom P.functor M N).hom = _
  rw [InternalModule.π_algebraComapTensorHom_assoc, InternalModule.π_mapModulesTensorHom]

@[simp] theorem BoundaryAutoequivalence.moduleFunctor_ε_hom :
    (Functor.LaxMonoidal.ε (P.moduleFunctor R)).hom = (P.boundaryAlgebraIso R).inv := by
  let e := P.boundaryAlgebraIso R
  letI : IsMonHom e.symm.hom := inferInstanceAs (IsMonHom e.inv)
  change e.inv ≫ 𝟙 _ = e.inv
  exact Category.comp_id _

end Paper18.Category
