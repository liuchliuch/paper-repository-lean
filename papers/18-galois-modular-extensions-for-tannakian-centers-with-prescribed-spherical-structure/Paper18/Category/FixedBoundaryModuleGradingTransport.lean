import Paper18.Category.FixedBoundaryFunctorGrading
import Paper18.Category.FixedBoundaryModuleGrading
import Paper18.Category.FixedBoundaryModuleFunctorMonoidal
import Paper18.Category.FixedBoundaryRestriction

/-!
# The specified boundary functor preserves the actual module grading

The original braided functor fixes the invertible grading object through
its given object isomorphism. This proves compatibility with the actual
descended module character and hence preserves and reflects its actual
homogeneous components, even though the category of all modules need not
be braided.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped MonObj Obj
universe v u v' u'
namespace Paper18.Category
variable {A : Type u} [Category.{v} A] [Preadditive A] [Linear ℂ A]
  [MonoidalCategory A] [BraidedCategory A]
  {N : Type u'} [Category.{v'} N] [Preadditive N] [Linear ℂ N]
  [MonoidalCategory N] [BraidedCategory N] [MonoidalPreadditive N] [MonoidalLinear ℂ N]
  {i : A ⥤ N} [i.Monoidal] (P : BoundaryAutoequivalence i)
  (R : A) [MonObj R] {T : N} (B : TensorInverse T)
  (hR : Centralizes T (i.obj R)) (e : P.functor.obj T ≅ T)

instance BoundaryAutoequivalence.moduleFunctorFaithful : (P.moduleFunctor R).Faithful := by
  dsimp only [BoundaryAutoequivalence.moduleFunctor]
  infer_instance

instance BoundaryAutoequivalence.moduleFunctorAdditive : (P.moduleFunctor R).Additive where
  map_add := by
    intros
    apply Mod_.Hom.ext
    exact P.functor.map_add

instance BoundaryAutoequivalence.moduleFunctorLinear : (P.moduleFunctor R).Linear ℂ where
  map_smul f r := by
    apply Mod_.Hom.ext
    exact P.functor.map_smul r f.hom

include e in
/-- Actual compatibility with the descended monodromy character. -/
theorem BoundaryAutoequivalence.moduleFunctor_map_monodromy
    (M : Mod_ N (i.obj R)) :
    (P.moduleFunctor R).map ((B.moduleMonodromyCharacter (i.obj R) hR).hom.app M) =
      (B.moduleMonodromyCharacter (i.obj R) hR).hom.app ((P.moduleFunctor R).obj M) := by
  apply Mod_.Hom.ext
  exact B.map_monodromyCharacter P.functor B e M.X

include e in
/-- The induced functor preserves actual degree on all internal modules. -/
theorem BoundaryAutoequivalence.moduleFunctor_homogeneous_map {d : ZMod 2}
    {M : Mod_ N (i.obj R)}
    (hM : FixedBoundary.Homogeneous (B.moduleMonodromyCharacter (i.obj R) hR) d M) :
    FixedBoundary.Homogeneous (B.moduleMonodromyCharacter (i.obj R) hR) d
      ((P.moduleFunctor R).obj M) := by
  unfold FixedBoundary.Homogeneous at hM ⊢
  rw [← P.moduleFunctor_map_monodromy R B hR e, hM, Functor.map_smul]
  exact congrArg (fun f => FixedBoundary.paritySign d • f) ((P.moduleFunctor R).map_id M)

include e in
/-- Actual degree reflection follows from the already proved fully
faithful module functor, with no braided structure on all modules. -/
theorem BoundaryAutoequivalence.moduleFunctor_homogeneous_map_iff (d : ZMod 2)
    (M : Mod_ N (i.obj R)) :
    FixedBoundary.Homogeneous (B.moduleMonodromyCharacter (i.obj R) hR) d
      ((P.moduleFunctor R).obj M) ↔
        FixedBoundary.Homogeneous (B.moduleMonodromyCharacter (i.obj R) hR) d M := by
  constructor
  · intro h
    unfold FixedBoundary.Homogeneous at h ⊢
    apply (P.moduleFunctor R).map_injective
    rw [Functor.map_smul]
    calc
      _ = (B.moduleMonodromyCharacter (i.obj R) hR).hom.app ((P.moduleFunctor R).obj M) :=
        P.moduleFunctor_map_monodromy R B hR e M
      _ = FixedBoundary.paritySign d • 𝟙 _ := h
      _ = _ := (congrArg (fun f => FixedBoundary.paritySign d • f)
        ((P.moduleFunctor R).map_id M)).symm
  · exact P.moduleFunctor_homogeneous_map R B hR e

end Paper18.Category
