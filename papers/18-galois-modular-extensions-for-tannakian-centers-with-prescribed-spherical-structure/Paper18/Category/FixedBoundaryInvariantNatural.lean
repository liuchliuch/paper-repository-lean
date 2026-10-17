import Paper18.Category.FixedBoundaryInvariantFree
import Paper18.Category.FixedBoundaryFullyFaithfulComparison

/-! # Genuine natural and monoidal comparison from regular invariants -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open scoped MonObj Obj
universe v u v' u'
namespace Paper18.Category.FixedBoundary
variable {G : Type} [Group G] [Fintype G]
  {A : Type u} [Category.{v} A] [Preadditive A] [Linear ℂ A]
  [MonoidalCategory A] [BraidedCategory A]
  {N : Type u'} [Category.{v'} N] [Preadditive N] [Linear ℂ N]
  [MonoidalCategory N] [BraidedCategory N]
  [MonoidalPreadditive N] [MonoidalLinear ℂ N]
  [RightRigidCategory N] [Limits.HasCoequalizers N]
  (F0 : FDRep ℂ G ⥤ A) [F0.Braided] [F0.Additive] [F0.Linear ℂ]
  (i : A ⥤ N) [i.Braided] [i.Additive] [i.Linear ℂ]
local instance invariantNaturalImageMonObj : MonObj (i.obj (regularAlgebra F0)) :=
  Functor.monObjObj (F := i) (regularAlgebra F0)
local instance invariantNaturalImageCommMonObj : IsCommMonObj (i.obj (regularAlgebra F0)) :=
  Functor.isCommMonObj_obj

variable {F H : N ⥤ N}
  (e : F ⋙ InternalModule.freeFunctor (A := i.obj (regularAlgebra F0)) ≅
    H ⋙ InternalModule.freeFunctor (A := i.obj (regularAlgebra F0)))
  (he : ∀ (X : N) (g : G), (e.app X).hom.hom ≫
      (i.map (regularTranslation F0 g) ▷ H.obj X) =
    (i.map (regularTranslation F0 g) ▷ F.obj X) ≫ (e.app X).hom.hom)

/-- The actual invariant components form a genuine natural isomorphism;
its naturality is reflected by the faithful actual staged free functor. -/
def stagedInvariantNatIso : F ≅ H :=
  NatIso.ofComponents (fun X => stagedInvariantIso F0 i (e.app X) (he X)) (by
    intro X Y f
    letI := stagedRegularFreeFaithful F0 i
    apply (InternalModule.freeFunctor (A := i.obj (regularAlgebra F0))).map_injective
    simp only [CategoryTheory.Functor.map_comp]
    change InternalModule.freeMap (F.map f) ≫
      InternalModule.freeMap (stagedInvariantIso F0 i (e.app Y) (he Y)).hom =
      InternalModule.freeMap (stagedInvariantIso F0 i (e.app X) (he X)).hom ≫
        InternalModule.freeMap (H.map f)
    rw [stagedInvariantIso_map_hom, stagedInvariantIso_map_hom]
    exact e.hom.naturality f)

@[simp] theorem stagedInvariantNatIso_map_hom (X : N) :
    InternalModule.freeMap (A := i.obj (regularAlgebra F0))
      ((stagedInvariantNatIso F0 i e he).hom.app X) = e.hom.app X :=
  stagedInvariantIso_map_hom F0 i (e.app X) (he X)

instance stagedInvariantNatIsoMonoidal [F.Monoidal] [H.Monoidal]
    [NatTrans.IsMonoidal e.hom] :
    NatTrans.IsMonoidal (stagedInvariantNatIso F0 i e he).hom := by
  letI := stagedRegularFreeFaithful F0 i
  apply natTransMonoidal_of_map (InternalModule.freeFunctor (A := i.obj (regularAlgebra F0))) e
  intro X
  exact stagedInvariantNatIso_map_hom F0 i e he X

end Paper18.Category.FixedBoundary
