import Paper18.Category.DeligneTensorProductMapWhisker

/-! # The actual comparison of inverse monoidal equivalences

All four tensor structures are the given ones. The proof composes the
actual monoidal unit, counit, and comparison; it does not replace the
inverse tensor structures by transported structures.
-/
noncomputable section
set_option synthInstance.maxSize 512
open CategoryTheory CategoryTheory.Category
universe v u v' u'
namespace Paper18.Category
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {D : Type u'} [Category.{v'} D] [MonoidalCategory D]
  (e f : C ≌ D)
  [e.functor.Monoidal] [e.inverse.Monoidal] [e.IsMonoidal]
  [f.functor.Monoidal] [f.inverse.Monoidal] [f.IsMonoidal]
  (r : e.functor ≅ f.functor) [NatTrans.IsMonoidal r.hom]

/-- The canonical actual inverse comparison preserves the given tensor
structures of both inverse functors. -/
theorem isoInverseOfIsoFunctor_isMonoidal :
    NatTrans.IsMonoidal (Iso.isoInverseOfIsoFunctor r).hom := by
  letI : NatTrans.IsMonoidal e.unitIso.hom :=
    inferInstanceAs (NatTrans.IsMonoidal e.unit)
  letI : NatTrans.IsMonoidal e.counitIso.hom :=
    inferInstanceAs (NatTrans.IsMonoidal e.counit)
  letI : NatTrans.IsMonoidal f.unitIso.hom :=
    inferInstanceAs (NatTrans.IsMonoidal f.unit)
  letI : NatTrans.IsMonoidal f.counitIso.hom :=
    inferInstanceAs (NatTrans.IsMonoidal f.counit)
  letI : NatTrans.IsMonoidal (Functor.isoWhiskerLeft e.inverse r).hom := by
    change NatTrans.IsMonoidal (Functor.whiskerLeft e.inverse r.hom)
    infer_instance
  dsimp only [Iso.isoInverseOfIsoFunctor, Iso.isoCompInverse, Iso.trans_hom,
    Iso.symm_hom, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom]
  infer_instance

end Paper18.Category
