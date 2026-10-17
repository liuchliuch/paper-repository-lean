import Paper18.Category.GraphPicardNativeMonoidal
import Paper18.Category.DeligneTensorProductMapWhisker

/-! # Actual inverse comparisons for simultaneous monoidal opposites -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open MonoidalOpposite
universe v u v' u'
namespace Paper18.Category.GraphPicard
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {D : Type u'} [Category.{v'} D] [MonoidalCategory D]
  (e : Cᴹᵒᵖ ≌ Dᴹᵒᵖ) (d : C ≌ D)
  [e.functor.Monoidal] [e.inverse.Monoidal] [e.IsMonoidal]
  [d.functor.Monoidal] [d.inverse.Monoidal] [d.IsMonoidal]
  (i : e.functor ≅ simultaneousMop d.functor) [NatTrans.IsMonoidal i.hom]

/-- The actual central counit and actual forward comparison identify
the composite with the identity, including the genuine tensor structure. -/
def inverseMopComparisonCounit : simultaneousMop d.inverse ⋙ e.functor ≅ 𝟭 Dᴹᵒᵖ :=
  Functor.isoWhiskerLeft (simultaneousMop d.inverse) i ≪≫
    (simultaneousMopCompIso d.inverse d.functor).symm ≪≫
    simultaneousMopNatIso d.counitIso ≪≫ simultaneousMopIdIso

instance inverseMopComparisonCounitMonoidal :
    NatTrans.IsMonoidal (inverseMopComparisonCounit e d i).hom := by
  dsimp only [inverseMopComparisonCounit, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerLeft_hom]
  infer_instance

/-- Inverting an actual forward comparison uses the actual equivalence
unit and counit, rather than identifying independently chosen inverses. -/
def inverseMopComparison : e.inverse ≅ simultaneousMop d.inverse :=
  (Iso.isoCompInverse (H := e) (inverseMopComparisonCounit e d i) ≪≫
    Functor.leftUnitor e.inverse).symm

instance inverseMopComparisonMonoidal :
    NatTrans.IsMonoidal (inverseMopComparison e d i).hom := by
  haveI : NatTrans.IsMonoidal
      (Iso.isoCompInverse (H := e) (inverseMopComparisonCounit e d i) ≪≫
        Functor.leftUnitor e.inverse).hom := by
    dsimp only [Iso.isoCompInverse, Iso.compInverseIso, Iso.trans_hom, Iso.symm_hom,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom]
    infer_instance
  exact inferInstanceAs (NatTrans.IsMonoidal
    (Iso.isoCompInverse (H := e) (inverseMopComparisonCounit e d i) ≪≫
      Functor.leftUnitor e.inverse).inv)

end Paper18.Category.GraphPicard
