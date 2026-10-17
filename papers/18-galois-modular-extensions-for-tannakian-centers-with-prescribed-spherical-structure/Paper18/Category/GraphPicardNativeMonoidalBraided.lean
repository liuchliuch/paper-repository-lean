import Paper18.Category.GraphPicardNativeMonoidalBasic

/-! # Braiding is retained when both tensor orders reverse -/
noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory MonoidalOpposite
universe v u v' u'
namespace Paper18.Category.GraphPicard
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  {D : Type u'} [Category.{v'} D] [MonoidalCategory D] [BraidedCategory D]

/-- A genuine braided tensor functor remains braided when both tensor
orders are reversed. Its actual braidedness equation is read in reversed
object order. -/
instance simultaneousMopBraided (F : C ⥤ D) [F.Braided] :
    (simultaneousMop F).Braided where
  braided X Y := by
    apply Quiver.Hom.unmop_inj
    exact Functor.LaxBraided.braided (F := F) Y.unmop X.unmop

end Paper18.Category.GraphPicard
