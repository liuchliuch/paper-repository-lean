import Mathlib.CategoryTheory.Monoidal.NaturalTransformation

/-! # Monoidality of actual whiskered natural isomorphisms -/
noncomputable section
open CategoryTheory CategoryTheory.Category
universe v u v' u' v'' u''
namespace Paper18.Category.DeligneTensorProductMap
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {D : Type u'} [Category.{v'} D] [MonoidalCategory D]
  {E : Type u''} [Category.{v''} E] [MonoidalCategory E]

instance whiskerLeft_monoidal (F : C ⥤ D) [F.Monoidal]
    {G H : D ⥤ E} [G.Monoidal] [H.Monoidal]
    (τ : G ⟶ H) [NatTrans.IsMonoidal τ] :
    NatTrans.IsMonoidal (Functor.whiskerLeft F τ) := by
  have hm : NatTrans.IsMonoidal ((𝟙 F) ◫ τ) := inferInstance
  convert hm using 1
  ext X
  simp

instance whiskerRight_monoidal {F G : C ⥤ D} [F.Monoidal] [G.Monoidal]
    (τ : F ⟶ G) [NatTrans.IsMonoidal τ] (H : D ⥤ E) [H.Monoidal] :
    NatTrans.IsMonoidal (Functor.whiskerRight τ H) := by
  have hm : NatTrans.IsMonoidal (τ ◫ (𝟙 H)) := inferInstance
  convert hm using 1
  ext X
  simp

end Paper18.Category.DeligneTensorProductMap
