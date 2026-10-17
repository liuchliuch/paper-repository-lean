import Paper18.Category.SemisimpleCoendBasic

/-! # Actual dinaturality from finite semisimple Hom resolutions -/
noncomputable section
open Classical Opposite
open CategoryTheory CategoryTheory.Limits
open scoped BigOperators
universe v u w v' u'
namespace Paper18.Category.FiniteSemisimpleSkeleton
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  {D : Type u'} [Category.{v'} D] [Preadditive D] [Linear ℂ D]
  (H : Cᵒᵖ ⥤ C ⥤ D) [H.Additive] [H.Linear ℂ]
  [∀ X, (H.obj X).Additive] [∀ X, (H.obj X).Linear ℂ]

/-- Sliding any morphism from a simple object across the extended family.
The proof uses Schur balancing and the actual identity resolution of `X`. -/
lemma coendExtend_sliding {Z : D}
    (q : ∀ i, (H.obj (op (S.simpleObject i))).obj (S.simpleObject i) ⟶ Z)
    {i : ι} {X : C} (u : S.simpleObject i ⟶ X) :
    (H.obj (op X)).map u ≫ S.coendExtend H q X =
      (H.map u.op).app (S.simpleObject i) ≫ q i := by
  have hres : (∑ a : Fin (S.length X),
      (u ≫ S.coendProjection X a) ≫ S.coendInclusion X a) = u := by
    simp only [Category.assoc, ← Preadditive.comp_sum, S.coendResolution, Category.comp_id]
  calc
    _ = ∑ a : Fin (S.length X),
        (H.map (S.coendInclusion X a).op).app (S.simpleObject i) ≫
          (H.obj (op (S.simpleObject (S.label X a)))).map
            (u ≫ S.coendProjection X a) ≫ q (S.label X a) := by
      unfold coendExtend
      simp only [Preadditive.comp_sum]
      apply Finset.sum_congr rfl
      intro a _
      rw [(H.map (S.coendInclusion X a).op).naturality_assoc u]
      rw [← Functor.map_comp_assoc]
    _ = ∑ a : Fin (S.length X),
        (H.map (S.coendInclusion X a).op).app (S.simpleObject i) ≫
          (H.map (u ≫ S.coendProjection X a).op).app (S.simpleObject i) ≫ q i := by
      apply Finset.sum_congr rfl
      intro a _
      rw [S.coend_simple_balance H q (u ≫ S.coendProjection X a)]
    _ = ∑ a : Fin (S.length X),
        (H.map ((u ≫ S.coendProjection X a) ≫ S.coendInclusion X a).op).app
          (S.simpleObject i) ≫ q i := by
      simp only [op_comp, H.map_comp, NatTrans.comp_app, Category.assoc]
    _ = (H.map ((∑ a : Fin (S.length X),
        (u ≫ S.coendProjection X a) ≫ S.coendInclusion X a)).op).app
          (S.simpleObject i) ≫ q i := by
      simp only [op_sum, H.map_sum, NatTrans.app_sum, Preadditive.sum_comp]
    _ = _ := by rw [hres]

/-- Extension agrees with the given simple-diagonal family. -/
lemma coendExtend_simple {Z : D}
    (q : ∀ i, (H.obj (op (S.simpleObject i))).obj (S.simpleObject i) ⟶ Z) (i : ι) :
    S.coendExtend H q (S.simpleObject i) = q i := by
  simpa using S.coendExtend_sliding H q (𝟙 (S.simpleObject i))

/-- The extended simple-diagonal family is actually dinatural for every
morphism of the original category. -/
lemma coendExtend_dinatural {Z : D}
    (q : ∀ i, (H.obj (op (S.simpleObject i))).obj (S.simpleObject i) ⟶ Z)
    {X Y : C} (f : X ⟶ Y) :
    (H.map f.op).app X ≫ S.coendExtend H q X =
      (H.obj (op Y)).map f ≫ S.coendExtend H q Y := by
  apply S.coend_map_hom_ext (H.obj (op Y)) X
  intro a
  rw [(H.map f.op).naturality_assoc (S.coendInclusion X a)]
  rw [S.coendExtend_sliding]
  rw [← Functor.map_comp_assoc, S.coendExtend_sliding]
  simp only [op_comp, H.map_comp, NatTrans.comp_app, Category.assoc]

end Paper18.Category.FiniteSemisimpleSkeleton
