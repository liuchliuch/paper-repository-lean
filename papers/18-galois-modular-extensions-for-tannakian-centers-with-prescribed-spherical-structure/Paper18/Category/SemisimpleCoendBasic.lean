import Paper18.Category.SemisimpleSplitting
import Paper18.Category.SemisimpleCoendOpposite
import Mathlib.CategoryTheory.Limits.Shapes.End

/-! # Actual finite semisimple resolutions for coends -/
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

/-- Inclusion of an actual chosen simple summand. -/
def coendInclusion (X : C) (a : Fin (S.length X)) : S.simpleObject (S.label X a) ⟶ X :=
  biproduct.ι (fun b : Fin (S.length X) => S.simpleObject (S.label X b)) a ≫
    (S.decomposition X).inv

/-- Projection onto an actual chosen simple summand. -/
def coendProjection (X : C) (a : Fin (S.length X)) : X ⟶ S.simpleObject (S.label X a) :=
  (S.decomposition X).hom ≫
    biproduct.π (fun b : Fin (S.length X) => S.simpleObject (S.label X b)) a

omit [Linear ℂ C] [HasKernels C] [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)] in
lemma coendResolution (X : C) :
    (∑ a : Fin (S.length X), S.coendProjection X a ≫ S.coendInclusion X a) = 𝟙 X := by
  unfold coendProjection coendInclusion
  simp only [← Category.assoc, ← Preadditive.sum_comp]
  simp only [Category.assoc, ← Preadditive.comp_sum, biproduct.total]
  change (S.decomposition X).hom ≫ 𝟙 _ ≫ (S.decomposition X).inv = 𝟙 X
  simp

variable {D : Type u'} [Category.{v'} D] [Preadditive D] [Linear ℂ D]

omit [Linear ℂ C] [HasKernels C] [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)] [Linear ℂ D] in
lemma map_coendResolution (F : C ⥤ D) [F.Additive] (X : C) :
    (∑ a : Fin (S.length X), F.map (S.coendProjection X a) ≫
      F.map (S.coendInclusion X a)) = 𝟙 (F.obj X) := by
  simp only [← F.map_comp, ← F.map_sum, S.coendResolution, F.map_id]

omit [Linear ℂ C] [HasKernels C] [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)] [Linear ℂ D] in
/-- Maps from the image of an actual object under an additive functor are
determined on images of its actual simple summands. -/
lemma coend_map_hom_ext (F : C ⥤ D) [F.Additive] (X : C) {Z : D}
    (f g : F.obj X ⟶ Z)
    (h : ∀ a : Fin (S.length X), F.map (S.coendInclusion X a) ≫ f =
      F.map (S.coendInclusion X a) ≫ g) : f = g := by
  calc
    f = (∑ a : Fin (S.length X), F.map (S.coendProjection X a) ≫
        F.map (S.coendInclusion X a)) ≫ f := by rw [S.map_coendResolution, Category.id_comp]
    _ = (∑ a : Fin (S.length X), F.map (S.coendProjection X a) ≫
        F.map (S.coendInclusion X a)) ≫ g := by
      simp only [Preadditive.sum_comp, Category.assoc, h]
    _ = g := by rw [S.map_coendResolution, Category.id_comp]

variable (H : Cᵒᵖ ⥤ C ⥤ D) [H.Additive] [H.Linear ℂ]
  [∀ X, (H.obj X).Additive] [∀ X, (H.obj X).Linear ℂ]

/-- Schur's lemma supplies precisely the balancing equation for any family
on the simple diagonal of an actual complex-bilinear bifunctor. -/
lemma coend_simple_balance {Z : D}
    (q : ∀ i, (H.obj (op (S.simpleObject i))).obj (S.simpleObject i) ⟶ Z)
    {i j : ι} (f : S.simpleObject i ⟶ S.simpleObject j) :
    (H.map f.op).app (S.simpleObject i) ≫ q i =
      (H.obj (op (S.simpleObject j))).map f ≫ q j := by
  by_cases hij : i = j
  · subst j
    obtain ⟨c, rfl⟩ := CategoryTheory.endomorphism_simple_eq_smul_id ℂ f
    simp [complex_op_smul]
  · have hf : f = 0 := by
      by_contra hn
      letI := CategoryTheory.isIso_of_hom_simple hn
      exact hij (S.iso_injective i j ⟨asIso f⟩)
    simp [hf]

/-- Extension of a simple-diagonal family along actual simple summand
inclusions and projections. -/
def coendExtend {Z : D}
    (q : ∀ i, (H.obj (op (S.simpleObject i))).obj (S.simpleObject i) ⟶ Z)
    (X : C) : (H.obj (op X)).obj X ⟶ Z :=
  ∑ a : Fin (S.length X), (H.map (S.coendInclusion X a).op).app X ≫
    (H.obj (op (S.simpleObject (S.label X a)))).map (S.coendProjection X a) ≫
      q (S.label X a)

end Paper18.Category.FiniteSemisimpleSkeleton
