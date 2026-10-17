import Mathlib.CategoryTheory.Idempotents.Basic
import Mathlib.CategoryTheory.Retract

/-! # Essential images of fully faithful functors are closed under retracts -/
noncomputable section
open CategoryTheory
universe v u v' u'
namespace Paper18.Category
variable {C : Type u} [Category.{v} C] [IsIdempotentComplete C]
  {D : Type u'} [Category.{v'} D] (F : C ⥤ D) [F.Full] [F.Faithful]

theorem essImage_of_retract {X : C} {Y : D} (r : Retract Y (F.obj X)) :
    ∃ Z : C, Nonempty (F.obj Z ≅ Y) := by
  let p : X ⟶ X := F.preimage (r.r ≫ r.i)
  have hp : p ≫ p = p := by
    apply F.map_injective
    simp only [Functor.map_comp, p, F.map_preimage]
    simp [Category.assoc, r.retract]
  obtain ⟨Z, i, e, hie, hei⟩ := IsIdempotentComplete.idempotents_split X p hp
  refine ⟨Z, ⟨{
    hom := F.map i ≫ r.r
    inv := r.i ≫ F.map e
    hom_inv_id := ?_
    inv_hom_id := ?_ }⟩⟩
  · calc
      (F.map i ≫ r.r) ≫ (r.i ≫ F.map e) = F.map (i ≫ p ≫ e) := by
        simp only [Functor.map_comp, p, F.map_preimage, Category.assoc]
      _ = 𝟙 _ := by rw [← hei]; simp [← Category.assoc, hie]
  · calc
      (r.i ≫ F.map e) ≫ (F.map i ≫ r.r) = r.i ≫ F.map p ≫ r.r := by
        rw [Category.assoc, ← Functor.map_comp_assoc, hei]
      _ = 𝟙 _ := by simp [p, Category.assoc, r.retract]

theorem essSurj_of_retract_dominant
    (hF : ∀ Y : D, ∃ X : C, Nonempty (Retract Y (F.obj X))) : F.EssSurj where
  mem_essImage Y := by
    obtain ⟨X, ⟨r⟩⟩ := hF Y
    exact essImage_of_retract F r

end Paper18.Category
