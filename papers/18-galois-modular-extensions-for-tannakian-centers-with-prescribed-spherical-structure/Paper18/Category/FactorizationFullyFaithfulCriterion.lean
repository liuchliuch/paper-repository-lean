import Paper18.Category.FunctorImage
import Paper18.Category.SemisimpleSplitting
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # Deriving actual full faithfulness from simple Hom dimensions -/
noncomputable section
open Classical
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open scoped BigOperators
universe v u w v' u'
namespace Paper18.Category
namespace FiniteSemisimpleSkeleton
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {D : Type u'} [Category.{v'} D] [Preadditive D] [Linear ℂ D]
  [HasFiniteBiproducts D] [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  (F : C ⥤ D) [F.Additive] [F.Linear ℂ]
  (hdim : ∀ i j, Module.finrank ℂ (F.obj (S.simpleObject i) ⟶ F.obj (S.simpleObject j)) =
    if i = j then 1 else 0)
include hdim

lemma image_simple_id_ne_zero (i : ι) : (𝟙 (F.obj (S.simpleObject i))) ≠ 0 := by
  have hp : 0 < Module.finrank ℂ
      (F.obj (S.simpleObject i) ⟶ F.obj (S.simpleObject i)) := by rw [hdim]; simp
  obtain ⟨f, hf⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hp
  intro h
  exact hf (by rw [← Category.id_comp f, h, zero_comp])

lemma simple_map_injective (i j : ι) :
    Function.Injective (F.map : (S.simpleObject i ⟶ S.simpleObject j) → _) := by
  intro f g h
  by_contra hfg
  have hk : f - g ≠ 0 := sub_ne_zero.mpr hfg
  letI : IsIso (f - g) := CategoryTheory.isIso_of_hom_simple hk
  have hz : F.map (f - g) = 0 := by simp only [Functor.map_sub, h, sub_self]
  apply S.image_simple_id_ne_zero F hdim i
  rw [← IsIso.hom_inv_id (F.map (f - g))]
  simp only [hz, zero_comp]

lemma map_injective_of_simpleHomDimensions {X Y : C} :
    Function.Injective (F.map : (X ⟶ Y) → _) := by
  intro f g h
  apply S.hom_ext_simples
  intro i a
  apply S.hom_ext_to_simples
  intro j b
  apply S.simple_map_injective F hdim i j
  simp only [Functor.map_comp, assoc, h]

lemma finrank_hom_image_of_simpleHomDimensions (X Y : C) :
    Module.finrank ℂ (X ⟶ Y) = Module.finrank ℂ (F.obj X ⟶ F.obj Y) := by
  let p : Fin (S.length X) → C := fun a => S.simpleObject (S.label X a)
  let q : Fin (S.length Y) → C := fun a => S.simpleObject (S.label Y a)
  let eX : F.obj X ≅ ⨁ fun a => F.obj (p a) :=
    F.mapIso (S.decomposition X) ≪≫ F.mapBiproduct p
  let eY : F.obj Y ≅ ⨁ fun a => F.obj (q a) :=
    F.mapIso (S.decomposition Y) ≪≫ F.mapBiproduct q
  rw [finrank_hom_iso (S.decomposition X) (S.decomposition Y), finrank_hom_iso eX eY,
    finrank_biproduct_hom, finrank_biproduct_hom]
  simp_rw [finrank_hom_biproduct]
  change (∑ a : Fin (S.length X), ∑ b : Fin (S.length Y),
    Module.finrank ℂ (S.simpleObject (S.label X a) ⟶ S.simpleObject (S.label Y b))) = _
  dsimp only [p, q]
  simp_rw [S.finrank_simple_hom_simple, hdim]

/-- The actual map on each Hom space is bijective; semisimplicity of the
target is not needed. -/
lemma map_bijective_of_simpleHomDimensions (X Y : C) :
    Function.Bijective (F.map : (X ⟶ Y) → _) := by
  have hinj := S.map_injective_of_simpleHomDimensions F hdim (X := X) (Y := Y)
  have heq := S.finrank_hom_image_of_simpleHomDimensions F hdim X Y
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank heq
    (f := F.mapLinearMap ℂ)).mp hinj⟩

/-- A fully faithful functor is constructed from proved actual simple Hom
dimensions; no full-faithfulness or image-simplicity field is supplied. -/
def fullyFaithfulOfSimpleHomDimensions : F.FullyFaithful where
  preimage {X Y} h :=
    (LinearEquiv.ofBijective (F.mapLinearMap ℂ)
      (S.map_bijective_of_simpleHomDimensions F hdim X Y)).symm h
  map_preimage {X Y} h :=
    (LinearEquiv.ofBijective (F.mapLinearMap ℂ)
      (S.map_bijective_of_simpleHomDimensions F hdim X Y)).apply_symm_apply h
  preimage_map {X Y} h :=
    (LinearEquiv.ofBijective (F.mapLinearMap ℂ)
      (S.map_bijective_of_simpleHomDimensions F hdim X Y)).symm_apply_apply h

end FiniteSemisimpleSkeleton
end Paper18.Category
