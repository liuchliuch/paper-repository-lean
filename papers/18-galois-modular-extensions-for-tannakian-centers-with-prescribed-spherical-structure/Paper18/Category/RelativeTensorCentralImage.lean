import Paper18.Category.FunctorRetract
import Paper18.Category.NondegenerateBasic
import Paper18.Category.FusionSubcategoryRigid

/-! # Actual fusion-image closure and finite sums of tensor units -/
noncomputable section
open Classical CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators
universe v u v' u'
namespace Paper18.Category.RelativeTensor
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

section UnitSums
variable [Preadditive C] [HasFiniteBiproducts C] [MonoidalCategory C]
  [Preadditive D] [HasFiniteBiproducts D] [MonoidalCategory D]
  (F : C ⥤ D) [F.Additive] [F.Monoidal]

/-- An actual additive tensor functor carries actual finite sums of units
to actual finite sums of units. -/
theorem unitSum_map {X : C} (hX : IsUnitSum X) : IsUnitSum (F.obj X) := by
  obtain ⟨n, ⟨e⟩⟩ := hX
  refine ⟨n, ⟨F.mapIso e ≪≫ F.mapBiproduct (fun _ : Fin n => 𝟙_ C) ≪≫ ?_⟩⟩
  exact biproduct.mapIso (fun _ => (Functor.Monoidal.εIso F).symm)

/-- An actual unit decomposition of an underlying object lifts to every
full tensor subcategory containing it. -/
theorem unitSum_fullSubcategory (P : ObjectProperty D) [P.IsMonoidal]
    [IsAdditiveFullProperty P] (X : P.FullSubcategory) (hX : IsUnitSum X.obj) :
    IsUnitSum X := by
  obtain ⟨n, ⟨e⟩⟩ := hX
  refine ⟨n, ⟨P.isoMk (e ≪≫ ?_)⟩⟩
  exact (P.ι.mapBiproduct (fun _ : Fin n => 𝟙_ P.FullSubcategory)).symm

/-- A fully faithful actual additive tensor functor reflects actual finite
sums of tensor units by lifting the complete decomposition isomorphism. -/
theorem unitSum_of_map [F.Full] [F.Faithful] {X : C}
    (hX : IsUnitSum (F.obj X)) : IsUnitSum X := by
  obtain ⟨n, ⟨e⟩⟩ := hX
  let d : F.obj (⨁ fun _ : Fin n => 𝟙_ C) ≅ ⨁ fun _ : Fin n => 𝟙_ D :=
    F.mapBiproduct (fun _ : Fin n => 𝟙_ C) ≪≫
      biproduct.mapIso (fun _ => (Functor.Monoidal.εIso F).symm)
  exact ⟨n, ⟨F.preimageIso (e ≪≫ d.symm)⟩⟩
end UnitSums

section Image
variable [Preadditive C] [HasFiniteBiproducts C] [HasKernels C]
  [Preadditive D] [HasFiniteBiproducts D]
  (F : C ⥤ D) [F.Full] [F.Faithful] [F.Additive]

/-- Actual essential images of fully faithful additive functors from an
idempotent complete source are closed under summands and finite biproducts. -/
instance essImage_isAdditive : IsAdditiveFullProperty F.essImage where
  of_retract R hY := by
    letI : IsIdempotentComplete C :=
      (Idempotents.isIdempotentComplete_iff_idempotents_have_kernels (C := C)).mpr
        (fun X p _ => inferInstance)
    exact essImage_of_retract F (R.trans (Retract.ofIso hY.getIso.symm))
  biproduct f hf := by
    let g := fun j => (hf j).witness
    refine ⟨⨁ g, ⟨F.mapBiproduct g ≪≫ ?_⟩⟩
    exact biproduct.mapIso (fun j => (hf j).getIso)
end Image

section TensorImage
variable [MonoidalCategory C] [MonoidalCategory D] (F : C ⥤ D) [F.Monoidal]

/-- The essential image of an actual strong tensor functor is an actual
full tensor subcategory. -/
instance essImage_isMonoidal : F.essImage.IsMonoidal where
  prop_unit := ⟨𝟙_ C, ⟨(Functor.Monoidal.εIso F).symm⟩⟩
  prop_tensor _ _ hX hY :=
    ⟨hX.witness ⊗ hY.witness,
      ⟨(Functor.Monoidal.μIso F hX.witness hY.witness).symm ≪≫
        tensorIso hX.getIso hY.getIso⟩⟩
end TensorImage

section Braided
variable [Preadditive C] [HasFiniteBiproducts C] [MonoidalCategory C]
  [MonoidalPreadditive C] [BraidedCategory C]
  [Preadditive D] [HasFiniteBiproducts D] [MonoidalCategory D]
  [MonoidalPreadditive D] [BraidedCategory D]
  (F : C ⥤ D) [F.Additive] [F.Braided] [F.Faithful]

omit [MonoidalPreadditive C] [MonoidalPreadditive D] in
/-- The intersection of an actual nondegenerate braided image with its
actual centralizer contains only actual finite sums of tensor units. -/
theorem unitSum_of_image_and_centralizer (hC : IsNondegenerate (C := C))
    {X : D} (hX : F.essImage X) (hcentral : X ∈ centralizer (Set.range F.obj)) :
    IsUnitSum X := by
  have hx : hX.witness ∈ mugerCenter (C := C) := by
    intro Y _
    apply (centralizes_map_iff F hX.witness Y).mp
    exact (hcentral (F.obj Y) ⟨Y, rfl⟩).of_iso_left hX.getIso
  exact (unitSum_map F (hC _ hx)).of_iso hX.getIso.symm

omit [Preadditive C] [HasFiniteBiproducts C] [MonoidalCategory C]
  [MonoidalPreadditive C] [BraidedCategory C] [Preadditive D] [HasFiniteBiproducts D]
  [MonoidalPreadditive D] [F.Additive] [F.Braided] [F.Faithful] in
/-- Taking an essential image does not change the actual centralizer of
the object image. -/
theorem centralizer_essImage : centralizer (F.essImage : Set D) =
    centralizer (Set.range F.obj) := by
  ext X
  constructor
  · intro h Y hY
    obtain ⟨Y, rfl⟩ := hY
    exact h (F.obj Y) (F.obj_mem_essImage Y)
  · intro h Y hY
    exact (centralizes_iso_right hY.getIso).mp
      (h (F.obj hY.witness) ⟨hY.witness, rfl⟩)

omit [MonoidalPreadditive C] [MonoidalPreadditive D] in
/-- Nondegeneracy descends along an actual braided equivalence by mapping
transparency and lifting the resulting actual unit decomposition. -/
theorem nondegenerate_of_braided_equivalence [F.Full] [F.EssSurj]
    (hD : IsNondegenerate (C := D)) : IsNondegenerate (C := C) := by
  intro X hX
  apply unitSum_of_map F
  apply hD
  intro Y _
  have h : Centralizes (F.obj X) (F.obj (F.objPreimage Y)) :=
    (hX (F.objPreimage Y) (Set.mem_univ _)).map F
  exact (centralizes_iso_right (F.objObjPreimageIso Y)).mp h
end Braided

section Reverse
variable [MonoidalCategory C] [BraidedCategory C]

/-- Reversing the braiding preserves the actual centralization relation. -/
theorem centralizes_reverse_iff (X Y : C) :
    @Centralizes C _ _ (reverseBraiding C) X Y ↔ Centralizes X Y := by
  rw [@centralizes_iff_braiding_inv C _ _ (reverseBraiding C) X Y,
    centralizes_iff_braiding_inv]
  change (β_ X Y).inv = (β_ Y X).hom ↔ (β_ Y X).hom = (β_ X Y).inv
  exact eq_comm

variable [Preadditive C] [HasFiniteBiproducts C] [MonoidalPreadditive C]

omit [MonoidalPreadditive C] in
/-- Reversing the actual braiding preserves actual Müger nondegeneracy. -/
theorem nondegenerate_reverse_iff :
    @IsNondegenerate C _ _ (reverseBraiding C) _ _ ↔ IsNondegenerate (C := C) := by
  constructor
  · intro h X hX
    apply h X
    intro Y _
    exact (centralizes_reverse_iff X Y).mpr (hX Y (Set.mem_univ _))
  · intro h X hX
    apply h X
    intro Y _
    exact (centralizes_reverse_iff X Y).mp (hX Y (Set.mem_univ _))
end Reverse
end Paper18.Category.RelativeTensor
