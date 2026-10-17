import Paper18.Category.MinimalExtensionCentralizer
import Paper18.Category.FusionSubcategoryFunctor

/-! # Actual centralizer equivalences inside a minimal extension -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
universe v u w v' u' w'
namespace Paper18.Category
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [RightRigidCategory C] [Preadditive C] [Linear ℂ C]
  [MonoidalPreadditive C] [MonoidalLinear ℂ C] [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ C)]
  {D : Type u'} [Category.{v'} D] [MonoidalCategory D] [BraidedCategory D]
  [RightRigidCategory D] [Preadditive D] [Linear ℂ D]
  [MonoidalPreadditive D] [MonoidalLinear ℂ D] [HasKernels D] [HasFiniteBiproducts D]
  [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ D)]
  (F : C ⥤ D) [F.Additive] [F.Linear ℂ] [F.Braided] [F.Full] [F.Faithful]
  (A : Set C) {f : C} (hf : f ∈ mugerCenter (C := C))

include hf in
lemma centralizer_image_union_map (X : C) (hX : X ∈ centralizer A) :
    F.obj X ∈ centralizer (F.obj '' A ∪ {F.obj f}) := by
  intro Y hY
  rcases hY with hY | hY
  · obtain ⟨Z, hZ, rfl⟩ := hY
    exact (hX Z hZ).map F
  · rcases Set.mem_singleton_iff.mp hY with rfl
    exact (hf X (Set.mem_univ _)).symm.map F

/-- The actual restriction sends a source centralizer to the simultaneous
actual centralizer of its image and the distinguished invertible. -/
def centralizerImageFunctor : CentralizerCategory A ⥤
    CentralizerCategory (F.obj '' A ∪ {F.obj f}) :=
  fullSubcategoryFunctor (centralizerProperty A)
    (centralizerProperty (F.obj '' A ∪ {F.obj f})) F (centralizer_image_union_map F A hf)

instance centralizerImageFunctor_full : (centralizerImageFunctor F A hf).Full where
  map_surjective g := ⟨F.preimage g, F.map_preimage g⟩
instance centralizerImageFunctor_faithful : (centralizerImageFunctor F A hf).Faithful where
  map_injective {X Y} f g h := F.map_injective h
instance centralizerImageFunctor_additive : (centralizerImageFunctor F A hf).Additive := by
  dsimp [centralizerImageFunctor]; infer_instance
instance centralizerImageFunctor_linear : (centralizerImageFunctor F A hf).Linear ℂ := by
  dsimp [centralizerImageFunctor]; infer_instance
instance centralizerImageFunctor_monoidal : (centralizerImageFunctor F A hf).Monoidal := by
  dsimp [centralizerImageFunctor]; infer_instance
instance centralizerImageFunctor_braided : (centralizerImageFunctor F A hf).Braided where
  braided X Y := Functor.LaxBraided.braided (F := F) X.obj Y.obj

variable {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  {κ : Type w'} [Fintype κ] (T : FiniteSemisimpleSkeleton D κ)
  (K : PivotalStructure D) (hD : IsNondegenerate (C := D))
  (hminimal : T.fusionBasis.totalFPdim = 2 * S.fusionBasis.totalFPdim)
  (E : TensorInverse f) (hne : ¬ Nonempty (f ≅ 𝟙_ C))

include hf S T K hD hminimal E hne in
def centralizerImageFunctorEssSurj : (centralizerImageFunctor F A hf).EssSurj where
  mem_essImage Y := by
    have heq := centralizer_invertible_eq_image_of_minimal S T F K hD hminimal E hne hf
    have hi : F.essImage Y.obj := by
      rw [← heq]
      exact fun Z hZ => Y.property Z (Or.inr hZ)
    obtain ⟨X, ⟨e⟩⟩ := hi
    have hX : X ∈ centralizer A := by
      intro Z hZ
      apply (centralizes_map_iff F X Z).mp
      exact (Y.property (F.obj Z) (Or.inl ⟨Z, hZ, rfl⟩)).of_iso_left e
    exact ⟨⟨X, hX⟩,
      ⟨(centralizerProperty (F.obj '' A ∪ {F.obj f})).isoMk e⟩⟩

include hf S T K hD hminimal E hne in
/-- The actual source centralizer is equivalent to the actual simultaneous
centralizer in the minimal extension. Essential surjectivity is derived
from minimality, actual two-object support, and the actual double centralizer. -/
def centralizerEquivalenceOfMinimal : CentralizerCategory A ≌
    CentralizerCategory (F.obj '' A ∪ {F.obj f}) := by
  letI := centralizerImageFunctorEssSurj F A hf S T K hD hminimal E hne
  letI : (centralizerImageFunctor F A hf).IsEquivalence := {}
  exact (centralizerImageFunctor F A hf).asEquivalence

local notation "eMin" => centralizerEquivalenceOfMinimal F A hf S T K hD hminimal E hne

instance centralizerEquivalenceOfMinimal_functor_braided : (eMin).functor.Braided :=
  centralizerImageFunctor_braided F A hf
instance centralizerEquivalenceOfMinimal_functor_linear : (eMin).functor.Linear ℂ :=
  centralizerImageFunctor_linear F A hf
instance centralizerEquivalenceOfMinimal_functor_additive : (eMin).functor.Additive :=
  centralizerImageFunctor_additive F A hf
instance centralizerEquivalenceOfMinimal_inverse_monoidal : (eMin).inverse.Monoidal :=
  (eMin).inverseMonoidal
instance centralizerEquivalenceOfMinimal_isMonoidal : (eMin).IsMonoidal := inferInstance
instance centralizerEquivalenceOfMinimal_unit_monoidal : NatTrans.IsMonoidal (eMin).unitIso.hom :=
  inferInstanceAs (NatTrans.IsMonoidal (eMin).unit)
instance centralizerEquivalenceOfMinimal_counit_monoidal : NatTrans.IsMonoidal (eMin).counitIso.hom :=
  inferInstanceAs (NatTrans.IsMonoidal (eMin).counit)
instance centralizerEquivalenceOfMinimal_inverse_linear : (eMin).inverse.Linear ℂ :=
  Equivalence.inverseLinear ℂ eMin
instance centralizerEquivalenceOfMinimal_inverse_additive : (eMin).inverse.Additive :=
  Equivalence.inverse_additive eMin

instance centralizerEquivalenceOfMinimal_inverse_braided : (eMin).inverse.Braided where
  toMonoidal := centralizerEquivalenceOfMinimal_inverse_monoidal F A hf S T K hD hminimal E hne
  braided X Y := by
    letI : NatTrans.IsMonoidal (eMin).counitIso.symm.hom :=
      inferInstanceAs (NatTrans.IsMonoidal (eMin).counitIso.inv)
    letI : ((eMin).inverse ⋙ (eMin).functor).LaxBraided :=
      Functor.LaxBraided.ofNatIso (eMin).counitIso.symm
    have h := Functor.LaxBraided.braided (F := (eMin).inverse ⋙ (eMin).functor) X Y
    apply (eMin).functor.map_injective
    apply (cancel_epi (Functor.LaxMonoidal.μ (eMin).functor
      ((eMin).inverse.obj X) ((eMin).inverse.obj Y))).mp
    simp only [Functor.map_comp]
    rw [Functor.LaxBraided.braided_assoc]
    simpa only [Functor.comp_map, Functor.comp_obj, Functor.LaxMonoidal.comp_μ,
      Category.assoc] using h

include hf S T K hD hminimal E hne in
/-- The actual simultaneous target centralizer is integral whenever the
actual source centralizer is integral. The required dominance comes from
the constructed actual equivalence. -/
theorem centralizerIntegral_image_union_of_minimal (hI : S.CentralizerIntegral A) :
    T.CentralizerIntegral (F.obj '' A ∪ {F.obj f}) := by
  let P := centralizerProperty A
  let Q := centralizerProperty (F.obj '' A ∪ {F.obj f})
  letI := S.fullSubcategoryHasKernels P
  letI := S.fullSubcategoryRightRigid P
  letI := S.fullSubcategorySimpleUnit P
  letI := T.fullSubcategoryHasKernels Q
  letI := T.fullSubcategoryRightRigid Q
  letI := T.fullSubcategorySimpleUnit Q
  let R := centralizerImageFunctor F A hf
  letI := centralizerImageFunctorEssSurj F A hf S T K hD hminimal E hne
  apply (S.fullSubcategorySkeleton P).integral_of_dominant
    (T.fullSubcategorySkeleton Q) R ?_ hI
  intro Y
  exact ⟨R.objPreimage Y, ⟨Retract.ofIso (R.objObjPreimageIso Y).symm⟩⟩

end Paper18.Category
