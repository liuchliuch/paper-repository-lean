import Paper18.Category.CentralizerJoinTensor

/-! # Actual retract image and dominance of the tensor join functor -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators
universe v u v' u' w
namespace Paper18.Category.FusionJoin

section RetractImage
variable {E : Type u'} [Category.{v'} E] {C : Type u} [Category.{v} C]
  (F : E ⥤ C)

/-- The actual summand closure of a functor's actual object image. -/
def retractImage : ObjectProperty C := fun X => ∃ Y, Nonempty (Retract X (F.obj Y))

variable [Preadditive E] [HasFiniteBiproducts E]
  [Preadditive C] [HasFiniteBiproducts C] [F.Additive]

instance retractImage_isAdditive : IsAdditiveFullProperty (retractImage F) where
  of_retract r h := by
    obtain ⟨Y, ⟨s⟩⟩ := h
    exact ⟨Y, ⟨r.trans s⟩⟩
  biproduct f hf := by
    choose Y r using hf
    let s : ∀j, Retract (f j) (F.obj (Y j)) := fun j => Classical.choice (r j)
    let t : Retract (⨁ f) (⨁ fun j => F.obj (Y j)) := {
      i := biproduct.map (fun j => (s j).i)
      r := biproduct.map (fun j => (s j).r)
      retract := by
        apply biproduct.hom_ext
        intro j
        rw [assoc, biproduct.map_π, ← assoc, biproduct.map_π, assoc, (s j).retract, comp_id, id_comp] }
    exact ⟨⨁ Y, ⟨t.trans (Retract.ofIso (F.mapBiproduct Y).symm)⟩⟩

variable [MonoidalCategory E] [MonoidalCategory C] [F.Monoidal]

instance retractImage_isMonoidal : (retractImage F).IsMonoidal where
  prop_unit := ⟨𝟙_ E, ⟨Retract.ofIso (Functor.Monoidal.εIso F)⟩⟩
  prop_tensor _ _ hX hY := by
    obtain ⟨X, ⟨r⟩⟩ := hX
    obtain ⟨Y, ⟨s⟩⟩ := hY
    let t : Retract _ (F.obj X ⊗ F.obj Y) := {
      i := r.i ⊗ₘ s.i
      r := r.r ⊗ₘ s.r
      retract := by rw [tensorHom_comp_tensorHom, r.retract, s.retract, tensorHom_id, id_whiskerRight] }
    exact ⟨X ⊗ Y, ⟨t.trans (Retract.ofIso (Functor.Monoidal.μIso F X Y))⟩⟩
end RetractImage

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasFiniteBiproducts C]
  (P Q : ObjectProperty C) [P.IsMonoidal] [Q.IsMonoidal]
  [IsAdditiveFullProperty P] [IsAdditiveFullProperty Q]

lemma tensorFunctor_mem_join (X : DeligneProduct P.FullSubcategory Q.FullSubcategory) :
    fusionJoin P Q ((tensorFunctor P Q).obj X) := by
  change fusionJoin P Q (⨁ fun i => (X.X i).left.obj ⊗ (X.X i).right.obj)
  apply @IsAdditiveFullProperty.biproduct C _ _ ‹HasFiniteBiproducts C› (fusionJoin P Q) _
  intro i
  exact ObjectProperty.prop_tensor
    (subset_fusionJoin_left P Q _ (X.X i).left.property)
    (subset_fusionJoin_right P Q _ (X.X i).right.property)

lemma retractImage_le_join : ∀ X, retractImage (tensorFunctor P Q) X → fusionJoin P Q X := by
  rintro X ⟨Y, ⟨r⟩⟩
  exact @IsAdditiveFullProperty.of_retract C _ _ ‹HasFiniteBiproducts C› (fusionJoin P Q) _ _ _ r (tensorFunctor_mem_join P Q Y)

lemma left_le_retractImage : ∀ X, P X → retractImage (tensorFunctor P Q) X := by
  intro X hX
  refine ⟨(Mat_.embedding _).obj ⟨⟨X,hX⟩,𝟙_ Q.FullSubcategory⟩, ⟨Retract.ofIso ?_⟩⟩
  exact (tensorPairIso P Q ⟨X,hX⟩ (𝟙_ Q.FullSubcategory) ≪≫ ρ_ X).symm

lemma right_le_retractImage : ∀ X, Q X → retractImage (tensorFunctor P Q) X := by
  intro X hX
  refine ⟨(Mat_.embedding _).obj ⟨𝟙_ P.FullSubcategory,⟨X,hX⟩⟩, ⟨Retract.ofIso ?_⟩⟩
  exact (tensorPairIso P Q (𝟙_ P.FullSubcategory) ⟨X,hX⟩ ≪≫ λ_ X).symm

/-- The actual tensor functor landing in the actual fusion join. -/
def tensorToJoin : DeligneProduct P.FullSubcategory Q.FullSubcategory ⥤ (fusionJoin P Q).FullSubcategory :=
  (fusionJoin P Q).lift (tensorFunctor P Q) (tensorFunctor_mem_join P Q)

instance tensorToJoin_additive : (tensorToJoin P Q).Additive where
  map_add := by intros; exact (tensorFunctor P Q).map_add
instance tensorToJoin_linear : (tensorToJoin P Q).Linear ℂ where
  map_smul f r := (tensorFunctor P Q).map_smul r f
instance tensorToJoin_monoidal : (tensorToJoin P Q).Monoidal :=
  Functor.CoreMonoidal.toMonoidal {
    εIso := (fusionJoin P Q).isoMk (Functor.Monoidal.εIso (tensorFunctor P Q))
    μIso X Y := (fusionJoin P Q).isoMk (Functor.Monoidal.μIso (tensorFunctor P Q) X Y)
    μIso_hom_natural_left := fun f Y => Functor.LaxMonoidal.μ_natural_left (tensorFunctor P Q) f Y
    μIso_hom_natural_right := fun X f => Functor.LaxMonoidal.μ_natural_right (tensorFunctor P Q) X f
    associativity X Y Z := Functor.LaxMonoidal.associativity (tensorFunctor P Q) X Y Z
    left_unitality X := Functor.LaxMonoidal.left_unitality (tensorFunctor P Q) X
    right_unitality X := Functor.LaxMonoidal.right_unitality (tensorFunctor P Q) X }

variable [HasKernels C] [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  [RightRigidCategory C] [Simple (𝟙_ C)] {ι : Type w} [Fintype ι]
  (S : FiniteSemisimpleSkeleton C ι) (J : PivotalStructure C)

include S J in
lemma retractImage_eq_join (hC : IsNondegenerate (C := C)) :
    retractImage (tensorFunctor P Q) = fusionJoin P Q := by
  apply le_antisymm (retractImage_le_join P Q)
  exact (S.fusionJoin_le_iff J hC P Q _).mpr
    ⟨left_le_retractImage P Q, right_le_retractImage P Q⟩

include S J in
/-- Actual dominance is proved from tensor-image closure and the least
fusion-subcategory property, with a concrete retract for every target. -/
lemma tensorToJoin_dominant (hC : IsNondegenerate (C := C))
    (X : (fusionJoin P Q).FullSubcategory) :
    ∃ Y, Nonempty (Retract X ((tensorToJoin P Q).obj Y)) := by
  have h : retractImage (tensorFunctor P Q) X.obj := by
    rw [retractImage_eq_join P Q S J hC]
    exact X.property
  obtain ⟨Y, ⟨r⟩⟩ := h
  exact ⟨Y, ⟨{ i := r.i, r := r.r, retract := r.retract }⟩⟩

end Paper18.Category.FusionJoin
