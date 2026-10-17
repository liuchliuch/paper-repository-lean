import Paper18.Category.DrinfeldInnerTrivializationMonoidal

/-! # The actual half-braiding trivializes tensor conjugation on the center -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Functor.LaxMonoidal CategoryTheory.Functor.Monoidal
universe v u w
namespace Paper18.Category.DrinfeldInner
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  (F : C ⥤ C) [F.Monoidal] [F.IsEquivalence] (L : C)
  (γ : tensorLeft L ≅ F ⋙ tensorRight L)

/-- The actual central half-braidings form a natural family when the
homogeneous line is held fixed. -/
def centralLineIso : Center.forget C ⋙ tensorRight L ≅ Center.forget C ⋙ tensorLeft L :=
  NatIso.ofComponents (fun Z => Z.2.β L) (fun f => f.comm L)

/-- After right tensoring by the actual conjugating line, the desired
trivialization is the inverse intertwiner followed by the inverse half-braiding. -/
def whiskeredTrivialization :
    (DrinfeldEquivalence.map F ⋙ Center.forget C) ⋙ tensorRight L ≅
      Center.forget C ⋙ tensorRight L :=
  Functor.isoWhiskerRight (DrinfeldEquivalence.forgetIso F) (tensorRight L) ≪≫
    Functor.associator (Center.forget C) F (tensorRight L) ≪≫
      Functor.isoWhiskerLeft (Center.forget C) γ.symm ≪≫ (centralLineIso L).symm

/-- Fully faithful cancellation of the actual invertible line constructs
the natural isomorphism; no trivialization is an existence premise. -/
def underlyingOfIntertwiner (E : TensorInverse L) :
    DrinfeldEquivalence.map F ⋙ Center.forget C ≅ Center.forget C := by
  letI : (tensorRight L).IsEquivalence := (tensorRightEquivalence E).isEquivalence_functor
  exact ((Functor.whiskeringRight (Center C) C C).obj (tensorRight L)).preimageIso
    (whiskeredTrivialization F L γ)

lemma underlyingOfIntertwiner_whisker (E : TensorInverse L) (Z : Center C) :
    (underlyingOfIntertwiner F L γ E).hom.app Z ▷ L =
      (γ.app Z.1).inv ≫ (Z.2.β L).inv := by
  letI : (tensorRight L).IsEquivalence := (tensorRightEquivalence E).isEquivalence_functor
  let Q := (Functor.whiskeringRight (Center C) C C).obj (tensorRight L)
  have h := Q.map_preimage (whiskeredTrivialization F L γ).hom
  have ha := congrArg (fun a => a.app Z) h
  change (underlyingOfIntertwiner F L γ E).hom.app Z ▷ L =
    (whiskeredTrivialization F L γ).hom.app Z at ha
  simp only [whiskeredTrivialization, Iso.trans_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, DrinfeldEquivalence.forgetIso, Iso.refl_hom,
    NatTrans.id_app, Functor.map_id, Functor.associator_hom_app,
    centralLineIso, NatIso.ofComponents_inv_app, Iso.symm_hom, tensorRight,
    id_whiskerRight, id_comp] at ha
  change (underlyingOfIntertwiner F L γ E).hom.app Z ▷ L =
    (𝟙 (F.obj Z.1) ▷ L) ≫ (γ.app Z.1).inv ≫ (Z.2.β L).inv at ha
  simpa only [id_whiskerRight, id_comp] using ha

lemma underlyingOfIntertwiner_intertwines (E : TensorInverse L) (Z : Center C) :
    γ.hom.app Z.1 ≫ (underlyingOfIntertwiner F L γ E).hom.app Z ▷ L =
      (Z.2.β L).inv := by
  rw [underlyingOfIntertwiner_whisker]
  exact Iso.hom_inv_id_assoc (γ.app Z.1) _

/-- The actual half-braiding equation determines each trivializing
component uniquely, by faithful cancellation of the invertible line. -/
lemma intertwining_unique (E : TensorInverse L) (Z : Center C)
    (a b : F.obj Z.1 ⟶ Z.1)
    (ha : γ.hom.app Z.1 ≫ a ▷ L = (Z.2.β L).inv)
    (hb : γ.hom.app Z.1 ≫ b ▷ L = (Z.2.β L).inv) : a = b := by
  letI : (tensorRight L).IsEquivalence := (tensorRightEquivalence E).isEquivalence_functor
  apply (tensorRight L).map_injective
  change a ▷ L = b ▷ L
  apply (cancel_epi (γ.app Z.1).hom).mp
  exact ha.trans hb.symm

/-- Actual tensor and unit coherence of the conjugation intertwiner imply
actual monoidality of the constructed underlying trivialization. -/
def underlyingOfIntertwinerMonoidal (E : TensorInverse L)
    (hγunit : γ.hom.app (𝟙_ C) =
      (ρ_ L).hom ≫ (λ_ L).inv ≫ ε F ▷ L)
    (hγtensor : ∀ X Y, γ.hom.app (X ⊗ Y) =
      (conjugatingTensorIso F L γ X Y).hom ≫ μ F X Y ▷ L) :
    NatTrans.IsMonoidal (underlyingOfIntertwiner F L γ E).hom :=
  monoidalOfIntertwining F L γ (underlyingOfIntertwiner F L γ E) E hγunit hγtensor
    (underlyingOfIntertwiner_intertwines F L γ E)

section Fusion
variable [RightRigidCategory C] [Preadditive C] [Linear ℂ C]
  [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [CategoryTheory.Limits.HasKernels C] [CategoryTheory.Limits.HasFiniteBiproducts C]
  [Simple (𝟙_ C)] [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι) (J : PivotalStructure C)

/-- Tensor conjugation by the actual invertible line is actually trivial
on the actual Drinfeld center, with both monoidal laws derived. -/
def trivializationOfIntertwiner (E : TensorInverse L)
    (hγunit : γ.hom.app (𝟙_ C) =
      (ρ_ L).hom ≫ (λ_ L).inv ≫ ε F ▷ L)
    (hγtensor : ∀ X Y, γ.hom.app (X ⊗ Y) =
      (conjugatingTensorIso F L γ X Y).hom ≫ μ F X Y ▷ L) :
    DrinfeldEquivalence.map F ≅ 𝟭 (Center C) := by
  letI := underlyingOfIntertwinerMonoidal F L γ E hγunit hγtensor
  exact liftOverForget F (underlyingOfIntertwiner F L γ E) S J

instance trivializationOfIntertwiner_monoidal (E : TensorInverse L)
    (hγunit : γ.hom.app (𝟙_ C) =
      (ρ_ L).hom ≫ (λ_ L).inv ≫ ε F ▷ L)
    (hγtensor : ∀ X Y, γ.hom.app (X ⊗ Y) =
      (conjugatingTensorIso F L γ X Y).hom ≫ μ F X Y ▷ L) :
    NatTrans.IsMonoidal (trivializationOfIntertwiner F L γ S J E hγunit hγtensor).hom := by
  letI := underlyingOfIntertwinerMonoidal F L γ E hγunit hγtensor
  exact inferInstanceAs (NatTrans.IsMonoidal
    (liftOverForget F (underlyingOfIntertwiner F L γ E) S J).hom)

@[simp] lemma trivializationOfIntertwiner_hom_app_f (E : TensorInverse L)
    (hγunit : γ.hom.app (𝟙_ C) =
      (ρ_ L).hom ≫ (λ_ L).inv ≫ ε F ▷ L)
    (hγtensor : ∀ X Y, γ.hom.app (X ⊗ Y) =
      (conjugatingTensorIso F L γ X Y).hom ≫ μ F X Y ▷ L) (Z : Center C) :
    ((trivializationOfIntertwiner F L γ S J E hγunit hγtensor).hom.app Z).f =
      (underlyingOfIntertwiner F L γ E).hom.app Z := rfl

end Fusion
end Paper18.Category.DrinfeldInner
