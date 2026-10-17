import Paper18.Category.CentralizerDimensionProjector

/-! # Actual images of the categorical centralizer support projector -/
noncomputable section
open Classical
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
universe v u w
namespace Paper18.Category.FiniteSemisimpleSkeleton
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  (P : ObjectProperty C) [IsAdditiveFullProperty P]

/-- The complement of the support idempotent as an actual endomorphism. -/
def supportComplement (X : C) : X ⟶ X :=
  (S.supportProjector (fun Y => ¬ P Y)).app X

/-- The actual fixed subobject of the natural support projector. -/
def supportImage (X : C) : C := kernel (S.supportComplement P X)

def supportImageInclusion (X : C) : S.supportImage P X ⟶ X :=
  kernel.ι (S.supportComplement P X)

instance supportImageInclusion_mono (X : C) : Mono (S.supportImageInclusion P X) :=
  inferInstanceAs (Mono (kernel.ι _))

@[reassoc] lemma supportImageInclusion_projector (X : C) :
    S.supportImageInclusion P X ≫ (S.supportProjector P).app X =
      S.supportImageInclusion P X := by
  have h := kernel.condition (S.supportComplement P X)
  have ht := congrArg (fun q : 𝟭 C ⟶ 𝟭 C => S.supportImageInclusion P X ≫ q.app X)
    (S.supportProjector_add_not P)
  change S.supportImageInclusion P X ≫ ((S.supportProjector P).app X +
    (S.supportProjector (fun Y => ¬ P Y)).app X) = S.supportImageInclusion P X ≫ 𝟙 X at ht
  rw [Preadditive.comp_add] at ht
  change S.supportImageInclusion P X ≫ (S.supportProjector (fun Y => ¬ P Y)).app X = 0 at h
  rw [h, add_zero, comp_id] at ht
  exact ht

lemma supportImage_property (X : C) : P (S.supportImage P X) := by
  apply (S.supportProjector_eq_id_iff P _).mp
  apply (cancel_mono (S.supportImageInclusion P X)).mp
  change (S.supportProjector P).app (S.supportImage P X) ≫ S.supportImageInclusion P X =
    𝟙 (S.supportImage P X) ≫ S.supportImageInclusion P X
  rw [id_comp, ← S.supportProjector_naturality P (S.supportImageInclusion P X)]
  exact S.supportImageInclusion_projector P X

/-- The actual projection onto the fixed subobject, obtained by the kernel
universal property and the proved idempotence. -/
def supportImageProjection (X : C) : X ⟶ S.supportImage P X :=
  kernel.lift (S.supportComplement P X) ((S.supportProjector P).app X) (by
    apply S.hom_ext_simples
    intro i f
    change f ≫ ((S.supportProjector P).app X ≫
      (S.supportProjector (fun Y => ¬ P Y)).app X) = f ≫ 0
    rw [← assoc, S.supportProjector_naturality P, assoc,
      S.supportProjector_naturality (fun Y => ¬ P Y) f,
      S.supportProjector_simple, S.supportProjector_simple]
    split_ifs <;> simp_all)

@[simp, reassoc] lemma supportImageProjection_inclusion (X : C) :
    S.supportImageProjection P X ≫ S.supportImageInclusion P X =
      (S.supportProjector P).app X := kernel.lift_ι _ _ _

@[simp, reassoc] lemma supportImageInclusion_projection (X : C) :
    S.supportImageInclusion P X ≫ S.supportImageProjection P X =
      𝟙 (S.supportImage P X) := by
  apply (cancel_mono (S.supportImageInclusion P X)).mp
  rw [assoc, S.supportImageProjection_inclusion, id_comp]
  exact S.supportImageInclusion_projector P X

/-- The actual support reflector/coreflector on objects. -/
def supportFunctor : C ⥤ P.FullSubcategory where
  obj X := ⟨S.supportImage P X, S.supportImage_property P X⟩
  map {X Y} f := (show S.supportImage P X ⟶ S.supportImage P Y from
    S.supportImageInclusion P X ≫ f ≫ S.supportImageProjection P Y)
  map_id X := by
    change S.supportImageInclusion P X ≫ 𝟙 X ≫ S.supportImageProjection P X = _
    rw [id_comp, S.supportImageInclusion_projection]
    rfl
  map_comp {X Y Z} f g := by
    change S.supportImageInclusion P X ≫ (f ≫ g) ≫ S.supportImageProjection P Z =
      (S.supportImageInclusion P X ≫ f ≫ S.supportImageProjection P Y) ≫
        (S.supportImageInclusion P Y ≫ g ≫ S.supportImageProjection P Z)
    simp only [assoc, S.supportImageProjection_inclusion_assoc]
    rw [S.supportProjector_naturality_assoc P f, S.supportImageInclusion_projector_assoc]

/-- Maps from an actual object in the full subcategory factor uniquely
through the actual fixed subobject. -/
def supportRightHomEquiv (Y : P.FullSubcategory) (X : C) :
    (Y.obj ⟶ X) ≃ (Y.obj ⟶ S.supportImage P X) where
  toFun f := (show Y.obj ⟶ S.supportImage P X from f ≫ S.supportImageProjection P X)
  invFun f := (show Y.obj ⟶ X from (f : Y.obj ⟶ S.supportImage P X) ≫ S.supportImageInclusion P X)
  left_inv f := by
    change (f ≫ S.supportImageProjection P X) ≫ S.supportImageInclusion P X = f
    rw [assoc, S.supportImageProjection_inclusion,
      S.supportProjector_naturality P,
      (S.supportProjector_eq_id_iff P Y.obj).mpr Y.property]
    exact Category.id_comp f
  right_inv f := by
    change ((f : Y.obj ⟶ S.supportImage P X) ≫ S.supportImageInclusion P X) ≫
      S.supportImageProjection P X = (f : Y.obj ⟶ S.supportImage P X)
    simp

/-- The dual Hom correspondence uses the same actual retract. -/
def supportLeftHomEquiv (X : C) (Y : P.FullSubcategory) :
    (S.supportImage P X ⟶ Y.obj) ≃ (X ⟶ Y.obj) where
  toFun f := (show X ⟶ Y.obj from S.supportImageProjection P X ≫ (f : S.supportImage P X ⟶ Y.obj))
  invFun f := (show S.supportImage P X ⟶ Y.obj from S.supportImageInclusion P X ≫ f)
  left_inv f := by
    change S.supportImageInclusion P X ≫ (S.supportImageProjection P X ≫ f) = f
    rw [← assoc, S.supportImageInclusion_projection, id_comp]
  right_inv f := by
    change S.supportImageProjection P X ≫ (S.supportImageInclusion P X ≫ f) = f
    rw [← assoc, S.supportImageProjection_inclusion,
      ← S.supportProjector_naturality P,
      (S.supportProjector_eq_id_iff P Y.obj).mpr Y.property, comp_id]

end Paper18.Category.FiniteSemisimpleSkeleton
