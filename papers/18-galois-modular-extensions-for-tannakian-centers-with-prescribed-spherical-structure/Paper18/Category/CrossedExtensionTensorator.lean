import Paper18.Category.CrossedExtensionRegrade

/-! # Actual unit-valued scalar tensorators on convolution -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
namespace Paper18.Category.CrossedExtension
variable {A : Type} [Fintype A] [AddGroup A]
open GradedObject.Monoidal
local instance tensoratorBaseMonoidal : MonoidalCategory (GradedObject A (FGModuleCat ℂ)) :=
  GradedObject.monoidalCategory

/-- An actual scalar map on each homogeneous tensor summand. -/
def binaryScalar (t : A → A → ℂ) (X Y : PointedVec A) : X ⊗ Y ⟶ X ⊗ Y :=
  fun k => tensorObjDesc (fun a b h => t a b • ιTensorObj X Y a b k h)

@[reassoc (attr := simp)]
lemma inclusion_binaryScalar (t : A → A → ℂ) (X Y : PointedVec A)
    (a b k : A) (h : a + b = k) :
    ιTensorObj X Y a b k h ≫ binaryScalar t X Y k = t a b • ιTensorObj X Y a b k h := by
  simp [binaryScalar]

lemma binaryScalar_comp (t s : A → A → ℂ) (X Y : PointedVec A) :
    binaryScalar t X Y ≫ binaryScalar s X Y = binaryScalar (fun a b => t a b * s a b) X Y := by
  apply GradedObject.hom_ext
  intro k
  apply tensorObj_ext
  intro a b h
  simp [smul_smul]

lemma binaryScalar_one (X Y : PointedVec A) : binaryScalar (fun _ _ => 1) X Y = 𝟙 _ := by
  apply GradedObject.hom_ext
  intro k
  apply tensorObj_ext
  intro a b h
  simp
  exact (comp_id _).symm

def binaryScalarIso (t : A → A → ℂˣ) (X Y : PointedVec A) : X ⊗ Y ≅ X ⊗ Y where
  hom := binaryScalar (fun a b => (t a b : ℂ)) X Y
  inv := binaryScalar (fun a b => ((t a b)⁻¹ : ℂˣ)) X Y
  hom_inv_id := by
    rw [binaryScalar_comp]
    simpa only [← Units.val_mul, mul_inv_cancel, Units.val_one] using binaryScalar_one X Y
  inv_hom_id := by
    rw [binaryScalar_comp]
    simpa only [← Units.val_mul, inv_mul_cancel, Units.val_one] using binaryScalar_one X Y

lemma binaryScalar_naturality (t : A → A → ℂ) {X X' Y Y' : PointedVec A}
    (f : X ⟶ X') (g : Y ⟶ Y') :
    (f ⊗ₘ g) ≫ binaryScalar t X' Y' = binaryScalar t X Y ≫ (f ⊗ₘ g) := by
  apply GradedObject.hom_ext
  intro k
  apply tensorObj_ext
  intro a b h
  change ιTensorObj X Y a b k h ≫ GradedObject.Monoidal.tensorHom f g k ≫ _ =
    ιTensorObj X Y a b k h ≫ binaryScalar t X Y k ≫ GradedObject.Monoidal.tensorHom f g k
  simp

/-- The actual scalar-weighted tensor comparison for an actual regrading functor. -/
def weightedRegradeTensorIso (e : A ≃+ A) (t : A → A → ℂˣ) (X Y : PointedVec A) :
    (regradeFunctor e).obj X ⊗ (regradeFunctor e).obj Y ≅
      (regradeFunctor e).obj (X ⊗ Y) :=
  binaryScalarIso t _ _ ≪≫ regradeTensorIso e X Y

@[reassoc (attr := simp)]
lemma inclusion_weightedRegradeTensorIso (e : A ≃+ A) (t : A → A → ℂˣ)
    (X Y : PointedVec A) (a b k : A) (h : a + b = k) :
    ιTensorObj ((regradeFunctor e).obj X) ((regradeFunctor e).obj Y) a b k h ≫
        (weightedRegradeTensorIso e t X Y).hom k =
      (t a b : ℂ) • ιTensorObj X Y (e a) (e b) (e k) (by rw [← e.map_add, h]) := by
  change _ ≫ (binaryScalar _ _ _ k ≫ regradeTensorHom e X Y k) = _
  simp

lemma weightedRegradeTensorIso_naturality (e : A ≃+ A) (t : A → A → ℂˣ)
    {X X' Y Y' : PointedVec A} (f : X ⟶ X') (g : Y ⟶ Y') :
    ((regradeFunctor e).map f ⊗ₘ (regradeFunctor e).map g) ≫
        (weightedRegradeTensorIso e t X' Y').hom =
      (weightedRegradeTensorIso e t X Y).hom ≫ (regradeFunctor e).map (f ⊗ₘ g) := by
  change _ ≫ binaryScalar _ _ _ ≫ regradeTensorHom _ _ _ =
    binaryScalar _ _ _ ≫ regradeTensorHom _ _ _ ≫ _
  rw [← assoc, binaryScalar_naturality, assoc, regradeTensorHom_naturality]

end Paper18.Category.CrossedExtension
