import Paper18.Category.GradedQuasiCancellationBasic

/-! # Actual cochain rescaling of homogeneous associators -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory CategoryTheory.Limits
universe v u w
namespace Paper18.Category.GradedQuasiCancellation
open FiniteCohomologyKilling
variable {C : Type u} [Category.{v} C] [MonoidalCategoryStruct C]
  [Preadditive C] [Linear ℂ C] {G : Type w} [Group G]
  (T : TensorCoherence (C := C)) (L : TensorLinearity (C := C))
  (P : HomogeneousGrading (C := C) G) (a : ThreeCochain G ℂˣ)

/-- The actual old associator multiplied by the inverse cochain. -/
def rescaledAssociator (X Y Z : C) : (X ⊗ Y) ⊗ Z ≅ X ⊗ (Y ⊗ Z) :=
  scalarIso (a.val (P.degree X) (P.degree Y) (P.degree Z))⁻¹ (α_ X Y Z)

include T L in
/-- Scalar rescaling is natural on all actual morphisms, including zero
maps between different graded components. -/
theorem rescaledAssociator_naturality
    {X₁ X₂ X₃ Y₁ Y₂ Y₃ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃) :
    ((f₁ ⊗ₘ f₂) ⊗ₘ f₃) ≫ (rescaledAssociator P a Y₁ Y₂ Y₃).hom =
      (rescaledAssociator P a X₁ X₂ X₃).hom ≫ (f₁ ⊗ₘ (f₂ ⊗ₘ f₃)) := by
  change ((f₁ ⊗ₘ f₂) ⊗ₘ f₃) ≫
      (((a.val (P.degree Y₁) (P.degree Y₂) (P.degree Y₃))⁻¹ : ℂˣ).val • (α_ Y₁ Y₂ Y₃).hom) =
    (((a.val (P.degree X₁) (P.degree X₂) (P.degree X₃))⁻¹ : ℂˣ).val •
      (α_ X₁ X₂ X₃).hom) ≫ (f₁ ⊗ₘ (f₂ ⊗ₘ f₃))
  by_cases h₁ : f₁ = 0
  · simp only [h₁, TensorLinearity.zero_tensor T L, zero_comp, comp_zero]
  by_cases h₂ : f₂ = 0
  · simp only [h₂, TensorLinearity.zero_tensor T L, TensorLinearity.tensor_zero T L,
      zero_comp, comp_zero]
  by_cases h₃ : f₃ = 0
  · simp only [h₃, TensorLinearity.tensor_zero T L, zero_comp, comp_zero]
  have d₁ := P.degree_eq_of_ne_zero h₁
  have d₂ := P.degree_eq_of_ne_zero h₂
  have d₃ := P.degree_eq_of_ne_zero h₃
  simp only [Linear.smul_comp, Linear.comp_smul, ← d₁, ← d₂, ← d₃,
    T.associator_naturality]

/-- Actual tensor data with the corrected associator and the unchanged
actual tensor products and unit isomorphisms. -/
def rescaledStruct : MonoidalCategoryStruct C :=
  { (inferInstance : MonoidalCategoryStruct C) with associator := rescaledAssociator P a }

/-- All actual tensor/unitor equations survive the cochain correction;
only the actual pentagon defect changes. -/
def rescaledCoherence :
    letI := rescaledStruct P a
    TensorCoherence (C := C) := by
  have hn : ∀ {X₁ X₂ X₃ Y₁ Y₂ Y₃ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃),
      ((f₁ ⊗ₘ f₂) ⊗ₘ f₃) ≫ (rescaledAssociator P a Y₁ Y₂ Y₃).hom =
        (rescaledAssociator P a X₁ X₂ X₃).hom ≫ (f₁ ⊗ₘ (f₂ ⊗ₘ f₃)) :=
    rescaledAssociator_naturality T L P a
  have du := P.degree_unit
  rcases T with ⟨htdef, htid, htcomp, hwLid, hwRid, _, hLeftNat, hRightNat, htriangle⟩
  letI := rescaledStruct P a
  exact
    { tensorHom_def := htdef
      id_tensorHom_id := htid
      tensorHom_comp_tensorHom := htcomp
      whiskerLeft_id := hwLid
      id_whiskerRight := hwRid
      associator_naturality := hn
      leftUnitor_naturality := hLeftNat
      rightUnitor_naturality := hRightNat
      triangle X Y := by
        simpa only [rescaledStruct, rescaledAssociator, scalarIso, du,
          a.one₂, inv_one, Units.val_one, one_smul] using htriangle X Y }

/-- The same actual homogeneous degree function remains a grading. -/
def rescaledGrading :
    letI := rescaledStruct P a
    HomogeneousGrading (C := C) G := by
  have du := P.degree_unit
  have dt := P.degree_tensor
  have hz : ∀ {X Y : C}, P.degree X ≠ P.degree Y → ∀ f : X ⟶ Y, f = 0 := P.hom_zero
  let d := P.degree
  letI := rescaledStruct P a
  exact
    { degree := d
      degree_unit := du
      degree_tensor := dt
      hom_zero := hz }

/-- Actual bilinearity is preserved because the underlying tensor maps
are the same actual maps. -/
def rescaledLinearity :
    letI := rescaledStruct P a
    TensorLinearity (C := C) := by
  rcases L with ⟨hL0, hR0, hLadd, hRadd, hLsmul, hRsmul⟩
  letI := rescaledStruct P a
  exact
    { whiskerLeft_zero := hL0
      zero_whiskerRight := hR0
      whiskerLeft_add := hLadd
      add_whiskerRight := hRadd
      whiskerLeft_smul := hLsmul
      smul_whiskerRight := hRsmul }

end Paper18.Category.GradedQuasiCancellation
