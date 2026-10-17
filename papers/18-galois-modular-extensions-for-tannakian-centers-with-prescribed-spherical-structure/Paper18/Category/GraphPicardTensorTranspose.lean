import Paper18.Category.GraphPicardTensorTransposeBasic

/-! # Tensor products of actual rigid transposes -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
universe v u
namespace Paper18.Category.GraphPicard
variable {E : Type u} [Category.{v} E] [MonoidalCategory E]

@[reassoc] lemma nestedCap_naturality_left {U U' V' P Q : E}
    (e : U' ⊗ U ⟶ 𝟙_ E) (f : V' ⊗ Q ⟶ 𝟙_ E) (h : P ⟶ U) :
    (V' ⊗ U') ◁ (h ▷ Q) ≫ nestedCap e f =
      nestedCap (U' ◁ h ≫ e) f := by
  have hi : U' ◁ (h ▷ Q) ≫ (α_ U' U Q).inv ≫ e ▷ Q ≫ (λ_ Q).hom =
      (α_ U' P Q).inv ≫ (U' ◁ h ≫ e) ▷ Q ≫ (λ_ Q).hom := by
    rw [associator_inv_naturality_middle_assoc]
    simp only [comp_whiskerRight, Category.assoc]
  unfold nestedCap
  rw [associator_naturality_right_assoc]
  simpa only [whiskerLeft_comp, Category.assoc] using
    congrArg (fun k => (α_ V' U' (P ⊗ Q)).hom ≫ V' ◁ k ≫ f) hi

@[reassoc] lemma nestedCap_naturality_right {U' V V' P Q : E}
    (e : U' ⊗ P ⟶ 𝟙_ E) (f : V' ⊗ V ⟶ 𝟙_ E) (k : Q ⟶ V) :
    (V' ⊗ U') ◁ (P ◁ k) ≫ nestedCap e f =
      nestedCap e (V' ◁ k ≫ f) := by
  have hi : U' ◁ (P ◁ k) ≫ (α_ U' P V).inv ≫ e ▷ V ≫ (λ_ V).hom =
      ((α_ U' P Q).inv ≫ e ▷ Q ≫ (λ_ Q).hom) ≫ k := by
    rw [associator_inv_naturality_right_assoc, whisker_exchange_assoc,
      leftUnitor_naturality]
    simp only [Category.assoc]
  unfold nestedCap
  rw [associator_naturality_right_assoc]
  simpa only [whiskerLeft_comp, Category.assoc] using
    congrArg (fun t => (α_ V' U' (P ⊗ Q)).hom ≫ V' ◁ t ≫ f) hi

/-- The actual nested cap of tensor maps is the nested cap of their
actual evaluations. This is a diagram identity, with no tensor-compatibility premise. -/
lemma nestedCap_naturality {U U' V V' P Q : E}
    (e : U' ⊗ U ⟶ 𝟙_ E) (f : V' ⊗ V ⟶ 𝟙_ E) (h : P ⟶ U) (k : Q ⟶ V) :
    (V' ⊗ U') ◁ (h ⊗ₘ k) ≫ nestedCap e f =
      nestedCap (U' ◁ h ≫ e) (V' ◁ k ≫ f) := by
  rw [MonoidalCategory.tensorHom_def, whiskerLeft_comp, Category.assoc,
    nestedCap_naturality_right, nestedCap_naturality_left]

/-- Transposing a genuine nested cap gives exactly the tensor product
of its genuine transposes, for arbitrary supplied exact pairings. -/
theorem capTranspose_tensor {U U' V V' P Q : E}
    [ExactPairing U U'] [ExactPairing V V']
    (e : U' ⊗ P ⟶ 𝟙_ E) (f : V' ⊗ Q ⟶ 𝟙_ E) :
    letI := specifiedTensorPairing U U' V V'
    capTransposeEquiv (U ⊗ V) (V' ⊗ U') (P ⊗ Q) (nestedCap e f) =
      capTransposeEquiv U U' P e ⊗ₘ capTransposeEquiv V V' Q f := by
  letI := specifiedTensorPairing U U' V V'
  apply cap_evaluation_injective (U ⊗ V) (V' ⊗ U') (P ⊗ Q)
  rw [capTransposeEquiv_evaluation]
  change nestedCap e f = (V' ⊗ U') ◁
    (capTransposeEquiv U U' P e ⊗ₘ capTransposeEquiv V V' Q f) ≫
      nestedCap (ε_ U U') (ε_ V V')
  rw [nestedCap_naturality, capTransposeEquiv_evaluation, capTransposeEquiv_evaluation]

end Paper18.Category.GraphPicard
