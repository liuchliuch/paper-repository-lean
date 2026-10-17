import Paper18.Category.GradedQuasiCancellationTwist

/-! # Actual cancellation of an associator's fourth-cocycle defect -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
universe v u w
namespace Paper18.Category.GradedQuasiCancellation
open FiniteCohomologyKilling
variable {C : Type u} [Category.{v} C] [MonoidalCategoryStruct C]
  [Preadditive C] [Linear ℂ C] {G : Type w} [Group G]
  (T : TensorCoherence (C := C)) (L : TensorLinearity (C := C))
  (P : HomogeneousGrading (C := C) G)

/-- The actual two composites around the old pentagon differ by the
specified fourth cocycle on the actual object degrees. -/
def HasPentagonDefect (ω : FourCocycle G ℂˣ) : Prop :=
  ∀ W X Y Z : C,
    (α_ W X Y).hom ▷ Z ≫ (α_ W (X ⊗ Y) Z).hom ≫ W ◁ (α_ X Y Z).hom =
      (ω.val (P.degree W) (P.degree X) (P.degree Y) (P.degree Z) : ℂ) •
        ((α_ (W ⊗ X) Y Z).hom ≫ (α_ W X (Y ⊗ Z)).hom)

include L in
/-- The actual associator correction divides the actual pentagon defect
by the actual third coboundary. -/
theorem rescaledAssociator_pentagon_defect (ω : FourCocycle G ℂˣ)
    (hω : HasPentagonDefect P ω) (a : ThreeCochain G ℂˣ) (W X Y Z : C) :
    (rescaledAssociator P a W X Y).hom ▷ Z ≫
        (rescaledAssociator P a W (X ⊗ Y) Z).hom ≫
        W ◁ (rescaledAssociator P a X Y Z).hom =
      ((ω.twist a).val (P.degree W) (P.degree X) (P.degree Y) (P.degree Z) : ℂ) •
        ((rescaledAssociator P a (W ⊗ X) Y Z).hom ≫
          (rescaledAssociator P a W X (Y ⊗ Z)).hom) := by
  simp only [rescaledAssociator, scalarIso, L.smul_whiskerRight, L.whiskerLeft_smul,
    Linear.smul_comp, Linear.comp_smul, smul_smul, P.degree_tensor]
  rw [hω W X Y Z]
  simp only [smul_smul]
  congr 1
  have hs :
      (a.val (P.degree W) (P.degree X) (P.degree Y))⁻¹ *
          (a.val (P.degree W) (P.degree X * P.degree Y) (P.degree Z))⁻¹ *
          (a.val (P.degree X) (P.degree Y) (P.degree Z))⁻¹ *
          ω.val (P.degree W) (P.degree X) (P.degree Y) (P.degree Z) =
        (ω.twist a).val (P.degree W) (P.degree X) (P.degree Y) (P.degree Z) *
          (a.val (P.degree W * P.degree X) (P.degree Y) (P.degree Z))⁻¹ *
          (a.val (P.degree W) (P.degree X) (P.degree Y * P.degree Z))⁻¹ := by
    apply Additive.ofMul.injective
    simp only [FourCocycle.twist, dThree, div_eq_mul_inv, ofMul_mul, ofMul_inv]
    abel
  simpa only [Units.val_mul, Units.val_inv_eq_inv_val, mul_assoc, mul_comm, mul_left_comm] using
    congrArg (fun s : ℂˣ => (s : ℂ)) hs

include L in
/-- An actual primitive of the actual defect makes the corrected
associator satisfy the actual pentagon. -/
theorem rescaledAssociator_pentagon (ω : FourCocycle G ℂˣ)
    (hω : HasPentagonDefect P ω) (a : ThreeCochain G ℂˣ)
    (ha : ∀ g h k l, dThree a.val g h k l = ω.val g h k l) (W X Y Z : C) :
    (rescaledAssociator P a W X Y).hom ▷ Z ≫
        (rescaledAssociator P a W (X ⊗ Y) Z).hom ≫
        W ◁ (rescaledAssociator P a X Y Z).hom =
      (rescaledAssociator P a (W ⊗ X) Y Z).hom ≫
        (rescaledAssociator P a W X (Y ⊗ Z)).hom := by
  simpa only [FourCocycle.twist, ha, div_self', Units.val_one, one_smul] using
    rescaledAssociator_pentagon_defect L P ω hω a W X Y Z

/-- Genuine monoidal structure obtained from actual homogeneous tensor
maps by cancelling their actual pentagon defect. -/
def correctedMonoidalCategory (ω : FourCocycle G ℂˣ)
    (hω : HasPentagonDefect P ω) (a : ThreeCochain G ℂˣ)
    (ha : ∀ g h k l, dThree a.val g h k l = ω.val g h k l) : MonoidalCategory C := by
  have hp := rescaledAssociator_pentagon L P ω hω a ha
  have hc := rescaledCoherence T L P a
  let corrected := rescaledStruct P a
  letI := corrected
  exact
    { toMonoidalCategoryStruct := corrected
      tensorHom_def := hc.tensorHom_def
      id_tensorHom_id := hc.id_tensorHom_id
      tensorHom_comp_tensorHom := hc.tensorHom_comp_tensorHom
      whiskerLeft_id := hc.whiskerLeft_id
      id_whiskerRight := hc.id_whiskerRight
      associator_naturality := hc.associator_naturality
      leftUnitor_naturality := hc.leftUnitor_naturality
      rightUnitor_naturality := hc.rightUnitor_naturality
      pentagon := hp
      triangle := hc.triangle }

/-- The corrected actual tensor product remains additive in both variables. -/
def correctedMonoidalPreadditive (ω : FourCocycle G ℂˣ)
    (hω : HasPentagonDefect P ω) (a : ThreeCochain G ℂˣ)
    (ha : ∀ g h k l, dThree a.val g h k l = ω.val g h k l) :
    letI := correctedMonoidalCategory T L P ω hω a ha
    MonoidalPreadditive C := by
  have hL0 : ∀ {X Y Z : C}, X ◁ (0 : Y ⟶ Z) = 0 := L.whiskerLeft_zero
  have hR0 : ∀ {X Y Z : C}, (0 : Y ⟶ Z) ▷ X = 0 := L.zero_whiskerRight
  have hLa : ∀ {X Y Z : C} (f g : Y ⟶ Z), X ◁ (f + g) = X ◁ f + X ◁ g := L.whiskerLeft_add
  have hRa : ∀ {X Y Z : C} (f g : Y ⟶ Z), (f + g) ▷ X = f ▷ X + g ▷ X := L.add_whiskerRight
  let corrected := correctedMonoidalCategory T L P ω hω a ha
  letI := corrected
  exact
    { whiskerLeft_zero := hL0
      zero_whiskerRight := hR0
      whiskerLeft_add := hLa
      add_whiskerRight := hRa }

/-- The corrected actual tensor product remains complex linear. -/
def correctedMonoidalLinear (ω : FourCocycle G ℂˣ)
    (hω : HasPentagonDefect P ω) (a : ThreeCochain G ℂˣ)
    (ha : ∀ g h k l, dThree a.val g h k l = ω.val g h k l) :
    letI := correctedMonoidalCategory T L P ω hω a ha
    letI := correctedMonoidalPreadditive T L P ω hω a ha
    MonoidalLinear ℂ C := by
  have hLs := L.whiskerLeft_smul
  have hRs := L.smul_whiskerRight
  let corrected := correctedMonoidalCategory T L P ω hω a ha
  have pp := correctedMonoidalPreadditive T L P ω hω a ha
  letI := corrected
  letI := pp
  exact { whiskerLeft_smul := hLs, smul_whiskerRight := hRs }

end Paper18.Category.GradedQuasiCancellation
