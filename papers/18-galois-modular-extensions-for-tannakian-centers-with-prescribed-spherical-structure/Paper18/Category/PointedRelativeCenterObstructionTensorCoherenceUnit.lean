import Paper18.Category.PointedRelativeCenterObstructionTensorCoherenceAssociator
import Paper18.Category.PointedRelativeCenterObstructionNeutral
import Mathlib.CategoryTheory.Monoidal.Center

/-! # The actual unit relative half-braiding and its unitors -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
namespace Paper18.Category.PointedRelativeCenterObstruction
open FiniteCohomologyKilling QuasiFusion GradedObject.Monoidal
variable {Γ G : Type} [Group Γ] [Fintype Γ] [Group G]
  (p : Γ →* G) (ψ : ThreeCochain Γ ℂˣ) (ω : FourCocycle G ℂˣ)
local notation "Vec" => PointedVec (Additive Γ)

lemma quasiAssociator_unit_left (X Y : Vec) :
    quasiAssociator ψ (𝟙_ Vec) X Y = α_ (𝟙_ Vec) X Y := by
  apply Iso.ext
  change tripleScalar (fun a b c : Additive Γ =>
      (ψ.val a.toMul b.toMul c.toMul : ℂ)) (𝟙_ Vec) X Y ≫ (α_ _ _ _).hom = _
  suffices hh : tripleScalar (fun a b c : Additive Γ =>
      (ψ.val a.toMul b.toMul c.toMul : ℂ)) (𝟙_ Vec) X Y = 𝟙 _ by rw [hh, id_comp]
  apply GradedObject.hom_ext
  intro k
  apply tensorObj₃'_ext (X₁ := (𝟙_ Vec)) (X₂ := X) (X₃ := Y)
  intro a b c h
  change ιTensorObj₃' (𝟙_ Vec) X Y a b c k h ≫ _ =
    ιTensorObj₃' (𝟙_ Vec) X Y a b c k h ≫ 𝟙 _
  rw [inclusion_tripleScalar, comp_id]
  by_cases ha : a = 0
  · subst a
    rw [toMul_zero, ψ.one₁, Units.val_one, one_smul]
  · have hu : IsZero ((𝟙_ Vec) a) := (isInitialTensorUnitApply a ha).isZero
    have hz : IsZero (((𝟙_ Vec) a ⊗ X b) ⊗ Y c) :=
      (tensorRight (Y c)).map_isZero ((tensorRight (X b)).map_isZero hu)
    rw [hz.eq_of_src (ιTensorObj₃' (𝟙_ Vec) X Y a b c k h) 0, smul_zero]

lemma quasiAssociator_unit_middle (X Y : Vec) :
    quasiAssociator ψ X (𝟙_ Vec) Y = α_ X (𝟙_ Vec) Y := by
  apply Iso.ext
  change tripleScalar (fun a b c : Additive Γ =>
      (ψ.val a.toMul b.toMul c.toMul : ℂ)) X (𝟙_ Vec) Y ≫ (α_ _ _ _).hom = _
  rw [tripleScalar_middle_unit]
  · exact id_comp _
  · intro a c
    rw [toMul_zero, ψ.one₂, Units.val_one]

lemma quasiAssociator_unit_right (X Y : Vec) :
    quasiAssociator ψ X Y (𝟙_ Vec) = α_ X Y (𝟙_ Vec) := by
  apply Iso.ext
  change tripleScalar (fun a b c : Additive Γ =>
      (ψ.val a.toMul b.toMul c.toMul : ℂ)) X Y (𝟙_ Vec) ≫ (α_ _ _ _).hom = _
  suffices hh : tripleScalar (fun a b c : Additive Γ =>
      (ψ.val a.toMul b.toMul c.toMul : ℂ)) X Y (𝟙_ Vec) = 𝟙 _ by rw [hh, id_comp]
  apply GradedObject.hom_ext
  intro k
  apply tensorObj₃'_ext (X₁ := X) (X₂ := Y) (X₃ := (𝟙_ Vec))
  intro a b c h
  change ιTensorObj₃' X Y (𝟙_ Vec) a b c k h ≫ _ =
    ιTensorObj₃' X Y (𝟙_ Vec) a b c k h ≫ 𝟙 _
  rw [inclusion_tripleScalar, comp_id]
  by_cases hc : c = 0
  · subst c
    rw [toMul_zero, ψ.one₃, Units.val_one, one_smul]
  · have hu : IsZero ((𝟙_ Vec) c) := (isInitialTensorUnitApply c hc).isZero
    have hz : IsZero ((X a ⊗ Y b) ⊗ (𝟙_ Vec) c) :=
      (tensorLeft (X a ⊗ Y b)).map_isZero hu
    rw [hz.eq_of_src (ιTensorObj₃' X Y (𝟙_ Vec) a b c k h) 0, smul_zero]

/-- The genuine monoidal neutral category supplies the actual unit crossing;
its underlying morphisms are the convolution unitors. -/
def unitRelativeHalfBraiding
    (hψ : ∀ a b c d, dThree ψ.val a b c d = ω.val (p a) (p b) (p c) (p d)) :
    RelativeHalfBraiding p ψ (𝟙_ Vec) := by
  letI := neutralMonoidalCategory p ψ ω hψ
  let e : Center (NeutralVec p) := 𝟙_ (Center (NeutralVec p))
  exact {
    β U hU := λ_ U ≪≫ (ρ_ U).symm
    monoidal U V hU hV := e.2.monoidal ⟨U, hU⟩ ⟨V, hV⟩
    naturality hU hV f := by
      simp only [Iso.trans_hom, Iso.symm_hom]
      rw [MonoidalCategory.leftUnitor_naturality_assoc,
        MonoidalCategory.rightUnitor_inv_naturality, assoc] }

@[simp] lemma unitRelativeHalfBraiding_β
    (hψ : ∀ a b c d, dThree ψ.val a b c d = ω.val (p a) (p b) (p c) (p d))
    (U : Vec) (hU : Supported p 1 U) :
    (unitRelativeHalfBraiding p ψ ω hψ).β U hU = λ_ U ≪≫ (ρ_ U).symm := rfl


@[reassoc] lemma tensorRelativeIso_leftUnitor
    (hψ : ∀ a b c d, dThree ψ.val a b c d = ω.val (p a) (p b) (p c) (p d))
    {X : Vec} (x : RelativeHalfBraiding p ψ X) (U : Vec) (hU : Supported p 1 U) :
    (λ_ X).hom ▷ U ≫ (x.β U hU).hom =
      (tensorRelativeIso p ψ (unitRelativeHalfBraiding p ψ ω hψ) x U hU).hom ≫
        U ◁ (λ_ X).hom := by
  dsimp only [tensorRelativeIso, Iso.trans_hom, Iso.symm_hom,
    whiskerLeftIso_hom, whiskerRightIso_hom]
  rw [quasiAssociator_unit_left, quasiAssociator_unit_left, quasiAssociator_unit_middle,
    unitRelativeHalfBraiding_β]
  dsimp only [Iso.trans_hom, Iso.symm_hom]
  monoidal

@[reassoc] lemma tensorRelativeIso_rightUnitor
    (hψ : ∀ a b c d, dThree ψ.val a b c d = ω.val (p a) (p b) (p c) (p d))
    {X : Vec} (x : RelativeHalfBraiding p ψ X) (U : Vec) (hU : Supported p 1 U) :
    (ρ_ X).hom ▷ U ≫ (x.β U hU).hom =
      (tensorRelativeIso p ψ x (unitRelativeHalfBraiding p ψ ω hψ) U hU).hom ≫
        U ◁ (ρ_ X).hom := by
  dsimp only [tensorRelativeIso, Iso.trans_hom, Iso.symm_hom,
    whiskerLeftIso_hom, whiskerRightIso_hom]
  rw [quasiAssociator_unit_middle, quasiAssociator_unit_right, quasiAssociator_unit_right,
    unitRelativeHalfBraiding_β]
  dsimp only [Iso.trans_hom, Iso.symm_hom]
  monoidal

end Paper18.Category.PointedRelativeCenterObstruction
