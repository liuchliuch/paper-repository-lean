import Paper18.Category.RelativeCenterBasic

/-! # Actual monoidal structure and strict forgetful functor for the relative center -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
universe v u
namespace Paper18.Category.RelativeCenter
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {P : ObjectProperty C} [P.IsMonoidal]

/-- Auxiliary definition for the `MonoidalCategory` instance on `RelativeCenter P`. -/
@[simps]
def tensorObj (X Y : RelativeCenter P) : RelativeCenter P :=
  ⟨X.1 ⊗ Y.1,
    { β := fun U hU =>
        α_ _ _ _ ≪≫
          (whiskerLeftIso X.1 (Y.2.β U hU)) ≪≫ (α_ _ _ _).symm ≪≫
            (whiskerRightIso (X.2.β U hU) Y.1) ≪≫ α_ _ _ _
      monoidal := fun U U' hU hU' => by
        dsimp only [Iso.trans_hom, whiskerLeftIso_hom, Iso.symm_hom, whiskerRightIso_hom]
        rw [Y.2.monoidal U U' hU hU', X.2.monoidal U U' hU hU']
        -- We'd like to commute `X.1 ◁ U ◁ (RelativeHalfBraiding.β Y.2 U' hU').hom`
        -- and `((RelativeHalfBraiding.β X.2 U hU).hom ▷ U' ▷ Y.1)` past each other.
        -- We do this with the help of the monoidal composition `⊗≫` and the `coherence` tactic.
        calc
          _ = 𝟙 _ ⊗≫
            X.1 ◁ (RelativeHalfBraiding.β Y.2 U hU).hom ▷ U' ⊗≫
              (_ ◁ (RelativeHalfBraiding.β Y.2 U' hU').hom ≫
                (RelativeHalfBraiding.β X.2 U hU).hom ▷ _) ⊗≫
                  U ◁ (RelativeHalfBraiding.β X.2 U' hU').hom ▷ Y.1 ⊗≫ 𝟙 _ := by monoidal
          _ = _ := by rw [whisker_exchange]; monoidal
      naturality := fun {U U'} hU hU' f => by
        dsimp only [Iso.trans_hom, whiskerLeftIso_hom, Iso.symm_hom, whiskerRightIso_hom]
        calc
          _ = 𝟙 _ ⊗≫
            (X.1 ◁ (Y.1 ◁ f ≫ (RelativeHalfBraiding.β Y.2 U' hU').hom)) ⊗≫
              (RelativeHalfBraiding.β X.2 U' hU').hom ▷ Y.1 ⊗≫ 𝟙 _ := by monoidal
          _ = 𝟙 _ ⊗≫
            X.1 ◁ (RelativeHalfBraiding.β Y.2 U hU).hom ⊗≫
              (X.1 ◁ f ≫ (RelativeHalfBraiding.β X.2 U' hU').hom) ▷ Y.1 ⊗≫ 𝟙 _ := by
            rw [Y.2.naturality hU hU' f]; monoidal
          _ = _ := by rw [X.2.naturality hU hU' f]; monoidal }⟩

@[reassoc]
theorem whiskerLeft_comm (X : RelativeCenter P) {Y₁ Y₂ : RelativeCenter P} (f : Y₁ ⟶ Y₂) (U : C) (hU : P U) :
    (X.1 ◁ f.f) ▷ U ≫ ((tensorObj X Y₂).2.β U hU).hom =
      ((tensorObj X Y₁).2.β U hU).hom ≫ U ◁ X.1 ◁ f.f := by
  dsimp only [tensorObj_fst, tensorObj_snd_β, Iso.trans_hom, whiskerLeftIso_hom,
    Iso.symm_hom, whiskerRightIso_hom]
  calc
    _ = 𝟙 _ ⊗≫
      X.fst ◁ (f.f ▷ U ≫ (RelativeHalfBraiding.β Y₂.snd U hU).hom) ⊗≫
        (RelativeHalfBraiding.β X.snd U hU).hom ▷ Y₂.fst ⊗≫ 𝟙 _ := by monoidal
    _ = 𝟙 _ ⊗≫
      X.fst ◁ (RelativeHalfBraiding.β Y₁.snd U hU).hom ⊗≫
        ((X.fst ⊗ U) ◁ f.f ≫ (RelativeHalfBraiding.β X.snd U hU).hom ▷ Y₂.fst) ⊗≫ 𝟙 _ := by
      rw [f.comm U hU]; monoidal
    _ = _ := by rw [whisker_exchange]; monoidal

/-- Auxiliary definition for the `MonoidalCategory` instance on `RelativeCenter P`. -/
def whiskerLeft (X : RelativeCenter P) {Y₁ Y₂ : RelativeCenter P} (f : Y₁ ⟶ Y₂) :
    tensorObj X Y₁ ⟶ tensorObj X Y₂ where
  f := X.1 ◁ f.f
  comm U hU := whiskerLeft_comm X f U hU

@[reassoc]
theorem whiskerRight_comm {X₁ X₂ : RelativeCenter P} (f : X₁ ⟶ X₂) (Y : RelativeCenter P) (U : C) (hU : P U) :
    f.f ▷ Y.1 ▷ U ≫ ((tensorObj X₂ Y).2.β U hU).hom =
      ((tensorObj X₁ Y).2.β U hU).hom ≫ U ◁ f.f ▷ Y.1 := by
  dsimp only [tensorObj_fst, tensorObj_snd_β, Iso.trans_hom, whiskerLeftIso_hom,
    Iso.symm_hom, whiskerRightIso_hom]
  calc
    _ = 𝟙 _ ⊗≫
      (f.f ▷ (Y.fst ⊗ U) ≫ X₂.fst ◁ (RelativeHalfBraiding.β Y.snd U hU).hom) ⊗≫
        (RelativeHalfBraiding.β X₂.snd U hU).hom ▷ Y.fst ⊗≫ 𝟙 _ := by monoidal
    _ = 𝟙 _ ⊗≫
      X₁.fst ◁ (RelativeHalfBraiding.β Y.snd U hU).hom ⊗≫
        (f.f ▷ U ≫ (RelativeHalfBraiding.β X₂.snd U hU).hom) ▷ Y.fst ⊗≫ 𝟙 _ := by
      rw [← whisker_exchange]; monoidal
    _ = _ := by rw [f.comm U hU]; monoidal

/-- Auxiliary definition for the `MonoidalCategory` instance on `RelativeCenter P`. -/
def whiskerRight {X₁ X₂ : RelativeCenter P} (f : X₁ ⟶ X₂) (Y : RelativeCenter P) :
    tensorObj X₁ Y ⟶ tensorObj X₂ Y where
  f := f.f ▷ Y.1
  comm U hU := whiskerRight_comm f Y U hU

/-- Auxiliary definition for the `MonoidalCategory` instance on `RelativeCenter P`. -/
@[simps]
def tensorHom {X₁ Y₁ X₂ Y₂ : RelativeCenter P} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    tensorObj X₁ X₂ ⟶ tensorObj Y₁ Y₂ where
  f := f.f ⊗ₘ g.f
  comm U hU := by
    rw [tensorHom_def, comp_whiskerRight_assoc, whiskerLeft_comm (hU := hU), whiskerRight_comm_assoc (hU := hU),
      MonoidalCategory.whiskerLeft_comp]

section

/-- Auxiliary definition for the `MonoidalCategory` instance on `RelativeCenter P`. -/
@[simps]
def tensorUnit : RelativeCenter P :=
  ⟨𝟙_ C, { β := fun U _ => λ_ U ≪≫ (ρ_ U).symm }⟩

/-- Auxiliary definition for the `MonoidalCategory` instance on `RelativeCenter P`. -/
def associator (X Y Z : RelativeCenter P) : tensorObj (tensorObj X Y) Z ≅ tensorObj X (tensorObj Y Z) :=
  isoMk P ⟨(α_ X.1 Y.1 Z.1).hom, fun U hU => by simp⟩

/-- Auxiliary definition for the `MonoidalCategory` instance on `RelativeCenter P`. -/
def leftUnitor (X : RelativeCenter P) : tensorObj tensorUnit X ≅ X :=
  isoMk P ⟨(λ_ X.1).hom, fun U hU => by simp⟩

/-- Auxiliary definition for the `MonoidalCategory` instance on `RelativeCenter P`. -/
def rightUnitor (X : RelativeCenter P) : tensorObj X tensorUnit ≅ X :=
  isoMk P ⟨(ρ_ X.1).hom, fun U hU => by simp⟩

end

section

attribute [local simp] associator_naturality leftUnitor_naturality rightUnitor_naturality pentagon

attribute [local simp] RelativeCenter.associator RelativeCenter.leftUnitor RelativeCenter.rightUnitor

attribute [local simp] RelativeCenter.whiskerLeft RelativeCenter.whiskerRight RelativeCenter.tensorHom

instance : MonoidalCategory (RelativeCenter P) where
  tensorObj X Y := tensorObj X Y
  tensorHom f g := tensorHom f g
  tensorHom_def := by intros; ext; simp [tensorHom_def]
  whiskerLeft X _ _ f := whiskerLeft X f
  whiskerRight f Y := whiskerRight f Y
  tensorUnit := tensorUnit
  associator := associator
  leftUnitor := leftUnitor
  rightUnitor := rightUnitor
  associator_naturality := by intros; apply ext P; simp [isoMk]
  leftUnitor_naturality := by intros; apply ext P; simp [isoMk]
  rightUnitor_naturality := by intros; apply ext P; simp [isoMk]
  pentagon := by intros; apply ext P; simp [isoMk]
  triangle := by intros; apply ext P; simp [isoMk]

@[simp]
theorem tensor_fst (X Y : RelativeCenter P) : (X ⊗ Y).1 = X.1 ⊗ Y.1 :=
  rfl

@[simp]
theorem tensor_β (X Y : RelativeCenter P) (U : C) (hU : P U) :
    (X ⊗ Y).2.β U hU =
      α_ _ _ _ ≪≫
        (whiskerLeftIso X.1 (Y.2.β U hU)) ≪≫ (α_ _ _ _).symm ≪≫
          (whiskerRightIso (X.2.β U hU) Y.1) ≪≫ α_ _ _ _ :=
  rfl

@[simp]
theorem whiskerLeft_f (X : RelativeCenter P) {Y₁ Y₂ : RelativeCenter P} (f : Y₁ ⟶ Y₂) : (X ◁ f).f = X.1 ◁ f.f :=
  rfl

@[simp]
theorem whiskerRight_f {X₁ X₂ : RelativeCenter P} (f : X₁ ⟶ X₂) (Y : RelativeCenter P) : (f ▷ Y).f = f.f ▷ Y.1 :=
  rfl

@[simp]
theorem tensor_f {X₁ Y₁ X₂ Y₂ : RelativeCenter P} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) : (f ⊗ₘ g).f = f.f ⊗ₘ g.f :=
  rfl

@[simp]
theorem tensorUnit_β (U : C) (hU : P U) : (𝟙_ (RelativeCenter P)).2.β U hU = λ_ U ≪≫ (ρ_ U).symm :=
  rfl

@[simp]
theorem associator_hom_f (X Y Z : RelativeCenter P) : Hom.f (α_ X Y Z).hom = (α_ X.1 Y.1 Z.1).hom :=
  rfl

@[simp]
theorem associator_inv_f (X Y Z : RelativeCenter P) : Hom.f (α_ X Y Z).inv = (α_ X.1 Y.1 Z.1).inv := by
  apply Iso.inv_ext' -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): Originally `ext`
  rw [← associator_hom_f, ← comp_f, Iso.hom_inv_id]; rfl

@[simp]
theorem leftUnitor_hom_f (X : RelativeCenter P) : Hom.f (λ_ X).hom = (λ_ X.1).hom :=
  rfl

@[simp]
theorem leftUnitor_inv_f (X : RelativeCenter P) : Hom.f (λ_ X).inv = (λ_ X.1).inv := by
  apply Iso.inv_ext' -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): Originally `ext`
  rw [← leftUnitor_hom_f, ← comp_f, Iso.hom_inv_id]; rfl

@[simp]
theorem rightUnitor_hom_f (X : RelativeCenter P) : Hom.f (ρ_ X).hom = (ρ_ X.1).hom :=
  rfl

@[simp]
theorem rightUnitor_inv_f (X : RelativeCenter P) : Hom.f (ρ_ X).inv = (ρ_ X.1).inv := by
  apply Iso.inv_ext' -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): Originally `ext`
  rw [← rightUnitor_hom_f, ← comp_f, Iso.hom_inv_id]; rfl

end

instance forget_monoidal : (forget P).Monoidal :=
  Functor.CoreMonoidal.toMonoidal {
    εIso := Iso.refl _
    μIso := fun _ _ => Iso.refl _
    μIso_hom_natural_left := by intros; simp [forget]
    μIso_hom_natural_right := by intros; simp [forget]
    associativity := by intros; simp [forget]
    left_unitality := by intros; simp [forget]
    right_unitality := by intros; simp [forget] }

@[simp] lemma forget_ε : Functor.LaxMonoidal.ε (forget P) = 𝟙 (𝟙_ C) := rfl
@[simp] lemma forget_μ (X Y : RelativeCenter P) :
    Functor.LaxMonoidal.μ (forget P) X Y = 𝟙 (X.1 ⊗ Y.1) := rfl
@[simp] lemma forget_η : Functor.OplaxMonoidal.η (forget P) = 𝟙 (𝟙_ C) := rfl
@[simp] lemma forget_δ (X Y : RelativeCenter P) :
    Functor.OplaxMonoidal.δ (forget P) X Y = 𝟙 (X.1 ⊗ Y.1) := rfl

/-- Restriction preserves the actual tensor and unit with identity underlying maps. -/
instance restriction_monoidal : (restriction P).Monoidal :=
  Functor.CoreMonoidal.toMonoidal {
    εIso := Iso.refl _
    μIso := fun _ _ => Iso.refl _
    μIso_hom_natural_left := by intros; apply ext P; simp [restriction]
    μIso_hom_natural_right := by intros; apply ext P; simp [restriction]
    associativity := by intros; apply ext P; simp [restriction]
    left_unitality := by intros; apply ext P; simp [restriction]
    right_unitality := by intros; apply ext P; simp [restriction] }

end Paper18.Category.RelativeCenter
