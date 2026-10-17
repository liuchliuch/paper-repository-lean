import Paper18.Category.PointedRelativeCenterObstructionBasic

/-! # The actual candidate tensor half-braiding and its naturality -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
namespace Paper18.Category.PointedRelativeCenterObstruction
open FiniteCohomologyKilling QuasiFusion
variable {Γ G : Type} [Group Γ] [Fintype Γ] [Group G] (p : Γ →* G)
  (ψ : ThreeCochain Γ ℂˣ)
local notation "V" => PointedVec (Additive Γ)

@[reassoc] lemma quasiAssociator_naturality {X Y Z X' Y' Z' : V}
    (f : X ⟶ X') (g : Y ⟶ Y') (h : Z ⟶ Z') :
    ((f ⊗ₘ g) ⊗ₘ h) ≫ (quasiAssociator ψ X' Y' Z').hom =
      (quasiAssociator ψ X Y Z).hom ≫ (f ⊗ₘ (g ⊗ₘ h)) :=
  scalarAssociator_naturality
    (fun a b c : Additive Γ => ψ.val a.toMul b.toMul c.toMul) f g h

@[reassoc] lemma quasiAssociator_inv_naturality {X Y Z X' Y' Z' : V}
    (f : X ⟶ X') (g : Y ⟶ Y') (h : Z ⟶ Z') :
    (f ⊗ₘ (g ⊗ₘ h)) ≫ (quasiAssociator ψ X' Y' Z').inv =
      (quasiAssociator ψ X Y Z).inv ≫ ((f ⊗ₘ g) ⊗ₘ h) := by
  have hh := congrArg (fun t => (quasiAssociator ψ X Y Z).inv ≫ t ≫
    (quasiAssociator ψ X' Y' Z').inv) (quasiAssociator_naturality ψ f g h)
  simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id, Category.comp_id] using hh.symm

@[reassoc] lemma quasiAssociator_naturality_right (X Y : V) {U W : V} (f : U ⟶ W) :
    (X ⊗ Y) ◁ f ≫ (quasiAssociator ψ X Y W).hom =
      (quasiAssociator ψ X Y U).hom ≫ X ◁ Y ◁ f := by
  simpa only [id_tensorHom_id, id_tensorHom, whiskerLeft_id] using
    quasiAssociator_naturality ψ (𝟙 X) (𝟙 Y) f

@[reassoc] lemma quasiAssociator_inv_naturality_middle (X Y : V) {U W : V} (f : U ⟶ W) :
    X ◁ (f ▷ Y) ≫ (quasiAssociator ψ X W Y).inv =
      (quasiAssociator ψ X U Y).inv ≫ (X ◁ f) ▷ Y := by
  simpa only [tensorHom_id, id_tensorHom] using
    quasiAssociator_inv_naturality ψ (𝟙 X) f (𝟙 Y)

@[reassoc] lemma quasiAssociator_naturality_left (X Y : V) {U W : V} (f : U ⟶ W) :
    (f ▷ X) ▷ Y ≫ (quasiAssociator ψ W X Y).hom =
      (quasiAssociator ψ U X Y).hom ≫ f ▷ (X ⊗ Y) := by
  simpa only [id_tensorHom_id, tensorHom_id, id_whiskerRight] using
    quasiAssociator_naturality ψ f (𝟙 X) (𝟙 Y)

/-- The actual tensor crossing formed from actual relative half-braidings
and the actual cochain associator. Its hexagon is proved separately. -/
def tensorRelativeIso {X Y : V} (x : RelativeHalfBraiding p ψ X)
    (y : RelativeHalfBraiding p ψ Y) (U : V) (hU : Supported p 1 U) :
    (X ⊗ Y) ⊗ U ≅ U ⊗ (X ⊗ Y) :=
  quasiAssociator ψ X Y U ≪≫ whiskerLeftIso X (y.β U hU) ≪≫
    (quasiAssociator ψ X U Y).symm ≪≫ whiskerRightIso (x.β U hU) Y ≪≫
      quasiAssociator ψ U X Y

@[reassoc] lemma tensorRelativeIso_naturality {X Y : V} (x : RelativeHalfBraiding p ψ X)
    (y : RelativeHalfBraiding p ψ Y) {U W : V} (hU : Supported p 1 U)
    (hW : Supported p 1 W) (f : U ⟶ W) :
    (X ⊗ Y) ◁ f ≫ (tensorRelativeIso p ψ x y W hW).hom =
      (tensorRelativeIso p ψ x y U hU).hom ≫ f ▷ (X ⊗ Y) := by
  dsimp only [tensorRelativeIso, Iso.trans_hom, Iso.symm_hom,
    whiskerLeftIso_hom, whiskerRightIso_hom]
  simp only [Category.assoc]
  rw [quasiAssociator_naturality_right_assoc,
    ← whiskerLeft_comp_assoc, y.naturality hU hW f, whiskerLeft_comp_assoc,
    quasiAssociator_inv_naturality_middle_assoc,
    ← comp_whiskerRight_assoc, x.naturality hU hW f, comp_whiskerRight_assoc,
    quasiAssociator_naturality_left]

end Paper18.Category.PointedRelativeCenterObstruction
