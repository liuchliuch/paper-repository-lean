import Paper18.Category.PointedRelativeCenterObstructionTensorCoherenceBasic

/-! # Actual morphisms of tensor relative half-braidings -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
namespace Paper18.Category.PointedRelativeCenterObstruction
open FiniteCohomologyKilling QuasiFusion
variable {Γ G : Type} [Group Γ] [Fintype Γ] [Group G]
  (p : Γ →* G) (ψ : ThreeCochain Γ ℂˣ)
local notation "Vec" => PointedVec (Additive Γ)

@[reassoc] lemma tensorRelativeIso_map_left {X X' Y : Vec}
    (x : RelativeHalfBraiding p ψ X) (x' : RelativeHalfBraiding p ψ X')
    (y : RelativeHalfBraiding p ψ Y) (f : X ⟶ X')
    (U : Vec) (hU : Supported p 1 U)
    (hf : f ▷ U ≫ (x'.β U hU).hom = (x.β U hU).hom ≫ U ◁ f) :
    (f ▷ Y) ▷ U ≫ (tensorRelativeIso p ψ x' y U hU).hom =
      (tensorRelativeIso p ψ x y U hU).hom ≫ U ◁ (f ▷ Y) := by
  dsimp only [tensorRelativeIso, Iso.trans_hom, Iso.symm_hom,
    whiskerLeftIso_hom, whiskerRightIso_hom]
  simp only [assoc]
  rw [quasiAssociator_naturality_left_assoc,
    ← whisker_exchange_assoc, quasiAssociator_inv_naturality_left_hex_assoc,
    ← comp_whiskerRight_assoc, hf, comp_whiskerRight_assoc,
    quasiAssociator_naturality_middle_hex]

@[reassoc] lemma tensorRelativeIso_map_right {X Y Y' : Vec}
    (x : RelativeHalfBraiding p ψ X) (y : RelativeHalfBraiding p ψ Y)
    (y' : RelativeHalfBraiding p ψ Y') (g : Y ⟶ Y')
    (U : Vec) (hU : Supported p 1 U)
    (hg : g ▷ U ≫ (y'.β U hU).hom = (y.β U hU).hom ≫ U ◁ g) :
    (X ◁ g) ▷ U ≫ (tensorRelativeIso p ψ x y' U hU).hom =
      (tensorRelativeIso p ψ x y U hU).hom ≫ U ◁ (X ◁ g) := by
  dsimp only [tensorRelativeIso, Iso.trans_hom, Iso.symm_hom,
    whiskerLeftIso_hom, whiskerRightIso_hom]
  simp only [assoc]
  rw [quasiAssociator_naturality_middle_hex_assoc,
    ← whiskerLeft_comp_assoc, hg, whiskerLeft_comp_assoc,
    quasiAssociator_inv_naturality_right_hex_assoc, whisker_exchange_assoc,
    quasiAssociator_naturality_right]

/-- Tensoring actual relative-central morphisms gives an actual relative-central
morphism; only naturality and tensor interchange enter this proof. -/
@[reassoc] lemma tensorRelativeIso_map {X X' Y Y' : Vec}
    (x : RelativeHalfBraiding p ψ X) (x' : RelativeHalfBraiding p ψ X')
    (y : RelativeHalfBraiding p ψ Y) (y' : RelativeHalfBraiding p ψ Y')
    (f : X ⟶ X') (g : Y ⟶ Y') (U : Vec) (hU : Supported p 1 U)
    (hf : f ▷ U ≫ (x'.β U hU).hom = (x.β U hU).hom ≫ U ◁ f)
    (hg : g ▷ U ≫ (y'.β U hU).hom = (y.β U hU).hom ≫ U ◁ g) :
    (f ⊗ₘ g) ▷ U ≫ (tensorRelativeIso p ψ x' y' U hU).hom =
      (tensorRelativeIso p ψ x y U hU).hom ≫ U ◁ (f ⊗ₘ g) := by
  rw [tensorHom_def, comp_whiskerRight, assoc,
    tensorRelativeIso_map_right p ψ x' y y' g U hU hg,
    tensorRelativeIso_map_left_assoc p ψ x x' y f U hU hf,
    ← whiskerLeft_comp]

end Paper18.Category.PointedRelativeCenterObstruction
