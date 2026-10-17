import Paper18.Category.PointedRelativeCenterObstructionTensorBasic
import Paper18.Category.PointedRelativeCenterObstructionPentagon

/-! # Finite mixed-pentagon rotations for the relative tensor hexagon -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
namespace Paper18.Category.PointedRelativeCenterObstruction
open FiniteCohomologyKilling QuasiFusion

section IsoRotations
variable {C : Type*} [Category C] {A B C' D E : C}
  (a : A ≅ B) (b : B ≅ C') (c : C' ≅ D) (d : A ≅ E) (e : E ≅ D)
  (h : a.hom ≫ b.hom ≫ c.hom = d.hom ≫ e.hom)
include h

lemma tensorHexagon_rotate_start : b.inv ≫ a.inv = c.hom ≫ e.inv ≫ d.inv := by
  have hi : (a ≪≫ b ≪≫ c) = d ≪≫ e := Iso.ext (by
    simpa only [Iso.trans_hom, assoc] using h)
  have hh : c.inv ≫ b.inv ≫ a.inv = e.inv ≫ d.inv := by
    simpa only [Iso.trans_inv, assoc] using congrArg Iso.inv hi
  calc
    b.inv ≫ a.inv = c.hom ≫ (c.inv ≫ b.inv ≫ a.inv) := by simp
    _ = _ := by rw [hh]

lemma tensorHexagon_rotate_middle : d.inv ≫ a.hom = e.hom ≫ c.inv ≫ b.inv := by
  calc
    d.inv ≫ a.hom = d.inv ≫ (a.hom ≫ b.hom ≫ c.hom) ≫ c.inv ≫ b.inv := by simp
    _ = d.inv ≫ (d.hom ≫ e.hom) ≫ c.inv ≫ b.inv := by rw [h]
    _ = _ := by simp
end IsoRotations

variable {Γ G : Type} [Group Γ] [Fintype Γ] [Group G] (p : Γ →* G)
  (ψ : ThreeCochain Γ ℂˣ) (ω : FourCocycle G ℂˣ)
local notation "V" => PointedVec (Additive Γ)

@[reassoc] lemma quasiAssociator_inv_naturality_left_hex (Y Z : V)
    {X X' : V} (f : X ⟶ X') :
    f ▷ (Y ⊗ Z) ≫ (quasiAssociator ψ X' Y Z).inv =
      (quasiAssociator ψ X Y Z).inv ≫ (f ▷ Y) ▷ Z := by
  simpa only [id_tensorHom_id, tensorHom_id, id_whiskerRight] using
    quasiAssociator_inv_naturality ψ f (𝟙 Y) (𝟙 Z)

@[reassoc] lemma quasiAssociator_inv_naturality_right_hex (X Y : V)
    {Z Z' : V} (f : Z ⟶ Z') :
    X ◁ Y ◁ f ≫ (quasiAssociator ψ X Y Z').inv =
      (quasiAssociator ψ X Y Z).inv ≫ (X ⊗ Y) ◁ f := by
  simpa only [id_tensorHom_id, id_tensorHom, whiskerLeft_id] using
    quasiAssociator_inv_naturality ψ (𝟙 X) (𝟙 Y) f

/-- Disjoint actual crossings commute after actual rebracketing. This
uses only associator naturality and tensor interchange. -/
@[reassoc] lemma tensorHexagon_disjoint {X U Y Z : V}
    (f : X ⊗ U ⟶ U ⊗ X) (g : Y ⊗ Z ⟶ Z ⊗ Y) :
    X ◁ U ◁ g ≫ (quasiAssociator ψ X U (Z ⊗ Y)).inv ≫
        f ▷ (Z ⊗ Y) ≫ (quasiAssociator ψ U X (Z ⊗ Y)).hom =
      (quasiAssociator ψ X U (Y ⊗ Z)).inv ≫ f ▷ (Y ⊗ Z) ≫
        (quasiAssociator ψ U X (Y ⊗ Z)).hom ≫ U ◁ X ◁ g := by
  rw [quasiAssociator_inv_naturality_right_hex_assoc,
    whisker_exchange_assoc, quasiAssociator_naturality_right]

variable (hψ : ∀ a b c d, dThree ψ.val a b c d = ω.val (p a) (p b) (p c) (p d))
include hψ

@[reassoc] lemma quasiAssociator_mixed_rotate_start
    {g0 g1 g2 g3 : G} (W X Y Z : V)
    (hW : Supported p g0 W) (hX : Supported p g1 X)
    (hY : Supported p g2 Y) (hZ : Supported p g3 Z)
    (hn : g0 = 1 ∨ g1 = 1 ∨ g2 = 1 ∨ g3 = 1) :
    (quasiAssociator ψ W (X ⊗ Y) Z).inv ≫ (quasiAssociator ψ W X Y).inv ▷ Z =
      W ◁ (quasiAssociator ψ X Y Z).hom ≫
        (quasiAssociator ψ W X (Y ⊗ Z)).inv ≫ (quasiAssociator ψ (W ⊗ X) Y Z).inv :=
  tensorHexagon_rotate_start
    (whiskerRightIso (quasiAssociator ψ W X Y) Z)
    (quasiAssociator ψ W (X ⊗ Y) Z)
    (whiskerLeftIso W (quasiAssociator ψ X Y Z))
    (quasiAssociator ψ (W ⊗ X) Y Z) (quasiAssociator ψ W X (Y ⊗ Z))
    (quasiAssociator_mixed_pentagon p ψ ω hψ W X Y Z hW hX hY hZ hn)

@[reassoc] lemma quasiAssociator_mixed_rotate_middle
    {g0 g1 g2 g3 : G} (W X Y Z : V)
    (hW : Supported p g0 W) (hX : Supported p g1 X)
    (hY : Supported p g2 Y) (hZ : Supported p g3 Z)
    (hn : g0 = 1 ∨ g1 = 1 ∨ g2 = 1 ∨ g3 = 1) :
    (quasiAssociator ψ (W ⊗ X) Y Z).inv ≫ (quasiAssociator ψ W X Y).hom ▷ Z =
      (quasiAssociator ψ W X (Y ⊗ Z)).hom ≫
        W ◁ (quasiAssociator ψ X Y Z).inv ≫ (quasiAssociator ψ W (X ⊗ Y) Z).inv :=
  tensorHexagon_rotate_middle
    (whiskerRightIso (quasiAssociator ψ W X Y) Z)
    (quasiAssociator ψ W (X ⊗ Y) Z)
    (whiskerLeftIso W (quasiAssociator ψ X Y Z))
    (quasiAssociator ψ (W ⊗ X) Y Z) (quasiAssociator ψ W X (Y ⊗ Z))
    (quasiAssociator_mixed_pentagon p ψ ω hψ W X Y Z hW hX hY hZ hn)

@[reassoc] lemma quasiAssociator_mixed_pentagon_inv_hex
    {g0 g1 g2 g3 : G} (W X Y Z : V)
    (hW : Supported p g0 W) (hX : Supported p g1 X)
    (hY : Supported p g2 Y) (hZ : Supported p g3 Z)
    (hn : g0 = 1 ∨ g1 = 1 ∨ g2 = 1 ∨ g3 = 1) :
    W ◁ (quasiAssociator ψ X Y Z).inv ≫
        (quasiAssociator ψ W (X ⊗ Y) Z).inv ≫ (quasiAssociator ψ W X Y).inv ▷ Z =
      (quasiAssociator ψ W X (Y ⊗ Z)).inv ≫ (quasiAssociator ψ (W ⊗ X) Y Z).inv := by
  rw [quasiAssociator_mixed_rotate_start p ψ ω hψ W X Y Z hW hX hY hZ hn]
  rw [← whiskerLeft_comp_assoc, Iso.inv_hom_id, whiskerLeft_id, id_comp]

@[reassoc] lemma quasiAssociator_mixed_rotate_end
    {g0 g1 g2 g3 : G} (W X Y Z : V)
    (hW : Supported p g0 W) (hX : Supported p g1 X)
    (hY : Supported p g2 Y) (hZ : Supported p g3 Z)
    (hn : g0 = 1 ∨ g1 = 1 ∨ g2 = 1 ∨ g3 = 1) :
    (quasiAssociator ψ W (X ⊗ Y) Z).inv ≫ (quasiAssociator ψ W X Y).inv ▷ Z ≫
        (quasiAssociator ψ (W ⊗ X) Y Z).hom ≫ (quasiAssociator ψ W X (Y ⊗ Z)).hom =
      W ◁ (quasiAssociator ψ X Y Z).hom := by
  rw [quasiAssociator_mixed_rotate_start_assoc p ψ ω hψ W X Y Z hW hX hY hZ hn]
  simp only [assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, comp_id]

end Paper18.Category.PointedRelativeCenterObstruction
