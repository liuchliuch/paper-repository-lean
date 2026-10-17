import Paper18.Category.PointedRelativeCenterObstructionTensorHexagon

/-! # Mixed-pentagon associativity of the relative tensor crossing -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
namespace Paper18.Category.PointedRelativeCenterObstruction
open FiniteCohomologyKilling QuasiFusion

section IsoRotations
variable {C : Type*} [Category C] {A B C' D E : C}
  (a : A ≅ B) (b : B ≅ C') (c : C' ≅ D) (d : A ≅ E) (e : E ≅ D)
  (h : a.hom ≫ b.hom ≫ c.hom = d.hom ≫ e.hom)
include h
lemma tensorCoherence_rotate_pair : e.hom ≫ c.inv = d.inv ≫ a.hom ≫ b.hom := by
  have hh := congrArg (fun k => d.inv ≫ k ≫ c.inv) h
  simpa only [assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id, comp_id] using hh.symm
lemma tensorCoherence_rotate_triple :
    b.hom ≫ c.hom ≫ e.inv = a.inv ≫ d.hom := by
  have hh := congrArg (fun k => a.inv ≫ k ≫ e.inv) h
  simpa only [assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id, comp_id] using hh
end IsoRotations

variable {Γ G : Type} [Group Γ] [Fintype Γ] [Group G]
  (p : Γ →* G) (ψ : ThreeCochain Γ ℂˣ) (ω : FourCocycle G ℂˣ)
local notation "Vec" => PointedVec (Additive Γ)

@[reassoc] lemma quasiAssociator_naturality_middle_hex (X Z : Vec)
    {Y Y' : Vec} (f : Y ⟶ Y') :
    (X ◁ f) ▷ Z ≫ (quasiAssociator ψ X Y' Z).hom =
      (quasiAssociator ψ X Y Z).hom ≫ X ◁ (f ▷ Z) := by
  simpa only [tensorHom_id, id_tensorHom] using
    quasiAssociator_naturality ψ (𝟙 X) f (𝟙 Z)

variable (hψ : ∀ a b c d, dThree ψ.val a b c d = ω.val (p a) (p b) (p c) (p d))
include hψ

@[reassoc] lemma quasiAssociator_mixed_rotate_pair
    {g0 g1 g2 g3 : G} (W X Y Z : Vec)
    (hW : Supported p g0 W) (hX : Supported p g1 X)
    (hY : Supported p g2 Y) (hZ : Supported p g3 Z)
    (hn : g0 = 1 ∨ g1 = 1 ∨ g2 = 1 ∨ g3 = 1) :
    (quasiAssociator ψ W X (Y ⊗ Z)).hom ≫ W ◁ (quasiAssociator ψ X Y Z).inv =
      (quasiAssociator ψ (W ⊗ X) Y Z).inv ≫
        (quasiAssociator ψ W X Y).hom ▷ Z ≫ (quasiAssociator ψ W (X ⊗ Y) Z).hom :=
  tensorCoherence_rotate_pair
    (whiskerRightIso (quasiAssociator ψ W X Y) Z)
    (quasiAssociator ψ W (X ⊗ Y) Z)
    (whiskerLeftIso W (quasiAssociator ψ X Y Z))
    (quasiAssociator ψ (W ⊗ X) Y Z) (quasiAssociator ψ W X (Y ⊗ Z))
    (quasiAssociator_mixed_pentagon p ψ ω hψ W X Y Z hW hX hY hZ hn)

@[reassoc] lemma quasiAssociator_mixed_rotate_triple
    {g0 g1 g2 g3 : G} (W X Y Z : Vec)
    (hW : Supported p g0 W) (hX : Supported p g1 X)
    (hY : Supported p g2 Y) (hZ : Supported p g3 Z)
    (hn : g0 = 1 ∨ g1 = 1 ∨ g2 = 1 ∨ g3 = 1) :
    (quasiAssociator ψ W (X ⊗ Y) Z).hom ≫ W ◁ (quasiAssociator ψ X Y Z).hom ≫
        (quasiAssociator ψ W X (Y ⊗ Z)).inv =
      (quasiAssociator ψ W X Y).inv ▷ Z ≫ (quasiAssociator ψ (W ⊗ X) Y Z).hom :=
  tensorCoherence_rotate_triple
    (whiskerRightIso (quasiAssociator ψ W X Y) Z)
    (quasiAssociator ψ W (X ⊗ Y) Z)
    (whiskerLeftIso W (quasiAssociator ψ X Y Z))
    (quasiAssociator ψ (W ⊗ X) Y Z) (quasiAssociator ψ W X (Y ⊗ Z))
    (quasiAssociator_mixed_pentagon p ψ ω hψ W X Y Z hW hX hY hZ hn)

/-- The actual four-strand associator/crossing word. All four pentagons
have the same neutral strand U. The three crossings are arbitrary maps. -/
lemma tensorCoherence_associator_word {gX gY gZ : G} (X Y Z U : Vec)
    (hX : Supported p gX X) (hY : Supported p gY Y)
    (hZ : Supported p gZ Z) (hU : Supported p 1 U)
    (f : X ⊗ U ⟶ U ⊗ X) (g : Y ⊗ U ⟶ U ⊗ Y) (h : Z ⊗ U ⟶ U ⊗ Z) :
    (quasiAssociator ψ X Y Z).hom ▷ U ≫
      (quasiAssociator ψ X (Y ⊗ Z) U).hom ≫
      X ◁ ((quasiAssociator ψ Y Z U).hom ≫ Y ◁ h ≫
        (quasiAssociator ψ Y U Z).inv ≫ g ▷ Z ≫ (quasiAssociator ψ U Y Z).hom) ≫
      (quasiAssociator ψ X U (Y ⊗ Z)).inv ≫ f ▷ (Y ⊗ Z) ≫
      (quasiAssociator ψ U X (Y ⊗ Z)).hom =
    (quasiAssociator ψ (X ⊗ Y) Z U).hom ≫ (X ⊗ Y) ◁ h ≫
      (quasiAssociator ψ (X ⊗ Y) U Z).inv ≫
      ((quasiAssociator ψ X Y U).hom ≫ X ◁ g ≫
        (quasiAssociator ψ X U Y).inv ≫ f ▷ Y ≫ (quasiAssociator ψ U X Y).hom) ▷ Z ≫
      (quasiAssociator ψ U (X ⊗ Y) Z).hom ≫ U ◁ (quasiAssociator ψ X Y Z).hom := by
  simp only [whiskerLeft_comp, comp_whiskerRight, assoc]
  have hp := quasiAssociator_mixed_pentagon p ψ ω hψ X Y Z U hX hY hZ hU
    (Or.inr (Or.inr (Or.inr rfl)))
  rw [reassoc_of% hp]
  rw [← quasiAssociator_naturality_right_assoc ψ X Y h]
  rw [quasiAssociator_mixed_rotate_pair_assoc p ψ ω hψ X Y U Z hX hY hU hZ
    (Or.inr (Or.inr (Or.inl rfl)))]
  rw [← quasiAssociator_naturality_middle_hex_assoc ψ X Z g]
  rw [quasiAssociator_mixed_rotate_triple_assoc p ψ ω hψ X U Y Z hX hU hY hZ
    (Or.inr (Or.inl rfl))]
  rw [← quasiAssociator_naturality_left_assoc ψ Y Z f]
  rw [← quasiAssociator_mixed_pentagon p ψ ω hψ U X Y Z hU hX hY hZ (Or.inl rfl)]

end Paper18.Category.PointedRelativeCenterObstruction
