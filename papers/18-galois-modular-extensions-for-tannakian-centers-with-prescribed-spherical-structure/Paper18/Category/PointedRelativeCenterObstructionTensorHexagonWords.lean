import Paper18.Category.PointedRelativeCenterObstructionTensorHexagonBasic

/-! # The two actual four-strand tensor-hexagon words

Each normalization uses only three mixed pentagons on the four actual
objects X,Y,U,V. The two neutral strands remain visible in every use.
-/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
namespace Paper18.Category.PointedRelativeCenterObstruction
open FiniteCohomologyKilling QuasiFusion
variable {Γ G : Type} [Group Γ] [Fintype Γ] [Group G]
  (p : Γ →* G) (ψ : ThreeCochain Γ ℂˣ) (ω : FourCocycle G ℂˣ)
local notation "Vec" => PointedVec (Additive Γ)
local notation "a" => quasiAssociator ψ

def tensorHexagon_leftWord (X Y U V : Vec)
    (s : Y ⊗ U ⟶ U ⊗ Y) (t : Y ⊗ V ⟶ V ⊗ Y)
    (f : X ⊗ U ⟶ U ⊗ X) (g : X ⊗ V ⟶ V ⊗ X) :
    X ⊗ (Y ⊗ (U ⊗ V)) ⟶ U ⊗ (V ⊗ (X ⊗ Y)) :=
  X ◁ ((a Y U V).inv ≫ s ▷ V ≫ (a U Y V).hom ≫ U ◁ t ≫ (a U V Y).inv) ≫
    (a X (U ⊗ V) Y).inv ≫
      ((a X U V).inv ≫ f ▷ V ≫ (a U X V).hom ≫ U ◁ g ≫ (a U V X).inv) ▷ Y ≫
        (a (U ⊗ V) X Y).hom ≫ (a U V (X ⊗ Y)).hom

def tensorHexagon_leftNormal (X Y U V : Vec)
    (s : Y ⊗ U ⟶ U ⊗ Y) (t : Y ⊗ V ⟶ V ⊗ Y)
    (f : X ⊗ U ⟶ U ⊗ X) (g : X ⊗ V ⟶ V ⊗ X) :
    X ⊗ (Y ⊗ (U ⊗ V)) ⟶ U ⊗ (V ⊗ (X ⊗ Y)) :=
  X ◁ (a Y U V).inv ≫ X ◁ (s ▷ V) ≫ X ◁ (a U Y V).hom ≫
    X ◁ U ◁ t ≫ (a X U (V ⊗ Y)).inv ≫ f ▷ (V ⊗ Y) ≫ (a U X (V ⊗ Y)).hom ≫
      U ◁ (a X V Y).inv ≫ U ◁ (g ▷ Y) ≫ U ◁ (a V X Y).hom

def tensorHexagon_rightWord (X Y U V : Vec)
    (s : Y ⊗ U ⟶ U ⊗ Y) (t : Y ⊗ V ⟶ V ⊗ Y)
    (f : X ⊗ U ⟶ U ⊗ X) (g : X ⊗ V ⟶ V ⊗ X) :
    X ⊗ (Y ⊗ (U ⊗ V)) ⟶ U ⊗ (V ⊗ (X ⊗ Y)) :=
  (a X Y (U ⊗ V)).inv ≫ (a (X ⊗ Y) U V).inv ≫
    ((a X Y U).hom ≫ X ◁ s ≫ (a X U Y).inv ≫ f ▷ Y ≫ (a U X Y).hom) ▷ V ≫
      (a U (X ⊗ Y) V).hom ≫
        U ◁ ((a X Y V).hom ≫ X ◁ t ≫ (a X V Y).inv ≫ g ▷ Y ≫ (a V X Y).hom)

def tensorHexagon_rightNormal (X Y U V : Vec)
    (s : Y ⊗ U ⟶ U ⊗ Y) (t : Y ⊗ V ⟶ V ⊗ Y)
    (f : X ⊗ U ⟶ U ⊗ X) (g : X ⊗ V ⟶ V ⊗ X) :
    X ⊗ (Y ⊗ (U ⊗ V)) ⟶ U ⊗ (V ⊗ (X ⊗ Y)) :=
  X ◁ (a Y U V).inv ≫ X ◁ (s ▷ V) ≫ X ◁ (a U Y V).hom ≫
    (a X U (Y ⊗ V)).inv ≫ f ▷ (Y ⊗ V) ≫ (a U X (Y ⊗ V)).hom ≫
      U ◁ X ◁ t ≫ U ◁ (a X V Y).inv ≫ U ◁ (g ▷ Y) ≫ U ◁ (a V X Y).hom

variable (hψ : ∀ a0 b0 c0 d0, dThree ψ.val a0 b0 c0 d0 = ω.val (p a0) (p b0) (p c0) (p d0))
include hψ

lemma tensorHexagon_leftWord_normal {gX gY : G} (X Y U V : Vec)
    (hX : Supported p gX X) (hY : Supported p gY Y)
    (hU : Supported p 1 U) (hV : Supported p 1 V)
    (s : Y ⊗ U ⟶ U ⊗ Y) (t : Y ⊗ V ⟶ V ⊗ Y)
    (f : X ⊗ U ⟶ U ⊗ X) (g : X ⊗ V ⟶ V ⊗ X) : tensorHexagon_leftWord ψ X Y U V s t f g =
    tensorHexagon_leftNormal ψ X Y U V s t f g := by
  unfold tensorHexagon_leftWord tensorHexagon_leftNormal
  simp only [whiskerLeft_comp, comp_whiskerRight, assoc]
  rw [quasiAssociator_mixed_pentagon_inv_hex_assoc p ψ ω hψ X U V Y hX hU hV hY
    (Or.inr (Or.inl rfl))]
  rw [← quasiAssociator_inv_naturality_left_hex_assoc ψ V Y f]
  rw [quasiAssociator_mixed_rotate_middle_assoc p ψ ω hψ U X V Y hU hX hV hY (Or.inl rfl)]
  rw [← quasiAssociator_inv_naturality_middle_assoc ψ U Y g]
  rw [quasiAssociator_mixed_rotate_end p ψ ω hψ U V X Y hU hV hX hY (Or.inl rfl)]

lemma tensorHexagon_rightWord_normal {gX gY : G} (X Y U V : Vec)
    (hX : Supported p gX X) (hY : Supported p gY Y)
    (hU : Supported p 1 U) (hV : Supported p 1 V)
    (s : Y ⊗ U ⟶ U ⊗ Y) (t : Y ⊗ V ⟶ V ⊗ Y)
    (f : X ⊗ U ⟶ U ⊗ X) (g : X ⊗ V ⟶ V ⊗ X) : tensorHexagon_rightWord ψ X Y U V s t f g =
    tensorHexagon_rightNormal ψ X Y U V s t f g := by
  unfold tensorHexagon_rightWord tensorHexagon_rightNormal
  simp only [whiskerLeft_comp, comp_whiskerRight, assoc]
  rw [quasiAssociator_mixed_rotate_middle_assoc p ψ ω hψ X Y U V hX hY hU hV
    (Or.inr (Or.inr (Or.inl rfl))), Iso.inv_hom_id_assoc]
  rw [← quasiAssociator_inv_naturality_middle_assoc ψ X V s]
  rw [quasiAssociator_mixed_rotate_start_assoc p ψ ω hψ X U Y V hX hU hY hV
    (Or.inr (Or.inl rfl))]
  rw [← quasiAssociator_inv_naturality_left_hex_assoc ψ Y V f]
  have hp := quasiAssociator_mixed_pentagon p ψ ω hψ U X Y V hU hX hY hV (Or.inl rfl)
  rw [reassoc_of% hp, Iso.inv_hom_id_assoc]

/-- The actual four-strand interchange closes after precisely the six
mixed pentagons above; no global cochain pentagon is used. -/
lemma tensorHexagon_words {gX gY : G} (X Y U V : Vec)
    (hX : Supported p gX X) (hY : Supported p gY Y)
    (hU : Supported p 1 U) (hV : Supported p 1 V)
    (s : Y ⊗ U ⟶ U ⊗ Y) (t : Y ⊗ V ⟶ V ⊗ Y)
    (f : X ⊗ U ⟶ U ⊗ X) (g : X ⊗ V ⟶ V ⊗ X) : tensorHexagon_leftWord ψ X Y U V s t f g =
    tensorHexagon_rightWord ψ X Y U V s t f g := by
  rw [tensorHexagon_leftWord_normal p ψ ω hψ X Y U V hX hY hU hV s t f g,
    tensorHexagon_rightWord_normal p ψ ω hψ X Y U V hX hY hU hV s t f g]
  unfold tensorHexagon_leftNormal tensorHexagon_rightNormal
  rw [tensorHexagon_disjoint_assoc]

end Paper18.Category.PointedRelativeCenterObstruction
