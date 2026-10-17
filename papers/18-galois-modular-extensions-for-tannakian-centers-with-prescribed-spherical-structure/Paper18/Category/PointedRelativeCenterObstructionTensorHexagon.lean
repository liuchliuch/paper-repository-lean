import Paper18.Category.PointedRelativeCenterObstructionTensorHexagonWords

/-! # Tensor closure of actual supported relative half-braidings

The tensor hexagon follows from six mixed pentagons, each with a neutral
strand. No pentagon on four arbitrary nonneutral objects is used.
-/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
namespace Paper18.Category.PointedRelativeCenterObstruction
open FiniteCohomologyKilling QuasiFusion
variable {Γ G : Type} [Group Γ] [Fintype Γ] [Group G]
  (p : Γ →* G) (ψ : ThreeCochain Γ ℂˣ) (ω : FourCocycle G ℂˣ)
  (hψ : ∀ a b c d, dThree ψ.val a b c d = ω.val (p a) (p b) (p c) (p d))
local notation "Vec" => PointedVec (Additive Γ)
include hψ

/-- The actual tensor crossing satisfies the relative half-braiding
hexagon whenever its two factors have homogeneous quotient support. -/
lemma tensorRelativeIso_monoidal {gX gY : G} {X Y : Vec}
    (hX : Supported p gX X) (hY : Supported p gY Y)
    (x : RelativeHalfBraiding p ψ X) (y : RelativeHalfBraiding p ψ Y)
    (U V : Vec) (hU : Supported p 1 U) (hV : Supported p 1 V) :
    (tensorRelativeIso p ψ x y (U ⊗ V)
      (by simpa only [one_mul] using supported_tensor p hU hV)).hom =
      (quasiAssociator ψ (X ⊗ Y) U V).inv ≫
        (tensorRelativeIso p ψ x y U hU).hom ▷ V ≫
          (quasiAssociator ψ U (X ⊗ Y) V).hom ≫
            U ◁ (tensorRelativeIso p ψ x y V hV).hom ≫
              (quasiAssociator ψ U V (X ⊗ Y)).inv := by
  apply (cancel_epi (quasiAssociator ψ X Y (U ⊗ V)).inv).mp
  apply (cancel_mono (quasiAssociator ψ U V (X ⊗ Y)).hom).mp
  dsimp only [tensorRelativeIso, Iso.trans_hom, Iso.symm_hom,
    whiskerLeftIso_hom, whiskerRightIso_hom]
  rw [x.monoidal U V hU hV, y.monoidal U V hU hV]
  simpa only [assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, comp_id] using
    tensorHexagon_words p ψ ω hψ X Y U V hX hY hU hV
      (y.β U hU).hom (y.β V hV).hom (x.β U hU).hom (x.β V hV).hom

/-- Actual tensor closure of supported relative half-braidings. The
hexagon is derived from the cochain coboundary equation and the normalized
quotient four-cocycle, rather than supplied as a coherence field. -/
def tensorRelativeHalfBraiding {gX gY : G} {X Y : Vec}
    (hX : Supported p gX X) (hY : Supported p gY Y)
    (x : RelativeHalfBraiding p ψ X) (y : RelativeHalfBraiding p ψ Y) :
    RelativeHalfBraiding p ψ (X ⊗ Y) where
  β := tensorRelativeIso p ψ x y
  monoidal := tensorRelativeIso_monoidal p ψ ω hψ hX hY x y
  naturality := tensorRelativeIso_naturality p ψ x y

@[simp] lemma tensorRelativeHalfBraiding_β {gX gY : G} {X Y : Vec}
    (hX : Supported p gX X) (hY : Supported p gY Y)
    (x : RelativeHalfBraiding p ψ X) (y : RelativeHalfBraiding p ψ Y)
    (U : Vec) (hU : Supported p 1 U) :
    (tensorRelativeHalfBraiding p ψ ω hψ hX hY x y).β U hU =
      tensorRelativeIso p ψ x y U hU := rfl

end Paper18.Category.PointedRelativeCenterObstruction
