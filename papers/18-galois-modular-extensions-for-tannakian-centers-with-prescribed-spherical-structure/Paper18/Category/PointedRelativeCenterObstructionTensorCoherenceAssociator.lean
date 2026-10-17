import Paper18.Category.PointedRelativeCenterObstructionTensorCoherenceMorphisms

/-! # The actual quasi-associator intertwines relative tensor crossings -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
namespace Paper18.Category.PointedRelativeCenterObstruction
open FiniteCohomologyKilling QuasiFusion
variable {Γ G : Type} [Group Γ] [Fintype Γ] [Group G]
  (p : Γ →* G) (ψ : ThreeCochain Γ ℂˣ) (ω : FourCocycle G ℂˣ)
  (hψ : ∀ a b c d, dThree ψ.val a b c d = ω.val (p a) (p b) (p c) (p d))
local notation "Vec" => PointedVec (Additive Γ)
include hψ

@[reassoc] lemma tensorRelativeIso_associator {gX gY gZ : G} {X Y Z : Vec}
    (hX : Supported p gX X) (hY : Supported p gY Y) (hZ : Supported p gZ Z)
    (x : RelativeHalfBraiding p ψ X) (y : RelativeHalfBraiding p ψ Y)
    (z : RelativeHalfBraiding p ψ Z) (U : Vec) (hU : Supported p 1 U) :
    (quasiAssociator ψ X Y Z).hom ▷ U ≫
      (tensorRelativeIso p ψ x
        (tensorRelativeHalfBraiding p ψ ω hψ hY hZ y z) U hU).hom =
      (tensorRelativeIso p ψ
        (tensorRelativeHalfBraiding p ψ ω hψ hX hY x y) z U hU).hom ≫
          U ◁ (quasiAssociator ψ X Y Z).hom := by
  simpa only [tensorRelativeIso, tensorRelativeHalfBraiding_β,
    Iso.trans_hom, Iso.symm_hom, whiskerLeftIso_hom, whiskerRightIso_hom, assoc] using
    tensorCoherence_associator_word p ψ ω hψ X Y Z U hX hY hZ hU
      (x.β U hU).hom (y.β U hU).hom (z.β U hU).hom

end Paper18.Category.PointedRelativeCenterObstruction
