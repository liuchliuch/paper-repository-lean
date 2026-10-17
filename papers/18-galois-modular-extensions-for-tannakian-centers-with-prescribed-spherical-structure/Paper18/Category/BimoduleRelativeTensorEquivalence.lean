import Paper18.Category.BimoduleRelativeTensorBasic

/-! # The actual equivalence of the two bimodule presentations -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open MonoidalOpposite
open scoped MonObj MonoidalLeftAction
universe v u
namespace Paper18.Category.BimoduleRelativeTensor
variable {D : Type u} [Category.{v} D] [MonoidalCategory D]
  (R S : D) [MonObj R] [MonObj S]
attribute [local instance] InternalModule.ambientMonoidalOppositeLeftAction

/-- The actual inverse functor, installing the two given actions as
native internal-module structures. -/
def fromBimod : Bimod (Mon.mk R) (Mon.mk S) ⥤ Native R S where
  obj := fromBimodObj R S
  map f := Mod_.Hom.mk' (Mod_.Hom.mk' f.hom f.left_act_hom) (by
    apply Mod_.Hom.ext
    exact f.right_act_hom)
  map_id _ := by apply Mod_.Hom.ext; apply Mod_.Hom.ext; rfl
  map_comp _ _ := by apply Mod_.Hom.ext; apply Mod_.Hom.ext; rfl

/-- The native roundtrip is an actual identity-underlying bimodule
isomorphism; both native action maps are unchanged. -/
def nativeRoundtripComponent (M : Native R S) :
    (fromBimod R S).obj ((toBimod R S).obj M) ≅ M where
  hom := Mod_.Hom.mk' (Mod_.Hom.mk' (𝟙 M.X.X) (by
    change γ[R,M.X.X] ≫ 𝟙 _ = R ◁ 𝟙 _ ≫ γ[R,M.X.X]
    simp only [comp_id, whiskerLeft_id, id_comp])) (by
    apply Mod_.Hom.ext
    change γ[mop S,M.X].hom ≫ 𝟙 _ = (𝟙 _ ▷ S) ≫ γ[mop S,M.X].hom
    simp)
  inv := Mod_.Hom.mk' (Mod_.Hom.mk' (𝟙 M.X.X) (by
    change γ[R,M.X.X] ≫ 𝟙 _ = R ◁ 𝟙 _ ≫ γ[R,M.X.X]
    simp only [comp_id, whiskerLeft_id, id_comp])) (by
    apply Mod_.Hom.ext
    change γ[mop S,M.X].hom ≫ 𝟙 _ = (𝟙 _ ▷ S) ≫ γ[mop S,M.X].hom
    simp)
  hom_inv_id := by apply Mod_.Hom.ext; apply Mod_.Hom.ext; exact id_comp _
  inv_hom_id := by apply Mod_.Hom.ext; apply Mod_.Hom.ext; exact id_comp _

/-- The two-sided roundtrip retains the given underlying object and both
given action maps exactly. -/
def bimodRoundtripComponent (P : Bimod (Mon.mk R) (Mon.mk S)) :
    (toBimod R S).obj ((fromBimod R S).obj P) ≅ P :=
  Bimod.isoOfIso (Iso.refl P.X) (by
    change P.actLeft ≫ 𝟙 _ = R ◁ 𝟙 _ ≫ P.actLeft
    simp only [comp_id, whiskerLeft_id, id_comp]) (by
    change P.actRight ≫ 𝟙 _ = 𝟙 _ ▷ S ≫ P.actRight
    simp only [comp_id, id_whiskerRight, id_comp])

/-- Actual native iterated modules are equivalent to actual two-sided
bimodules, without a braiding, rigidity or pivotal hypothesis. -/
def equivalence : Native R S ≌ Bimod (Mon.mk R) (Mon.mk S) :=
  CategoryTheory.Equivalence.mk (toBimod R S) (fromBimod R S)
    (NatIso.ofComponents (fun M => (nativeRoundtripComponent R S M).symm)
      (fun f => by
        apply Mod_.Hom.ext; apply Mod_.Hom.ext
        change f.hom.hom ≫ 𝟙 _ = 𝟙 _ ≫ f.hom.hom
        rw [comp_id, id_comp]))
    (NatIso.ofComponents (bimodRoundtripComponent R S)
      (fun f => by
        apply Bimod.hom_ext
        change f.hom ≫ 𝟙 _ = 𝟙 _ ≫ f.hom
        rw [comp_id, id_comp]))

end Paper18.Category.BimoduleRelativeTensor
