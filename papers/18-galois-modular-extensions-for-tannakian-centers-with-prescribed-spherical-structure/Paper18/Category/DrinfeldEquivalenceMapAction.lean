import Paper18.Category.DrinfeldEquivalenceMapLinear
import Paper18.Category.EquivariantMonoidal

/-! # Actual weak monoidal group actions transported to Drinfeld centers -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
universe v u w
namespace Paper18.Category.DrinfeldEquivalence
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {Γ : Type w} [Group Γ] (A : WeakAction Γ C)
  [∀ g, (A.ρ g).Monoidal] [A.IsMonoidal]

@[simp] lemma center_eqToHom_f {Z W : Center C} (h : Z = W) :
    (eqToHom h).f = eqToHom (congrArg Sigma.fst h) := by cases h; rfl

/-- A weak monoidal action lifts to the Drinfeld center using the
actual induced center functors and their actual comparison maps. -/
def centerAction : WeakAction Γ (Center C) where
  ρ g := map (A.ρ g)
  unitIso := mapNatIso A.unitIso ≪≫ identityIso C
  mulIso g h := compositionIso (A.ρ h) (A.ρ g) ≪≫ mapNatIso (A.mulIso g h)
  assoc g h k Z := by
    apply Center.Hom.ext
    simpa using A.assoc g h k Z.1
  one_mul g Z := by
    apply Center.Hom.ext
    simpa using A.one_mul g Z.1
  mul_one g Z := by
    apply Center.Hom.ext
    simpa using A.mul_one g Z.1

instance centerAction_rho_monoidal (g : Γ) : ((centerAction A).ρ g).Monoidal :=
  inferInstanceAs (map (A.ρ g)).Monoidal

instance centerAction_rho_braided (g : Γ) : ((centerAction A).ρ g).Braided :=
  inferInstanceAs (map (A.ρ g)).Braided

instance centerAction_isMonoidal : (centerAction A).IsMonoidal where
  unit_monoidal := by
    change NatTrans.IsMonoidal (mapNatIso A.unitIso ≪≫ identityIso C).hom
    infer_instance
  mul_monoidal g h := by
    change NatTrans.IsMonoidal
      ((compositionIso (A.ρ h) (A.ρ g)).hom ≫ (mapNatIso (A.mulIso g h)).hom)
    infer_instance

@[simp] lemma centerAction_rho_obj_fst (g : Γ) (Z : Center C) :
    (((centerAction A).ρ g).obj Z).1 = (A.ρ g).obj Z.1 := rfl

@[simp] lemma centerAction_rho_map_f (g : Γ) {Z W : Center C} (f : Z ⟶ W) :
    (((centerAction A).ρ g).map f).f = (A.ρ g).map f.f := rfl

@[simp] lemma centerAction_unit_hom_app_f (Z : Center C) :
    ((centerAction A).unitIso.hom.app Z).f = A.unitIso.hom.app Z.1 := by
  change A.unitIso.hom.app Z.1 ≫ 𝟙 _ = _
  exact comp_id _

@[simp] lemma centerAction_mul_hom_app_f (g h : Γ) (Z : Center C) :
    (((centerAction A).mulIso g h).hom.app Z).f = (A.mulIso g h).hom.app Z.1 := by
  change 𝟙 _ ≫ (A.mulIso g h).hom.app Z.1 = _
  exact id_comp _

section Linear
variable [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]

instance centerAction_rho_additive [∀ g, (A.ρ g).Additive] (g : Γ) :
    ((centerAction A).ρ g).Additive :=
  inferInstanceAs (map (A.ρ g)).Additive

instance centerAction_rho_linear [∀ g, (A.ρ g).Additive] [∀ g, (A.ρ g).Linear ℂ] (g : Γ) :
    ((centerAction A).ρ g).Linear ℂ :=
  inferInstanceAs ((map (A.ρ g)).Linear ℂ)
end Linear

end Paper18.Category.DrinfeldEquivalence
