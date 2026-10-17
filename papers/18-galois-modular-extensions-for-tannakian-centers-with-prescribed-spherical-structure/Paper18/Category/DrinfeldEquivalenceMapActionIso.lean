import Paper18.Category.DrinfeldEquivalenceMapAction
import Paper18.Category.WeakActionQuotientMonoidal

/-! # Actual weak-action isomorphisms lifted to Drinfeld centers -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
universe v u w
namespace Paper18.Category.DrinfeldEquivalence
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {Γ : Type w} [Group Γ] {A B : WeakAction Γ C}
  [∀ g, (A.ρ g).Monoidal] [A.IsMonoidal]
  [∀ g, (B.ρ g).Monoidal] [B.IsMonoidal]
  (i : WeakAction.ActionIso A B) [i.IsMonoidal]

/-- An actual monoidal isomorphism of actions lifts componentwise to
an actual isomorphism of the constructed braided center actions. -/
def centerActionIso : WeakAction.ActionIso (centerAction A) (centerAction B) where
  iso g := mapNatIso (i.iso g)
  unit Z := by
    apply Center.Hom.ext
    simpa using i.unit Z.1
  mul g h Z := by
    apply Center.Hom.ext
    simpa using i.mul g h Z.1

instance centerActionIso_monoidal : (centerActionIso i).IsMonoidal where
  iso_monoidal g := inferInstanceAs (NatTrans.IsMonoidal (mapNatIso (i.iso g)).hom)

@[simp] lemma centerActionIso_iso_hom_app_f (g : Γ) (Z : Center C) :
    (((centerActionIso i).iso g).hom.app Z).f = (i.iso g).hom.app Z.1 := rfl

end Paper18.Category.DrinfeldEquivalence
