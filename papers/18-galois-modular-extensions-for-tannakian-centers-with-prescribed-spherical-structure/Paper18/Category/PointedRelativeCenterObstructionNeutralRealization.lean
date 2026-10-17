import Paper18.Category.PointedRelativeCenterObstructionNeutralComponent
import Paper18.Category.PointedRelativeCenterObstructionNeutralCenter

/-! # Actual braided realization of the homogeneous neutral component -/
noncomputable section
set_option maxHeartbeats 2000000
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
namespace Paper18.Category.PointedRelativeCenterObstruction
open FiniteCohomologyKilling
variable {Γ G : Type} [Group Γ] [Fintype Γ] [Group G]
  (p : Γ →* G) (ψ : ThreeCochain Γ ℂˣ) (ω : FourCocycle G ℂˣ)
  (hψ : ∀ a b c d, dThree ψ.val a b c d = ω.val (p a) (p b) (p c) (p d))
namespace NeutralComponent
local notation "N" => NeutralComponent p ψ ω hψ

/-- Dropping the redundant degree-one label preserves the actual relative
half-braiding and actual neutral support. -/
def relativeObject (X : N) : NeutralRelativeObject p ψ :=
  ⟨X.obj.obj, by
    change Supported p 1 X.obj.obj.1
    have h : X.obj.degree = 1 := X.property
    rw [← h]
    exact X.obj.support⟩

/-- The homogeneous neutral component is realized in the actual Drinfeld
center of the actual cochain-neutral vector category. -/
def realization : N ⥤ Center (NeutralTwistedVec p ψ ω hψ) where
  obj X := (neutralRelativeToCenter p ψ ω hψ).obj (relativeObject p ψ ω hψ X)
  map f := ⟨f.f, fun U => f.comm U.obj U.property⟩
  map_id X := by apply Center.Hom.ext; rfl
  map_comp f g := by apply Center.Hom.ext; rfl

instance realization_faithful : (realization p ψ ω hψ).Faithful where
  map_injective := by
    intro X Y f g h
    exact RelativeObject.ext p ψ f g (congrArg Center.Hom.f h)
instance realization_full : (realization p ψ ω hψ).Full where
  map_surjective f := ⟨⟨f.f, fun U hU => f.comm ⟨U,hU⟩⟩, by apply Center.Hom.ext; rfl⟩

/-- Every actual neutral center object is realized with actual degree one. -/
def ofCenter (Z : Center (NeutralTwistedVec p ψ ω hψ)) : N :=
  let X := neutralRelativeFromCenter p ψ ω hψ Z
  ⟨⟨1, X.obj, X.property⟩, rfl⟩

instance realization_essSurj : (realization p ψ ω hψ).EssSurj where
  mem_essImage Z := ⟨ofCenter p ψ ω hψ Z,
    ⟨neutralRelativeRealizationIso p ψ ω hψ Z⟩⟩
instance realization_isEquivalence : (realization p ψ ω hψ).IsEquivalence := {}

/-- The tensorators are actual identities on convolution tensor products:
the constructed relative tensor half-braiding is exactly the center one. -/
def realizationCoreMonoidal : (realization p ψ ω hψ).CoreMonoidal where
  μIso X Y := Iso.refl _
  εIso := Iso.refl _
  μIso_hom_natural_left f Y := by
    apply Center.Hom.ext
    simp only [Iso.refl_hom, id_comp, comp_id]
    rfl
  μIso_hom_natural_right X f := by
    apply Center.Hom.ext
    simp only [Iso.refl_hom, id_comp, comp_id]
    rfl
  associativity X Y Z := by
    apply Center.Hom.ext
    simp only [Iso.refl_hom, id_whiskerRight, whiskerLeft_id, id_comp, comp_id]
    rfl
  left_unitality X := by
    apply Center.Hom.ext
    simp only [Iso.refl_hom, id_whiskerRight, id_comp]
    rfl
  right_unitality X := by
    apply Center.Hom.ext
    simp only [Iso.refl_hom, whiskerLeft_id, id_comp]
    rfl

instance realization_monoidal : (realization p ψ ω hψ).Monoidal :=
  (realizationCoreMonoidal p ψ ω hψ).toMonoidal

instance braidedCategory : BraidedCategory N :=
  BraidedCategory.ofFullyFaithful (realization p ψ ω hψ)
instance realization_braided : (realization p ψ ω hψ).Braided where
  braided X Y := by
    simp [braidedCategory, BraidedCategory.ofFullyFaithful, BraidedCategory.ofFaithful,
      Functor.Monoidal.μIso]

/-- The constructed neutral braiding is the original actual relative
half-braiding, evaluated on the other neutral object. -/
lemma braiding_hom_f (X Y : NeutralComponent p ψ ω hψ) :
    (β_ X Y).hom.f =
      (X.obj.obj.2.β Y.obj.obj.1 (relativeObject p ψ ω hψ Y).property).hom := by
  have h := Functor.LaxBraided.braided (F := realization p ψ ω hψ) X Y
  have hf := congrArg Center.Hom.f h
  change (𝟙 _ ≫ (realization p ψ ω hψ).map (β_ X Y).hom).f =
    ((β_ ((realization p ψ ω hψ).obj X)
      ((realization p ψ ω hψ).obj Y)).hom ≫ 𝟙 _).f at hf
  simp only [id_comp, comp_id] at hf
  exact hf

/-- Actual braided tensor equivalence from the actual neutral component
of the homogeneous relative center. -/
def centerEquivalence : N ≌ Center (NeutralTwistedVec p ψ ω hψ) :=
  (realization p ψ ω hψ).asEquivalence

end NeutralComponent
end Paper18.Category.PointedRelativeCenterObstruction
