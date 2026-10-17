import Paper18.Category.RepresentationBasic
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! # Actual inflation from a quotient group and its essential image -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
namespace Paper18.Category.TannakianSignKernel
variable {G : Type} [Group G] (N : Subgroup G) [N.Normal]

/-- The actual representation pullback along the quotient homomorphism. -/
def inflate : FDRep ℂ (G ⧸ N) ⥤ FDRep ℂ G :=
  Action.res (FGModuleCat ℂ) (QuotientGroup.mk' N)

instance inflate_additive : (inflate N).Additive := by dsimp [inflate]; infer_instance
instance inflate_linear : (inflate N).Linear ℂ := by dsimp [inflate]; infer_instance
instance inflate_faithful : (inflate N).Faithful := by dsimp [inflate]; infer_instance
instance inflate_full : (inflate N).Full :=
  Action.full_res (FGModuleCat ℂ) (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)

def inflateCoreMonoidal : (inflate N).CoreMonoidal where
  εIso := Iso.refl _
  μIso _ _ := Iso.refl _

instance inflate_monoidal : (inflate N).Monoidal := (inflateCoreMonoidal N).toMonoidal
instance inflate_braided : (inflate N).Braided where
  braided X Y := by
    apply Action.Hom.ext
    change 𝟙 _ ≫ (β_ X.V Y.V).hom = (β_ X.V Y.V).hom ≫ 𝟙 _
    simp

/-- The actual kernel equation of a subgroup on a finite representation. -/
def TrivialOn (V : FDRep ℂ G) : Prop := ∀ g ∈ N, V.ρ g = 1

/-- An actual representation trivial on the normal subgroup descends to an
actual finite representation of the quotient group, using its actual group
homomorphism universal property. -/
def quotientRepresentation (V : FDRep ℂ G) (hV : TrivialOn N V) : FDRep ℂ (G ⧸ N) :=
  FDRep.of (QuotientGroup.lift N V.ρ (fun g hg => hV g hg))

def inflateQuotientIso (V : FDRep ℂ G) (hV : TrivialOn N V) :
    (inflate N).obj (quotientRepresentation N V hV) ≅ V :=
  Action.mkIso (Iso.refl _) (fun g => by
    apply ModuleCat.hom_ext
    rfl)

lemma inflate_trivial (V : FDRep ℂ (G ⧸ N)) : TrivialOn N ((inflate N).obj V) := by
  intro g hg
  change V.ρ (QuotientGroup.mk' N g) = 1
  have hgq : QuotientGroup.mk' N g = 1 := (QuotientGroup.eq_one_iff g).mpr hg
  rw [hgq, map_one]

/-- The essential image of actual quotient inflation is exactly the actual
representations on which the normal subgroup acts trivially. -/
theorem inflate_image_iff (V : FDRep ℂ G) : (inflate N).essImage V ↔ TrivialOn N V := by
  constructor
  · rintro ⟨W, ⟨e⟩⟩ g hg
    rw [FDRep.Iso.conj_ρ e]
    rw [inflate_trivial N W g hg]
    apply LinearMap.ext
    intro v
    simp [LinearEquiv.conj_apply]
  · intro hV
    exact ⟨quotientRepresentation N V hV, ⟨inflateQuotientIso N V hV⟩⟩

end Paper18.Category.TannakianSignKernel
