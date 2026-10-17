import Paper18.Category.GraphPicardMoritaImageBasic
import Paper18.Category.FusionSubcategoryRigid

/-! # Actual tensor and dual closure of the genuine summand image -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
universe v u w v' u'
namespace Paper18.Category.GraphPicard.MoritaImage
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [HasFiniteBiproducts C] [MonoidalCategory C]
  {D : Type u'} [Category.{v'} D] [Preadditive D] [Linear ℂ D]
  [HasFiniteBiproducts D] [MonoidalCategory D]
  (F : C ⥤ D) [F.Additive] [F.Linear ℂ] [F.Monoidal]

instance property_monoidal : (property F).IsMonoidal where
  prop_unit := ⟨𝟙_ C, ⟨Retract.ofIso (Functor.Monoidal.εIso F)⟩⟩
  prop_tensor X Y hX hY := by
    obtain ⟨U, ⟨r⟩⟩ := hX
    obtain ⟨V, ⟨s⟩⟩ := hY
    let t : Retract (X ⊗ Y) (F.obj U ⊗ F.obj V) :=
      { i := r.i ⊗ₘ s.i
        r := r.r ⊗ₘ s.r
        retract := by rw [tensorHom_comp_tensorHom, r.retract, s.retract]; simp }
    exact ⟨U ⊗ V, ⟨t.trans (Retract.ofIso (Functor.Monoidal.μIso F U V))⟩⟩

/-- The actual corestriction has the actual original strong tensorators. -/
instance core_monoidal : (core F).Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := (property F).isoMk (Functor.Monoidal.εIso F)
      μIso X Y := (property F).isoMk (Functor.Monoidal.μIso F X Y)
      μIso_hom_natural_left f Y := Functor.LaxMonoidal.μ_natural_left F f Y
      μIso_hom_natural_right X f := Functor.LaxMonoidal.μ_natural_right F X f
      associativity X Y Z := Functor.LaxMonoidal.associativity F X Y Z
      left_unitality X := Functor.LaxMonoidal.left_unitality F X
      right_unitality X := Functor.LaxMonoidal.right_unitality F X }

variable [HasKernels D] [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalPreadditive D] [MonoidalLinear ℂ D] [RightRigidCategory D] [Simple (𝟙_ D)]
  {κ : Type w} [Fintype κ] (T : FiniteSemisimpleSkeleton D κ)

/-- Actual dual closure follows from actual tensor/summand closure. -/
def rightRigid : RightRigidCategory (Image F) := T.fullSubcategoryRightRigid (property F)

/-- The actual unit remains simple in the actual tensor image. -/
def simpleUnit : Simple (𝟙_ (Image F)) := T.fullSubcategorySimpleUnit (property F)

end Paper18.Category.GraphPicard.MoritaImage
