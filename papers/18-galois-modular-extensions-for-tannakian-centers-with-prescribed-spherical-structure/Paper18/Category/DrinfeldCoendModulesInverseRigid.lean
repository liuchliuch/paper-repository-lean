import Paper18.Category.DrinfeldRigidLax
import Mathlib.CategoryTheory.Monoidal.Opposite

/-! # Rigidity makes a coherent inverse-oriented crossing invertible -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalOpposite
universe v u
namespace Paper18.Category.DrinfeldCoendModules
variable {D : Type u} [Category.{v} D] [MonoidalCategory D]

/-- The inverse orientation of a lax half-braiding. This generic helper
will be populated from the actual module laws, not supplied to the inverse functor. -/
structure RightLaxHalfBraiding (M : D) where
  hom : ∀ U : D, U ⊗ M ⟶ M ⊗ U
  naturality : ∀ {U V : D} (f : U ⟶ V), f ▷ M ≫ hom V = hom U ≫ M ◁ f
  monoidal (U V : D) : hom (U ⊗ V) =
    (α_ U V M).hom ≫ U ◁ hom V ≫ (α_ U M V).inv ≫ hom U ▷ V ≫ (α_ M U V).hom
  unit : hom (𝟙_ D) = (λ_ M).hom ≫ (ρ_ M).inv

namespace RightLaxHalfBraiding
variable {M : D} (b : RightLaxHalfBraiding M)

/-- Reversing the tensor factors turns the inverse orientation into an
ordinary lax half-braiding. -/
def mopLax : Drinfeld.LaxHalfBraiding (mop M) where
  hom U := (b.hom U.unmop).mop
  naturality f := by
    apply Quiver.Hom.unmop_inj
    exact b.naturality f.unmop
  monoidal U V := by
    apply Quiver.Hom.unmop_inj
    exact b.monoidal V.unmop U.unmop
  unit := by
    apply Quiver.Hom.unmop_inj
    exact b.unit

variable [RightRigidCategory D]
attribute [local instance 2000] RightRigidCategory.rightDual

/-- The actual chosen right pairing becomes an actual left pairing in
the reversed tensor category. -/
def reversedPair (U : D) : ExactPairing (mop (Uᘁ)) (mop U) where
  coevaluation' := (η_ U (Uᘁ)).mop
  evaluation' := (ε_ U (Uᘁ)).mop
  coevaluation_evaluation' := by
    apply Quiver.Hom.unmop_inj
    exact ExactPairing.evaluation_coevaluation U (Uᘁ)
  evaluation_coevaluation' := by
    apply Quiver.Hom.unmop_inj
    exact ExactPairing.coevaluation_evaluation U (Uᘁ)

/-- Rigidity constructs both inverse identities; invertibility is not a
field in the recovered crossing data. -/
def crossingIso (U : D) : U ⊗ M ≅ M ⊗ U := by
  letI := reversedPair U
  letI : HasLeftDual (mop U) := ⟨mop (Uᘁ)⟩
  letI := b.mopLax.hom_isIso (mop U)
  exact (asIso (b.mopLax.hom (mop U))).unmop

@[simp] lemma crossingIso_hom (U : D) : (b.crossingIso U).hom = b.hom U := rfl

/-- Reversing the constructed crossing yields an actual half-braiding. -/
def toHalfBraiding : HalfBraiding M where
  β U := (b.crossingIso U).symm
  naturality f := by
    apply (cancel_epi (b.crossingIso _).hom).mp
    simp only [Iso.symm_hom, Iso.hom_inv_id_assoc]
    rw [b.crossingIso_hom, ← reassoc_of% (b.naturality f),
      ← b.crossingIso_hom, Iso.hom_inv_id, comp_id]
  monoidal U V := by
    have he : b.crossingIso (U ⊗ V) =
        α_ U V M ≪≫ whiskerLeftIso U (b.crossingIso V) ≪≫
          (α_ U M V).symm ≪≫ whiskerRightIso (b.crossingIso U) V ≪≫ α_ M U V := by
      apply Iso.ext
      simpa only [Iso.trans_hom, Iso.symm_hom, whiskerLeftIso_hom,
        whiskerRightIso_hom, crossingIso_hom] using b.monoidal U V
    have hi := congrArg Iso.inv he
    simpa only [Iso.symm_hom, Iso.trans_inv, Iso.symm_inv, whiskerLeftIso_inv,
      whiskerRightIso_inv, assoc] using hi

end RightLaxHalfBraiding
end Paper18.Category.DrinfeldCoendModules
