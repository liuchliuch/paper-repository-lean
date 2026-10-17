import Paper18.Category.BimoduleRelativeTensorMixedWattsFullyFaithful

/-! # The actual mixed-algebra Eilenberg--Watts equivalence -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits MonoidalOpposite
open scoped MonObj MonoidalLeftAction
universe v u
namespace Paper18.Category.BimoduleRelativeTensor.MixedWatts
open ModuleFunctor
variable {D : Type u} [Category.{v} D] [MonoidalCategory D]
  [HasCoequalizers D] [LeftRigidCategory D] [RightRigidCategory D]
  [Preadditive D] [Linear ℂ D] [MonoidalPreadditive D] [MonoidalLinear ℂ D]
  {R S : D} [MonObj R] [MonObj S]
attribute [local instance] InternalModule.ambientMonoidalOppositeLeftAction

lemma tensor_regular_right (P : Native R S) :
    γ[mop S,(evaluation.obj (tensorBundled P)).X] ≫ (tensorFunctorRegularIso P).hom =
      (mop S) ⊴ₗ (tensorFunctorRegularIso P).hom ≫ γ[mop S,P.X] := by
  apply Mod_.Hom.ext
  change (lineatorRaw P (Mod_.regular S) S ≫
      ((tensorFunctor P).map γ[mop S,(wattsRegular (R := S)).X]).hom) ≫
        (tensorFunctorRegularIso P).hom.hom =
    (tensorFunctorRegularIso P).hom.hom ▷ S ≫ γ[mop S,P.X].hom
  apply (cancel_epi (moduleπ P (Mod_.regular S) ▷ S)).mp
  simp only [assoc]
  rw [moduleπ_lineatorRaw_assoc, moduleπ_map_assoc]
  change (α_ P.X.X S S).hom ≫ P.X.X ◁ μ[S] ≫
      moduleπ P (Mod_.regular S) ≫ (tensorFunctorRegularIso P).hom.hom =
    moduleπ P (Mod_.regular S) ▷ S ≫ (tensorFunctorRegularIso P).hom.hom ▷ S ≫
      γ[mop S,P.X].hom
  rw [moduleπ_regular, ← comp_whiskerRight_assoc, moduleπ_regular]
  change (α_ P.X.X S S).hom ≫ P.X.X ◁ μ[S] ≫ γ[mop S,P.X].hom =
    γ[mop S,P.X].hom ▷ S ≫ γ[mop S,P.X].hom
  have h := (toBimodObj R S P).right_assoc
  apply (cancel_epi (α_ P.X.X S S).inv).mp
  simpa only [assoc, Iso.inv_hom_id_assoc] using h

/-- The actual regular action contraction recovers both actions of an
arbitrary mixed bimodule. -/
def tensorIso (P : Native R S) : evaluation.obj (tensorBundled P) ≅ P where
  hom := Mod_.Hom.mk' (tensorFunctorRegularIso P).hom (tensor_regular_right P)
  inv := by
    letI : IsMod_Hom (mop S) (M := (evaluation.obj (tensorBundled P)).X) (N := P.X)
        (tensorFunctorRegularIso P).hom := ⟨tensor_regular_right P⟩
    exact ⟨(tensorFunctorRegularIso P).inv⟩
  hom_inv_id := by apply Mod_.Hom.ext; exact (tensorFunctorRegularIso P).hom_inv_id
  inv_hom_id := by apply Mod_.Hom.ext; exact (tensorFunctorRegularIso P).inv_hom_id

instance evaluation_essSurj : (evaluation (R := R) (S := S)).EssSurj where
  mem_essImage P := ⟨tensorBundled P, ⟨tensorIso P⟩⟩

def tensorRoundtripIso : tensorRepresentation (R := R) (S := S) ⋙ evaluation ≅
    𝟭 (Native R S) :=
  NatIso.ofComponents tensorIso (by
    intro P Q f
    apply Mod_.Hom.ext
    apply Mod_.Hom.ext
    change ((tensorNat f).app (Mod_.regular S)).hom ≫
        (tensorFunctorRegularIso Q).hom.hom =
      (tensorFunctorRegularIso P).hom.hom ≫ f.hom.hom
    apply (cancel_epi (moduleπ P (Mod_.regular S))).mp
    rw [moduleπ_tensorNat_assoc, moduleπ_regular, moduleπ_regular_assoc]
    exact (congrArg Mod_.Hom.hom f.isMod_Hom.smul_hom).symm)

/-- Arbitrary actual mixed bimodules classify genuine strong module
functors between the two actual native module categories. Only the
source algebra needs separability. -/
def equivalence (Sep : SeparableAlgebra S) :
    Bundled Dᴹᵒᵖ (Mod_ D S) (Mod_ D R) ≌ Native R S := by
  letI := evaluationFaithful (R := R) Sep
  letI := evaluationFull (R := R) Sep
  letI : (evaluation (R := R) (S := S)).IsEquivalence := {}
  exact (evaluation (R := R) (S := S)).asEquivalence

def tensorRepresentationIsEquivalence (Sep : SeparableAlgebra S) :
    (tensorRepresentation (R := R) (S := S)).IsEquivalence := by
  letI : (evaluation (R := R) (S := S)).IsEquivalence :=
    (equivalence (R := R) Sep).isEquivalence_functor
  letI : (tensorRepresentation (R := R) (S := S) ⋙ evaluation).IsEquivalence :=
    Functor.isEquivalence_of_iso tensorRoundtripIso.symm
  exact Functor.isEquivalence_of_comp_right tensorRepresentation evaluation

/-- The inverse direction is the actual balancing quotient functor. -/
def tensorEquivalence (Sep : SeparableAlgebra S) :
    Native R S ≌ Bundled Dᴹᵒᵖ (Mod_ D S) (Mod_ D R) := by
  letI := tensorRepresentationIsEquivalence (R := R) Sep
  exact (tensorRepresentation (R := R) (S := S)).asEquivalence

instance equivalence_linear (Sep : SeparableAlgebra S) :
    (equivalence (R := R) Sep).functor.Linear ℂ := evaluation_linear

instance equivalence_additive (Sep : SeparableAlgebra S) :
    (equivalence (R := R) Sep).functor.Additive := evaluation_additive

instance tensorEquivalence_linear (Sep : SeparableAlgebra S) :
    (tensorEquivalence (R := R) Sep).functor.Linear ℂ := tensorRepresentation_linear

instance tensorEquivalence_additive (Sep : SeparableAlgebra S) :
    (tensorEquivalence (R := R) Sep).functor.Additive := tensorRepresentation_additive

end Paper18.Category.BimoduleRelativeTensor.MixedWatts
