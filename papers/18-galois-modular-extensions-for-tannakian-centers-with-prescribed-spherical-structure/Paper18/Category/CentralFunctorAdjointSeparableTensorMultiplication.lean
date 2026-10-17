import Paper18.Category.SeparableOfBimoduleSemisimple
import Paper18.Category.BimoduleRelativeTensorMixedWatts

/-! # Actual multiplication detected by its native tensor functor

The tensor functor induced by regular bimodule multiplication is pointwise
epimorphic. Evaluating an actual module-natural section at the regular
module recovers a genuine two-sided section of the original multiplication.
Neither construction assumes separability of the algebra.
-/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits MonoidalOpposite
open scoped MonObj MonoidalLeftAction
universe v u
namespace Paper18.Category.CentralFunctorAdjointSeparable
open BimoduleRelativeTensor
variable {D : Type u} [Category.{v} D] [MonoidalCategory D]
  [HasCoequalizers D] [LeftRigidCategory D] [RightRigidCategory D]
  [Preadditive D] [Linear ℂ D] [MonoidalPreadditive D] [MonoidalLinear ℂ D]
  (R : D) [MonObj R]
attribute [local instance] InternalModule.ambientMonoidalOppositeLeftAction

/-- The actual tensor transformation induced by actual regular
bimodule multiplication. -/
def tensorMultiplication :
    tensorFunctor (SeparableAlgebra.freeRegularBimodule R) ⟶
      tensorFunctor (ModuleFunctor.wattsRegular (R := R)) :=
  tensorNat (SeparableAlgebra.bimoduleMultiplication R)

/-- The actual algebra unit and actual balancing quotients prove each
component epimorphic; no bimodule section has been assumed. -/
instance tensorMultiplication_app_epi (M : Mod_ D R) :
    Epi ((tensorMultiplication R).app M) where
  left_cancellation {Z} f g h := by
    apply Mod_.Hom.ext
    have hh := congrArg (fun k =>
      moduleπ (SeparableAlgebra.freeRegularBimodule R) M ≫ k.hom) h
    simp only [Mod_.comp_hom', ← Category.assoc] at hh
    change (moduleπ (SeparableAlgebra.freeRegularBimodule R) M ≫
        ((tensorNat (SeparableAlgebra.bimoduleMultiplication R)).app M).hom) ≫ f.hom =
      (moduleπ (SeparableAlgebra.freeRegularBimodule R) M ≫
        ((tensorNat (SeparableAlgebra.bimoduleMultiplication R)).app M).hom) ≫ g.hom at hh
    rw [moduleπ_tensorNat, SeparableAlgebra.bimoduleMultiplication_hom] at hh
    have hu : ((λ_ R).inv ≫ η[R] ▷ R) ≫ μ[R] = 𝟙 R := by
      rw [Category.assoc, MonObj.one_mul, Iso.inv_hom_id]
    have ht := congrArg (fun k => (((λ_ R).inv ≫ η[R] ▷ R) ▷ M.X) ≫ k) hh
    simp only [← Category.assoc, ← comp_whiskerRight, hu,
      id_whiskerRight, Category.id_comp] at ht
    exact (cancel_epi (moduleπ (ModuleFunctor.wattsRegular (R := R)) M)).mp ht

/-- The proved evaluation/tensor roundtrip reflects an actual split
epimorphism of tensor functors to an actual split bimodule epimorphism. -/
def reflectTensorSplitEpi {P Q : Native R R} (f : P ⟶ Q)
    (s : SplitEpi ((tensorRepresentation (R := R) (S := R)).map f)) : SplitEpi f := by
  let T := tensorRepresentation (R := R) (S := R)
  let E := MixedWatts.evaluation (R := R) (S := R)
  let e := MixedWatts.tensorRoundtripIso (R := R) (S := R)
  refine ⟨e.inv.app Q ≫ E.map s.section_ ≫ e.hom.app P, ?_⟩
  have hn := e.hom.naturality f
  change E.map (T.map f) ≫ e.hom.app Q = e.hom.app P ≫ f at hn
  rw [Category.assoc, Category.assoc, ← hn]
  have hs : s.section_ ≫ T.map f = 𝟙 (T.obj Q) := s.id
  simp only [← Category.assoc, ← E.map_comp, hs]
  erw [E.map_id, Category.comp_id]
  exact e.inv_hom_id_app Q

/-- A genuine native module-functor section of the multiplication tensor
transformation gives an actual bimodule section of multiplication. -/
def separableOfTensorMultiplicationSplit
    (s : SplitEpi ((tensorRepresentation (R := R) (S := R)).map
      (SeparableAlgebra.bimoduleMultiplication R))) : SeparableAlgebra R := by
  let b := reflectTensorSplitEpi R (SeparableAlgebra.bimoduleMultiplication R) s
  exact
    { section_ := b.section_.hom.hom
      section_mul := by
        have h := congrArg (fun k => k.hom.hom) b.id
        simpa only [Mod_.comp_hom', SeparableAlgebra.bimoduleMultiplication_hom,
          Mod_.id_hom] using h
      left_linear := by
        have h := b.section_.hom.isMod_Hom.smul_hom
        change μ[R] ≫ b.section_.hom.hom =
          (R ◁ b.section_.hom.hom) ≫ (α_ R R R).inv ≫ μ[R] ▷ R at h
        exact h
      right_linear := by
        have h := b.section_.isMod_Hom.smul_hom
        rw [ModuleFunctor.SeparableAction.free_smul] at h
        have ht := congrArg Mod_.Hom.hom h
        change μ[R] ≫ b.section_.hom.hom =
          (b.section_.hom.hom ▷ R) ≫ (α_ R R R).hom ≫ R ◁ μ[R] at ht
        exact ht }

/-- A proved ordinary section with proved native module naturality
supplies the actual bimodule section. This form accepts the direct output
of separable averaging on ordinary natural transformations. -/
def separableOfModuleNaturalSection
    (s : tensorFunctor (ModuleFunctor.wattsRegular (R := R)) ⟶
      tensorFunctor (SeparableAlgebra.freeRegularBimodule R))
    [ModuleFunctor.IsModuleNatural Dᴹᵒᵖ s]
    (hs : s ≫ tensorMultiplication R = 𝟙 _) : SeparableAlgebra R := by
  apply separableOfTensorMultiplicationSplit R
  refine ⟨⟨s, (inferInstance : ModuleFunctor.IsModuleNatural Dᴹᵒᵖ s)⟩, ?_⟩
  apply Subtype.ext
  exact hs

end Paper18.Category.CentralFunctorAdjointSeparable
