import Paper18.Category.CentralizerDimensionFunctor
import Paper18.Category.DiagonalAlgebraSemisimpleUnit

/-! # The actual FP dimension quotient is the adjoint unit's dimension -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
universe v u w v' u' w'
namespace Paper18.Category.FiniteSemisimpleSkeleton
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [RightRigidCategory C] [Simple (𝟙_ C)]
  {D : Type u'} [Category.{v'} D] [Preadditive D] [Linear ℂ D]
  [HasKernels D] [HasFiniteBiproducts D]
  [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalLinear ℂ D]
  [RightRigidCategory D] [Simple (𝟙_ D)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  {κ : Type w'} [Fintype κ] (T : FiniteSemisimpleSkeleton D κ)
  (F : C ⥤ D) [F.Additive] [F.Monoidal]
  (R : D ⥤ C) [R.Additive] [R.Linear ℂ] (adj : F ⊣ R)

/-- The actual adjunction correspondence is linear because its right
adjoint is linear. Its maps are the genuine unit and functor maps. -/
def adjointHomLinearEquiv (X : C) (Y : D) :
    (F.obj X ⟶ Y) ≃ₗ[ℂ] (X ⟶ R.obj Y) where
  toEquiv := adj.homEquiv X Y
  map_add' f g := by
    change adj.unit.app X ≫ R.map (f + g) =
      adj.unit.app X ≫ R.map f + adj.unit.app X ≫ R.map g
    simp only [Functor.map_add, Preadditive.comp_add]
  map_smul' r f := by
    change adj.unit.app X ≫ R.map (r • f) = r • (adj.unit.app X ≫ R.map f)
    simp only [Functor.map_smul, Linear.comp_smul]

include adj in
/-- Actual right-adjoint unit multiplicities are exactly the actual
tensor functor's unit column. -/
theorem multiplicity_adjoint_unit (i : ι) :
    S.multiplicity (R.obj (𝟙_ D)) i = S.imageCoeff T F i T.unitLabel := by
  change Module.finrank ℂ (S.simpleObject i ⟶ R.obj (𝟙_ D)) = _
  rw [← (adjointHomLinearEquiv F R adj (S.simpleObject i) (𝟙_ D)).finrank_eq]
  unfold imageCoeff
  rw [T.multiplicity_eq_finrank_hom]
  exact finrank_hom_iso (Iso.refl _) T.unitIso.symm

include adj in
/-- Dominance identifies the actual dimension quotient with the actual
right-adjoint tensor unit. No separability, braiding or pivot is needed. -/
theorem totalFPdim_eq_adjoint_unit
    (hF : ∀ Y : D, ∃ X : C, Nonempty (Retract Y (F.obj X))) :
    S.fusionBasis.totalFPdim = S.fpdim (R.obj (𝟙_ D)) * T.fusionBasis.totalFPdim := by
  rw [S.dominant_totalFPdim_eq T F hF]
  unfold fpdim
  simp_rw [S.multiplicity_adjoint_unit T F R adj]

/-- The canonical constructed right adjoint has the same exact formula. -/
theorem totalFPdim_eq_semisimpleAdjointAlgebra [F.Linear ℂ]
    (hF : ∀ Y : D, ∃ X : C, Nonempty (Retract Y (F.obj X))) :
    S.fusionBasis.totalFPdim =
      S.fpdim (DiagonalAlgebra.semisimpleAdjointAlgebra S F) *
        T.fusionBasis.totalFPdim :=
  S.totalFPdim_eq_adjoint_unit T F (DiagonalAlgebra.semisimpleRightAdjoint S F)
    (DiagonalAlgebra.semisimpleRightAdjunction S F) hF

end Paper18.Category.FiniteSemisimpleSkeleton
