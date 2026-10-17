import Paper18.Category.ModuleFunctorDualDimensionScaling

/-! # Genuine underlying FP dimensions give a positive module weight

The common eigenvector is constructed from an actual faithful strong module
functor to the regular module category of an actual fusion category.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped BigOperators MonoidalLeftAction
universe v u vM uM w wM
namespace Paper18.Category.ModuleFunctor
open MonoidalLeftAction
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [RightRigidCategory C] [Simple (𝟙_ C)]
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {M : Type uM} [Category.{vM} M] [Preadditive M] [Linear ℂ M]
  [HasKernels M] [HasFiniteBiproducts M]
  [∀ X Y : M, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalLeftAction C M]
  [∀ c : C, (actionLeft M c).Additive]
  [∀ X : M, (actionRight C X).Additive]
  {ι : Type w} [Fintype ι] (SC : FiniteSemisimpleSkeleton C ι)
  {κ : Type wM} [Fintype κ] (SM : FiniteSemisimpleSkeleton M κ)
  (U : M ⥤ C) [U.Additive] [U.Faithful] [U.LeftLinear C]

/-- The actual underlying positive simple weights. -/
def moduleUnderlyingWeight (j : κ) : ℝ := SC.fpdim (U.obj (SM.simpleObject j))

omit [∀ c : C, (actionLeft M c).Additive] [∀ X : M, (actionRight C X).Additive]
  [U.Faithful] [U.LeftLinear C] in
omit [MonoidalLeftAction C M] in
/-- Actual source decompositions compute the actual underlying weight. -/
lemma fpdim_underlying_eq_weight (X : M) :
    SC.fpdim (U.obj X) = moduleObjectWeight SM (moduleUnderlyingWeight SC SM U) X := by
  simp only [FiniteSemisimpleSkeleton.fpdim, moduleObjectWeight, moduleUnderlyingWeight,
    SM.multiplicity_map SC U X, Nat.cast_sum, Nat.cast_mul, Finset.sum_mul,
    Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

omit [HasKernels M] [∀ X Y : M, FiniteDimensional ℂ (X ⟶ Y)]
  [∀ c : C, (actionLeft M c).Additive] [∀ X : M, (actionRight C X).Additive]
  [U.LeftLinear C] in
omit [Linear ℂ M] [MonoidalLeftAction C M] in
/-- Faithfulness detects the actual nonzero identity of every module simple. -/
lemma moduleUnderlyingWeight_pos (j : κ) : 0 < moduleUnderlyingWeight SC SM U j := by
  apply SC.fpdim_pos_of_not_isZero
  intro hz
  apply CategoryTheory.id_nonzero (SM.simpleObject j)
  apply U.map_injective
  rw [U.map_id, U.map_zero]
  exact hz.eq_zero_of_src _

omit [∀ c : C, (actionLeft M c).Additive] [∀ X : M, (actionRight C X).Additive]
  [U.Faithful] in
/-- The genuine module lineator proves the common action eigenvalue equation. -/
lemma moduleUnderlyingWeight_action (a : ι) (j : κ) :
    ∑ k, (moduleActionCoeff SC SM a j k : ℝ) * moduleUnderlyingWeight SC SM U k =
      SC.fusionBasis.fpdim a * moduleUnderlyingWeight SC SM U j := by
  change moduleObjectWeight SM (moduleUnderlyingWeight SC SM U)
    (SC.simpleObject a ⊙ₗ SM.simpleObject j) = _
  rw [← fpdim_underlying_eq_weight SC SM U]
  rw [← SC.fpdim_iso (Functor.LeftLinear.μₗIso U (SC.simpleObject a) (SM.simpleObject j))]
  change SC.fpdim (SC.simpleObject a ⊗ U.obj (SM.simpleObject j)) = _
  rw [SC.fpdim_tensor, SC.fpdim_simple]
  rfl

end Paper18.Category.ModuleFunctor
