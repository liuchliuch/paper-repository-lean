import Paper18.Category.BimoduleRelativeTensorFreeHom
import Paper18.Category.FusionCategory

/-! # Actual weighted free-bimodule dimension identity

The two genuine free-module universal properties, followed by actual simple
resolutions, compute the sum of squared ambient dimensions of simple bimodules.
There is no pivotal or dual-category dimension premise.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits MonoidalOpposite
open scoped BigOperators MonObj
universe v u w wB
namespace Paper18.Category.ModuleFunctor
variable {D : Type u} [Category.{v} D] [Preadditive D] [Linear ℂ D]
  [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalLinear ℂ D]
  [HasKernels D] [HasFiniteBiproducts D]
  [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)]
  [RightRigidCategory D] [Simple (𝟙_ D)]
  {R : D} [MonObj R]
attribute [local instance] InternalModule.ambientMonoidalOppositeLeftAction

/-- The genuine underlying functor forgets the two native actions. -/
def bimoduleUnderlying : Bimodules R ⥤ D :=
  Mod_.forget (D := Mod_ D R) (mop R) ⋙ Mod_.forget (D := D) R

instance bimoduleUnderlying_additive : (bimoduleUnderlying (R := R)).Additive := by
  unfold bimoduleUnderlying
  infer_instance

instance bimoduleUnderlying_linear : (bimoduleUnderlying (R := R)).Linear ℂ := by
  unfold bimoduleUnderlying
  infer_instance

instance bimoduleUnderlying_faithful : (bimoduleUnderlying (R := R)).Faithful := by
  unfold bimoduleUnderlying
  infer_instance

variable {ι : Type w} [Fintype ι] (T : FiniteSemisimpleSkeleton D ι)
  {κ : Type wB} [Fintype κ] (TB : FiniteSemisimpleSkeleton (Bimodules R) κ)

/-- The ambient size of an actual simple two-sided module. -/
def bimoduleSimpleWeight (j : κ) : ℝ := T.fpdim (TB.simpleObject j).X.X

/-- Actual simple-bimodule decompositions compute the actual underlying dimension. -/
lemma bimodule_underlying_fpdim (P : Bimodules R) :
    T.fpdim P.X.X = ∑ j, (TB.multiplicity P j : ℝ) * bimoduleSimpleWeight T TB j := by
  change T.fpdim ((bimoduleUnderlying (R := R)).obj P) = _
  simp only [FiniteSemisimpleSkeleton.fpdim, bimoduleSimpleWeight,
    TB.multiplicity_map T (bimoduleUnderlying (R := R)) P,
    Nat.cast_sum, Nat.cast_mul, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]
  rfl

omit [RightRigidCategory D] [Simple (𝟙_ D)] in
/-- The actual free-bimodule Hom bijection is the transpose simple coefficient. -/
lemma doubleFree_multiplicity (i : ι) (j : κ) :
    TB.multiplicity (BimoduleRelativeTensor.doubleFree R R (T.simpleObject i)) j =
      T.multiplicity (TB.simpleObject j).X.X i := by
  change Module.finrank ℂ (TB.simpleObject j ⟶
    BimoduleRelativeTensor.doubleFree R R (T.simpleObject i)) = _
  rw [TB.finrank_hom_comm]
  exact BimoduleRelativeTensor.finrank_doubleFree_hom R R (T.simpleObject i) (TB.simpleObject j)

/-- The free object and actual decompositions give the weighted column equation. -/
lemma doubleFree_weighted_column (i : ι) :
    ∑ j, (T.multiplicity (TB.simpleObject j).X.X i : ℝ) * bimoduleSimpleWeight T TB j =
      T.fpdim R ^ 2 * T.fusionBasis.fpdim i := by
  calc
    _ = T.fpdim (BimoduleRelativeTensor.doubleFree R R (T.simpleObject i)).X.X := by
      rw [bimodule_underlying_fpdim T TB]
      simp only [doubleFree_multiplicity T TB]
    _ = _ := by
      rw [BimoduleRelativeTensor.doubleFree_X, T.fpdim_tensor, T.fpdim_tensor, T.fpdim_simple]
      ring

/-- The genuine free-bimodule Hom formula computes the weighted total exactly. -/
theorem bimodule_weighted_total :
    (∑ j, bimoduleSimpleWeight T TB j ^ 2) =
      T.fpdim R ^ 2 * T.fusionBasis.totalFPdim := by
  calc
    _ = ∑ j, (∑ i, (T.multiplicity (TB.simpleObject j).X.X i : ℝ) *
        T.fusionBasis.fpdim i) * bimoduleSimpleWeight T TB j := by
      apply Finset.sum_congr rfl
      intro j _
      change bimoduleSimpleWeight T TB j ^ 2 = bimoduleSimpleWeight T TB j * _
      ring
    _ = ∑ i, T.fusionBasis.fpdim i *
        (∑ j, (T.multiplicity (TB.simpleObject j).X.X i : ℝ) * bimoduleSimpleWeight T TB j) := by
      simp only [Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = ∑ i, T.fusionBasis.fpdim i * (T.fpdim R ^ 2 * T.fusionBasis.fpdim i) := by
      simp only [doubleFree_weighted_column T TB]
    _ = _ := by
      rw [FusionBasis.totalFPdim, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring

end Paper18.Category.ModuleFunctor
