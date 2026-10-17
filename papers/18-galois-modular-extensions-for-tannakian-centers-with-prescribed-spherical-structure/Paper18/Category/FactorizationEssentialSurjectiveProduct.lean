import Paper18.Category.LinearTensorSemisimple
import Paper18.Category.LinearTensorRigid
import Paper18.Category.LinearMatMonoidalEmbedding
import Paper18.Category.LinearMatMonoidalRigid
import Paper18.Category.FunctorImage

/-! # Actual fusion coefficients and FP dimensions of the Deligne product -/
noncomputable section
open Classical
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits CategoryTheory.Functor.Monoidal
open scoped BigOperators TensorProduct
universe v u w v' u' w'
namespace Paper18.Category.DeligneProduct
attribute [local instance 2000] RightRigidCategory.rightDual
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

/-- The pair of actual unit representatives is the actual Deligne tensor unit. -/
def pairUnitIso : pairObject S T S.unitLabel T.unitLabel ≅ 𝟙_ (DeligneProduct C D) :=
  (Mat_.embedding (LinearTensor C D)).mapIso (LinearTensor.isoOfPair S.unitIso T.unitIso)

/-- The constructed simple-pair theorem gives an actual simple tensor unit. -/
def simpleUnit : Simple (𝟙_ (DeligneProduct C D)) :=
  Simple.of_iso (pairUnitIso S T).symm

variable [HasKernels (DeligneProduct C D)]

/-- The fusion coefficients of the actual simple pairs are products of
the actual factor fusion coefficients, by the actual tensor-product Hom spaces. -/
lemma fusionCoeff_pair (p q r : ι × κ) :
    (skeleton S T).fusionCoeff p q r =
      S.fusionCoeff p.1 q.1 r.1 * T.fusionCoeff p.2 q.2 r.2 := by
  let A : LinearTensor C D := ⟨S.simpleObject p.1, T.simpleObject p.2⟩
  let B : LinearTensor C D := ⟨S.simpleObject q.1, T.simpleObject q.2⟩
  let R : LinearTensor C D := ⟨S.simpleObject r.1, T.simpleObject r.2⟩
  change Module.finrank ℂ
    ((Mat_.embedding (LinearTensor C D)).obj R ⟶
      (Mat_.embedding (LinearTensor C D)).obj A ⊗ (Mat_.embedding (LinearTensor C D)).obj B) = _
  rw [finrank_hom_iso (Iso.refl _) (μIso (Mat_.embedding (LinearTensor C D)) A B),
    ← (fullyFaithfulHomLinearEquiv (Mat_.embedding (LinearTensor C D)) R (A ⊗ B)).finrank_eq]
  change Module.finrank ℂ
    ((S.simpleObject r.1 ⟶ S.simpleObject p.1 ⊗ S.simpleObject q.1) ⊗[ℂ]
      (T.simpleObject r.2 ⟶ T.simpleObject p.2 ⊗ T.simpleObject q.2)) = _
  exact Module.finrank_tensorProduct

variable [Simple (𝟙_ (DeligneProduct C D))]

lemma unitLabel_eq_pair : (skeleton S T).unitLabel = (S.unitLabel, T.unitLabel) := by
  apply (skeleton S T).iso_injective
  exact ⟨(skeleton S T).unitIso ≪≫ (pairUnitIso S T).symm⟩

/-- The actual Deligne simple pairs have the product FP dimensions. This is
derived by uniqueness of the positive dimension character applied to the
proved actual fusion coefficients. -/
lemma fpdim_pair (p : ι × κ) :
    (skeleton S T).fusionBasis.fpdim p = S.fusionBasis.fpdim p.1 * T.fusionBasis.fpdim p.2 := by
  let P := (skeleton S T).fusionBasis
  let d : ι × κ → ℝ := fun p => S.fusionBasis.fpdim p.1 * T.fusionBasis.fpdim p.2
  have hdpos (p : ι × κ) : 0 < d p :=
    mul_pos (S.fusionBasis.fpdim_pos p.1) (T.fusionBasis.fpdim_pos p.2)
  have hdone : d P.one = 1 := by
    change d (skeleton S T).unitLabel = 1
    rw [unitLabel_eq_pair]
    exact (congrArg₂ (fun a b : ℝ => a * b)
      S.fusionBasis.fpdim_one T.fusionBasis.fpdim_one).trans (one_mul 1)
  have hdmul (p q : ι × κ) : ∑ r, (P.N p q r : ℝ) * d r = d p * d q := by
    change ∑ r, ((skeleton S T).fusionCoeff p q r : ℝ) * d r = _
    simp_rw [fusionCoeff_pair, Nat.cast_mul]
    rw [Fintype.sum_prod_type]
    calc
      _ = (∑ i, (S.fusionCoeff p.1 q.1 i : ℝ) * S.fusionBasis.fpdim i) *
          (∑ j, (T.fusionCoeff p.2 q.2 j : ℝ) * T.fusionBasis.fpdim j) := by
        rw [Fintype.sum_mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        dsimp [d]
        ring
      _ = _ := by
        change (∑ i, (S.fusionBasis.N p.1 q.1 i : ℝ) * S.fusionBasis.fpdim i) *
          (∑ j, (T.fusionBasis.N p.2 q.2 j : ℝ) * T.fusionBasis.fpdim j) = _
        rw [S.fusionBasis.fpdim_mul, T.fusionBasis.fpdim_mul]
        dsimp [d]
        ring
  exact ((FusionBasis.PositiveDimension.mk d hdpos hdone hdmul).eq_fpdim p).symm

/-- The total dimension of the actual Deligne product is the product of
the two actual total dimensions. -/
theorem totalFPdim_product :
    (skeleton S T).fusionBasis.totalFPdim =
      S.fusionBasis.totalFPdim * T.fusionBasis.totalFPdim := by
  unfold FusionBasis.totalFPdim
  simp_rw [fpdim_pair, mul_pow]
  rw [Fintype.sum_prod_type, Fintype.sum_mul_sum]

end Paper18.Category.DeligneProduct
