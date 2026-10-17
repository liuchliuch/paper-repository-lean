import Paper18.Category.ENOPseudounitaryNumberField
import Paper18.Category.ENOPseudounitaryPositive

/-!
# Reduction of the weakly integral theorem to ratio integrality

The algebraic and categorical correction steps are proved. The only additional
premise in these reusable reductions is the categorical ratio-integrality
statement of ENO Proposition 8.22. Its actual categorical proof and the
resulting unconditional weakly integral theorem are in `ENOPseudounitary`.

Reference: Etingof--Nikshych--Ostrik, *On fusion categories*, Annals of
Mathematics 162 (2005), Propositions 8.22--8.24, pp. 622--623.
-/

noncomputable section
open Classical
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
universe v u w

namespace Paper18.Category.PivotalStructure

variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [RightRigidCategory C] [Simple (𝟙_ C)]
  {ι : Type w} [Fintype ι] (J : PivotalStructure C) (S : FiniteSemisimpleSkeleton C ι)

/-- Every step after categorical ratio integrality is proved, including
the actual coherent positive pivotal identification and its uniqueness. -/
theorem exists_unique_positive_of_weakIntegral_of_ratioIntegral
    (hJ : J.Spherical) (hB : S.fusionBasis.WeaklyIntegral)
    (hRatio : IsIntegral ℤ
      ((J.pivotalData S).globalDimension / (S.fusionBasis.totalFPdim : ℂ))) :
    ∃! K : PivotalStructure C, K.Positive :=
  J.exists_unique_positive_of_global_eq S hJ
    ((J.pivotalData S).globalDimension_eq_of_weakIntegral_and_ratioIntegral hB hRatio)

/-- The comparison sign with the prescribed actual spherical structure
is obtained from the constructed actual positive structure. -/
theorem exists_positive_sign_of_weakIntegral_of_ratioIntegral
    (hJ : J.Spherical) (hB : S.fusionBasis.WeaklyIntegral)
    (hRatio : IsIntegral ℤ
      ((J.pivotalData S).globalDimension / (S.fusionBasis.totalFPdim : ℂ))) :
    ∃ K : PivotalStructure C, K.Positive ∧ K.Spherical ∧
      ∃ χ : Paper18.SignCharacter S.fusionBasis,
        ∀ i, J.rightDim (S.simpleObject i) = χ.val i * (S.fusionBasis.fpdim i : ℂ) :=
  J.exists_positive_sign_of_global_eq S hJ
    ((J.pivotalData S).globalDimension_eq_of_weakIntegral_and_ratioIntegral hB hRatio)

end Paper18.Category.PivotalStructure
