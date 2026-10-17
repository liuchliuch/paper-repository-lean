import Paper18.Category.PivotalPullbackMonoidal

/-! # Actual positive pivotal structures are preserved by strong monoidal equivalences

The proof pulls the target pivotal structure back using the canonical
monoidal double-dual comparison, transfers its actual positive trace, and
uses uniqueness of the actual positive pivotal structure. No braiding is
assumed on either category or on the functor.
-/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
universe v u w v' u' w'
namespace Paper18.Category
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ C)]
  {D : Type u'} [Category.{v'} D] [MonoidalCategory D] [RightRigidCategory D]
  [Preadditive D] [Linear ℂ D] [MonoidalPreadditive D] [MonoidalLinear ℂ D]
  [HasKernels D] [HasFiniteBiproducts D]
  [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ D)]
  (F : C ⥤ D) [F.Monoidal] [F.Additive] [F.Linear ℂ]
  (J : PivotalStructure C) (K : PivotalStructure D)
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  {κ : Type w'} [Fintype κ] (T : FiniteSemisimpleSkeleton D κ)

include S T

/-- Any fully faithful complex-linear strong monoidal functor between
actual positive pivotal fusion categories preserves their actual pivotal
structures. Neither category nor functor needs a braiding. -/
theorem preservesPivotal_of_positive_fullyFaithful [F.Full] [F.Faithful]
    (hJ : J.Positive) (hK : K.Positive) : PreservesPivotal F J K := by
  have hP := pivotalPullbackMonoidal_positive F K T hK
  have he : J = pivotalPullbackMonoidal F K :=
    J.eq_of_positive (pivotalPullbackMonoidal F K) S hJ hP
  rw [he]
  exact pivotalPullbackMonoidal_preserves F K

/-- In particular, an actual complex-linear strong monoidal equivalence
preserves the prescribed actual positive pivotal structures. -/
theorem preservesPivotal_of_positive_equivalence [F.IsEquivalence]
    (hJ : J.Positive) (hK : K.Positive) : PreservesPivotal F J K :=
  preservesPivotal_of_positive_fullyFaithful F J K S T hJ hK

omit S in
/-- Positivity of the actual pivotal trace restricts along a faithful
complex-linear strong monoidal pivotal functor. The image object may be
reducible; its actual FP dimension is positive because it is nonzero. -/
theorem positive_of_faithful_pivotal [F.Faithful]
    (h : PreservesPivotal F J K) (hK : K.Positive) : J.Positive := by
  intro X hX
  letI := hX
  rw [← h.rightDim_scalar X, K.rightDim_eq_fpdim T hK]
  have hn : ¬ IsZero (F.obj X) := by
    intro hz
    apply CategoryTheory.id_nonzero X
    apply F.map_injective
    rw [CategoryTheory.Functor.map_id, Functor.map_zero]
    exact hz.eq_of_src _ _
  exact ⟨T.fpdim_pos_of_not_isZero _ hn, rfl⟩

end Paper18.Category
