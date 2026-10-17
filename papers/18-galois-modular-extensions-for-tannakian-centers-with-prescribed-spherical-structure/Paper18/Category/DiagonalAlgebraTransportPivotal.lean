import Paper18.Category.DiagonalAlgebraTransport
import Paper18.Category.ModuleBalancingPositive

/-! # Prescribed twist and positive dimension of the embedded actual diagonal -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
universe v u w v' u'
namespace Paper18.Category.DiagonalAlgebra
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [RightRigidCategory C] [Preadditive C] [Linear ℂ C]
  [MonoidalPreadditive C] [MonoidalLinear ℂ C] [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ C)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  {D : Type u'} [Category.{v'} D] [MonoidalCategory D] [BraidedCategory D]
  [RightRigidCategory D] [Preadditive D] [Linear ℂ D] [HasFiniteBiproducts D]
  (H : DeligneProduct C C ⥤ D) [H.Monoidal] [H.Additive] [H.Linear ℂ]
  (J : PivotalStructure C) (K : PivotalStructure D)
  (hP : PreservesPivotal H (Drinfeld.reverseSecondPivotal J) K)

include hP

/-- An actual compatible braided pivotal embedding carries the proved
trivial diagonal twist to the actual prescribed ambient twist. -/
theorem mappedCanonicalAlgebra_twist (hJ : J.Spherical)
    (hH : ∀ X Y : DeligneProduct C C,
      (letI : BraidedCategory (DeligneProduct C C) := Drinfeld.deligneReverseSecondBraiding C;
        Functor.LaxMonoidal.μ H X Y ≫ H.map (β_ X Y).hom) =
      (β_ (H.obj X) (H.obj Y)).hom ≫ Functor.LaxMonoidal.μ H Y X) :
    (K.twistIso (mappedCanonicalAlgebra S H)).hom = 𝟙 _ := by
  letI : BraidedCategory (DeligneProduct C C) := Drinfeld.deligneReverseSecondBraiding C
  letI : H.Braided := { toLaxBraided := { braided := hH } }
  have h := hP.twist (canonicalAlgebra S)
  rw [canonicalAlgebra_twist S J hJ, CategoryTheory.Functor.map_id] at h
  exact h.symm

section Dimensions
variable [HasKernels D] [Simple (𝟙_ D)]
  [MonoidalPreadditive D] [MonoidalLinear ℂ D]
  [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)]
/-- The embedded diagonal's actual prescribed dimension is computed by
actual pivotal preservation and the source's actual diagonal decomposition. -/
theorem mappedCanonicalAlgebra_rightDim :
    K.rightDim (mappedCanonicalAlgebra S H) = (J.pivotalData S).globalDimension := by
  letI := DeligneProduct.hasKernels S S
  letI := DeligneProduct.simpleUnit S S
  exact (hP.rightDim_scalar (canonicalAlgebra S)).trans (canonicalAlgebra_rightDim S J)

/-- The actual prescribed dimension of the embedded diagonal has positive
real part. No positivity conclusion is supplied as an assumption. -/
theorem mappedCanonicalAlgebra_rightDim_re_pos :
    0 < (K.rightDim (mappedCanonicalAlgebra S H)).re := by
  rw [mappedCanonicalAlgebra_rightDim S H J K hP]
  exact (J.pivotalData S).globalDimension_re_pos

/-- The actual prescribed dimension of the embedded diagonal is real. -/
theorem mappedCanonicalAlgebra_rightDim_im_eq_zero :
    (K.rightDim (mappedCanonicalAlgebra S H)).im = 0 := by
  rw [mappedCanonicalAlgebra_rightDim S H J K hP]
  simp [Paper18.PivotalData.globalDimension, (J.pivotalData S).ndim_eq_normSq]

end Dimensions
end Paper18.Category.DiagonalAlgebra
