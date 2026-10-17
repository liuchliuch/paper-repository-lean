import Paper18.Category.DiagonalAlgebraProductBraided
import Paper18.Category.DiagonalAlgebraTransportPivotal
import Paper18.Category.PivotalProductMap

/-! # Actual prescribed spherical data on the ambient shared diagonal -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
universe v u w vN uN vP uP wN wP
namespace Paper18.Category.DiagonalAlgebra
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [RightRigidCategory C] [Preadditive C] [Linear ℂ C]
  [MonoidalPreadditive C] [MonoidalLinear ℂ C] [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ C)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  {N : Type uN} [Category.{vN} N] [MonoidalCategory N] [BraidedCategory N]
  [RightRigidCategory N] [Preadditive N] [Linear ℂ N]
  [MonoidalPreadditive N] [MonoidalLinear ℂ N]
  {P : Type uP} [Category.{vP} P] [MonoidalCategory P] [BraidedCategory P]
  [RightRigidCategory P] [Preadditive P] [Linear ℂ P]
  [MonoidalPreadditive P] [MonoidalLinear ℂ P]
  (F : C ⥤ N) [F.Braided] [F.Additive] [F.Linear ℂ]
  (G : C ⥤ P) [G.Braided] [G.Additive] [G.Linear ℂ]
  (J : PivotalStructure C) (JN : PivotalStructure N) (JP : PivotalStructure P)
  (hF : PreservesPivotal F J JN) (hG : PreservesPivotal G J JP)

include hF hG

/-- Actual compatibility of the two given embeddings determines the
actual prescribed pivotal structure carried by their product functor. -/
theorem productCanonical_preservesPivotal :
    PreservesPivotal (DeligneProduct.map F G) (Drinfeld.reverseSecondPivotal J)
      (DeligneProduct.reverseRightProductPivotal JN JP) :=
  DeligneProduct.mapReverseSecond_preservesPivotal F G J J JN JP hF hG

/-- The actual embedded shared diagonal has trivial twist for the actual
prescribed ambient reverse-second pivotal structure. -/
theorem productCanonicalAlgebra_twist (hJ : J.Spherical) :
    letI : BraidedCategory (DeligneProduct N P) := DeligneProduct.reverseSecondBraiding N P
    ((DeligneProduct.reverseRightProductPivotal JN JP).twistIso
      (productCanonicalAlgebra S F G)).hom = 𝟙 _ := by
  letI : BraidedCategory (DeligneProduct N P) := DeligneProduct.reverseSecondBraiding N P
  letI : BraidedCategory (DeligneProduct C C) := Drinfeld.deligneReverseSecondBraiding C
  letI : (DeligneProduct.map F G).Braided := DeligneProduct.mapReverseSecondBraided F G
  exact mappedCanonicalAlgebra_twist S (DeligneProduct.map F G) J
    (DeligneProduct.reverseRightProductPivotal JN JP)
    (productCanonical_preservesPivotal F G J JN JP hF hG) hJ
    (fun X Y => Functor.LaxBraided.braided (F := DeligneProduct.map F G) X Y)

section Dimensions
variable [HasKernels N] [HasFiniteBiproducts N]
  [∀ X Y : N, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ N)]
  [HasKernels P] [HasFiniteBiproducts P]
  [∀ X Y : P, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ P)]
  {κ : Type wN} [Fintype κ] (T : FiniteSemisimpleSkeleton N κ)
  {ν : Type wP} [Fintype ν] (U : FiniteSemisimpleSkeleton P ν)
include hF hG

/-- Actual prescribed categorical dimension of the embedded shared diagonal. -/
theorem productCanonicalAlgebra_rightDim :
    letI := DeligneProduct.hasKernels T U
    letI := DeligneProduct.simpleUnit T U
    (DeligneProduct.reverseRightProductPivotal JN JP).rightDim
      (productCanonicalAlgebra S F G) = (J.pivotalData S).globalDimension := by
  letI := DeligneProduct.hasKernels T U
  letI := DeligneProduct.simpleUnit T U
  exact mappedCanonicalAlgebra_rightDim S (DeligneProduct.map F G) J
    (DeligneProduct.reverseRightProductPivotal JN JP)
    (productCanonical_preservesPivotal F G J JN JP hF hG)

/-- The actual prescribed dimension of the embedded diagonal is strictly
positive in real part, derived from actual global simple norms. -/
theorem productCanonicalAlgebra_rightDim_re_pos :
    letI := DeligneProduct.hasKernels T U
    letI := DeligneProduct.simpleUnit T U
    0 < ((DeligneProduct.reverseRightProductPivotal JN JP).rightDim
      (productCanonicalAlgebra S F G)).re := by
  letI := DeligneProduct.hasKernels T U
  letI := DeligneProduct.simpleUnit T U
  exact mappedCanonicalAlgebra_rightDim_re_pos S (DeligneProduct.map F G) J
    (DeligneProduct.reverseRightProductPivotal JN JP)
    (productCanonical_preservesPivotal F G J JN JP hF hG)

/-- The actual prescribed ambient diagonal dimension is real. -/
theorem productCanonicalAlgebra_rightDim_im_eq_zero :
    letI := DeligneProduct.hasKernels T U
    letI := DeligneProduct.simpleUnit T U
    ((DeligneProduct.reverseRightProductPivotal JN JP).rightDim
      (productCanonicalAlgebra S F G)).im = 0 := by
  letI := DeligneProduct.hasKernels T U
  letI := DeligneProduct.simpleUnit T U
  exact mappedCanonicalAlgebra_rightDim_im_eq_zero S (DeligneProduct.map F G) J
    (DeligneProduct.reverseRightProductPivotal JN JP)
    (productCanonical_preservesPivotal F G J JN JP hF hG)

end Dimensions
end Paper18.Category.DiagonalAlgebra
