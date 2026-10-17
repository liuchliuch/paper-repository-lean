import Paper18.Category.DiagonalAlgebraTransport
import Paper18.Category.DeligneProductMap
import Paper18.Category.DiagonalCondensationEmbeddingBasic

/-! # The actual shared diagonal algebra in an ambient Deligne product -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped MonObj
universe v u w vN uN vP uP wN wP
namespace Paper18.Category.DiagonalAlgebra
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [RightRigidCategory C] [Preadditive C] [Linear ℂ C]
  [MonoidalPreadditive C] [MonoidalLinear ℂ C] [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ C)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  {N : Type uN} [Category.{vN} N] [MonoidalCategory N]
  [Preadditive N] [Linear ℂ N] [MonoidalPreadditive N] [MonoidalLinear ℂ N]
  {P : Type uP} [Category.{vP} P] [MonoidalCategory P]
  [Preadditive P] [Linear ℂ P] [MonoidalPreadditive P] [MonoidalLinear ℂ P]
  (F : C ⥤ N) [F.Monoidal] [F.Additive] [F.Linear ℂ]
  (G : C ⥤ P) [G.Monoidal] [G.Additive] [G.Linear ℂ]

/-- The actual shared diagonal algebra in N ⊠ P. -/
abbrev productCanonicalAlgebra : DeligneProduct N P :=
  mappedCanonicalAlgebra S (DeligneProduct.map F G)

/-- Its actual decomposition uses the actual categorical duals, precisely
in the form required by the genuine free-module intersection calculation. -/
def productCanonicalAlgebraIso : productCanonicalAlgebra S F G ≅
    ⨁ fun i : ι => DiagonalCondensation.pair (F.obj (S.simpleObject i))
      (G.obj (dual C (S.simpleObject i))) :=
  mappedCanonicalAlgebraIso S (DeligneProduct.map F G) ≪≫
    biproduct.mapIso (fun i => DeligneProduct.mapPairIso F G
      (S.simpleObject i) (S.simpleObject (S.dualLabel i)) ≪≫
        (Mat_.embedding (LinearTensor N P)).mapIso
          (LinearTensor.isoOfPair (Iso.refl _) (G.mapIso (S.dualIso i))))

/-- The embedded actual multiplication pairing. -/
def productCanonicalMultiplicationPairing :
    ModuleBalancing.MultiplicationPairing (productCanonicalAlgebra S F G) :=
  mappedCanonicalMultiplicationPairing S (DeligneProduct.map F G)

/-- The embedded actual bimodule separability section. -/
def productCanonicalSeparable (J : PivotalStructure C) (hJ : J.Spherical) :
    SeparableAlgebra (productCanonicalAlgebra S F G) :=
  mappedCanonicalSeparable S (DeligneProduct.map F G) J hJ

/-- Genuine fully faithful tensor embeddings give a connected actual
shared diagonal algebra. -/
theorem productCanonicalAlgebra_connected [F.Full] [F.Faithful] [G.Full] [G.Faithful] :
    Module.finrank ℂ (𝟙_ (DeligneProduct N P) ⟶ productCanonicalAlgebra S F G) = 1 :=
  mappedCanonicalAlgebra_connected S (DeligneProduct.map F G)

section FPdim
variable [RightRigidCategory N] [HasKernels N] [HasFiniteBiproducts N]
  [∀ X Y : N, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ N)]
  [RightRigidCategory P] [HasKernels P] [HasFiniteBiproducts P]
  [∀ X Y : P, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ P)]
  {κ : Type wN} [Fintype κ] (T : FiniteSemisimpleSkeleton N κ)
  {ν : Type wP} [Fintype ν] (U : FiniteSemisimpleSkeleton P ν)

/-- Actual FP dimension of the ambient shared diagonal. -/
theorem productCanonicalAlgebra_fpdim :
    letI := DeligneProduct.hasKernels T U
    letI := DeligneProduct.simpleUnit T U
    (DeligneProduct.skeleton T U).fpdim (productCanonicalAlgebra S F G) =
      S.fusionBasis.totalFPdim := by
  letI := DeligneProduct.hasKernels T U
  letI := DeligneProduct.simpleUnit T U
  exact mappedCanonicalAlgebra_fpdim S (DeligneProduct.map F G) (DeligneProduct.skeleton T U)

end FPdim
end Paper18.Category.DiagonalAlgebra
