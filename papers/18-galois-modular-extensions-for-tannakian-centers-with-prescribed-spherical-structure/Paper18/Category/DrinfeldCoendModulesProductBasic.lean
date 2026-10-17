import Paper18.Category.DrinfeldCoendModulesDesc
import Paper18.Category.DeligneTensorProductMap

/-! # Actual diagonal multiplication on rigid cap generators -/
noncomputable section
set_option maxHeartbeats 2000000
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped MonObj
universe v u w
namespace Paper18.Category.DrinfeldCoendModules
attribute [local instance 2000] RightRigidCategory.rightDual
open DiagonalAlgebra
variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
  [RightRigidCategory D] [Preadditive D] [Linear ℂ D]
  [MonoidalPreadditive D] [MonoidalLinear ℂ D] [HasKernels D] [HasFiniteBiproducts D]
  [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ D)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton D ι)

/-- The actual tensor-product comparison crosses the second strand
negatively past the next first strand. -/
@[reassoc]
lemma capPairIso_tensor (X Y X' Y' : D) :
    Functor.LaxMonoidal.μ (tensorProductFunctor (C := D))
        (DeligneProduct.externalObject X Y) (DeligneProduct.externalObject X' Y') ≫
      (tensorProductFunctor (C := D)).map (DeligneProduct.externalTensorIso X X' Y Y').hom ≫
        (capPairIso (X ⊗ X') (Y ⊗ Y')).hom =
    ((capPairIso X Y).hom ⊗ₘ (capPairIso X' Y').hom) ≫
      @tensorμ D _ _ (reverseBraiding D) X Y X' Y' := by
  have h := NatTrans.IsMonoidal.tensor
    (τ := (DeligneTensorProductMap.capEmbeddingIso D).hom)
    (⟨X,Y⟩ : LinearTensor D D) (⟨X',Y'⟩ : LinearTensor D D)
  simp only [Functor.LaxMonoidal.comp_μ, Functor.comp_obj] at h
  have he (A B : D) : (DeligneTensorProductMap.capEmbeddingIso D).hom.app
      (⟨A,B⟩ : LinearTensor D D) = (capPairIso A B).hom :=
    congrArg Iso.hom (DeligneTensorProductMap.capEmbeddingIso_app A B)
  change (Functor.LaxMonoidal.μ (tensorProductFunctor (C := D)) _ _ ≫
      (tensorProductFunctor (C := D)).map (DeligneProduct.externalTensorIso X X' Y Y').hom) ≫
      (DeligneTensorProductMap.capEmbeddingIso D).hom.app ⟨X ⊗ X',Y ⊗ Y'⟩ =
    ((DeligneTensorProductMap.capEmbeddingIso D).hom.app ⟨X,Y⟩ ⊗ₘ
      (DeligneTensorProductMap.capEmbeddingIso D).hom.app ⟨X',Y'⟩) ≫
      Functor.LaxMonoidal.μ (DeligneTensorProductMap.rawTensor D) ⟨X,Y⟩ ⟨X',Y'⟩ at h
  rw [he, he, he, DeligneTensorProductMap.rawTensor_tensor] at h
  simpa only [assoc] using h

/-- The actual multiplication is evaluated by the actual tensor-product
adjunction, without a pivotal or spherical input. -/
lemma algebra_mul_counit :
    (tensorProductFunctor (C := D)).map μ[canonicalAlgebra S] ≫ canonicalAlgebraCounit S =
      Functor.OplaxMonoidal.δ (tensorProductFunctor (C := D)) _ _ ≫
        (canonicalAlgebraCounit S ⊗ₘ canonicalAlgebraCounit S) ≫ (λ_ (𝟙_ D)).hom := by
  letI := DeligneProduct.hasKernels S S
  exact semisimpleAdjointAlgebra_mul_counit
    (DeligneProduct.skeleton S S) (tensorProductFunctor (C := D))

/-- The actual adjunction evaluates a product of two actual cap
generators as the actual tensor product of their chosen rigid caps. -/
lemma capGenerator_mul_counit (X Y : D) :
    Functor.LaxMonoidal.μ (tensorProductFunctor (C := D))
        (DeligneProduct.externalObject (dual D X) X)
        (DeligneProduct.externalObject (dual D Y) Y) ≫
      (tensorProductFunctor (C := D)).map
        ((capGenerator S X ⊗ₘ capGenerator S Y) ≫ μ[canonicalAlgebra S]) ≫
          canonicalAlgebraCounit S =
    (((capPairIso (dual D X) X).hom ≫ ε_ X (dual D X)) ⊗ₘ
      ((capPairIso (dual D Y) Y).hom ≫ ε_ Y (dual D Y))) ≫ (λ_ (𝟙_ D)).hom := by
  simp only [Functor.map_comp, assoc]
  rw [← Functor.LaxMonoidal.μ_natural_assoc]
  rw [algebra_mul_counit]
  simp only [Functor.Monoidal.μ_δ_assoc]
  rw [tensorHom_comp_tensorHom_assoc, capGenerator_counit, capGenerator_counit]

end Paper18.Category.DrinfeldCoendModules
