import Paper18.Category.DiagonalAlgebraGeneralDecomposition
import Paper18.Category.DeligneProductEmbedding
import Paper18.Category.PivotalDimension

/-! # Actual cap generators of the canonical diagonal algebra

The generators are actual adjunction transposes of actual rigid evaluation
maps. Their spanning and retract formulas do not require a pivotal structure.
-/
noncomputable section
set_option maxHeartbeats 1000000
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped TensorProduct
universe v u w
namespace Paper18.Category.DiagonalAlgebra
attribute [local instance 2000] RightRigidCategory.rightDual
variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
  [RightRigidCategory D] [Preadditive D] [Linear ℂ D]
  [MonoidalPreadditive D] [MonoidalLinear ℂ D] [HasKernels D] [HasFiniteBiproducts D]
  [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ D)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton D ι)

/-- The actual tensor-product evaluation of an actual external pair. -/
def capPairIso (X Y : D) :
    (tensorProductFunctor (C := D)).obj (DeligneProduct.externalObject X Y) ≅ X ⊗ Y :=
  (Center.forget D).mapIso (Drinfeld.deligneFactorizationPairIso X Y)

/-- The actual external-pair map associated with actual factor maps. -/
def capPairMap {X X' Y Y' : D} (f : X ⟶ X') (g : Y ⟶ Y') :
    DeligneProduct.externalObject X Y ⟶ DeligneProduct.externalObject X' Y' :=
  (Mat_.embedding (LinearTensor D D)).map
    (show (⟨X,Y⟩ : LinearTensor D D) ⟶ ⟨X',Y'⟩ from f ⊗ₜ[ℂ] g)

@[reassoc]
lemma capPairIso_naturality {X X' Y Y' : D} (f : X ⟶ X') (g : Y ⟶ Y') :
    (tensorProductFunctor (C := D)).map (capPairMap f g) ≫ (capPairIso X' Y').hom =
      (capPairIso X Y).hom ≫ (f ⊗ₘ g) := by
  have h := congrArg (Center.forget D).map
    (Drinfeld.deligneFactorizationPairIso_naturality (f ⊗ₜ[ℂ] g))
  rw [Drinfeld.linearFactorization_map_tmul D f g] at h
  simpa only [Functor.map_comp, Functor.comp_map, tensorProductFunctor, capPairMap,
    capPairIso, Functor.mapIso_hom] using h

/-- The actual canonical diagonal cap generator at an arbitrary object. -/
def capGenerator (X : D) :
    DeligneProduct.externalObject (dual D X) X ⟶ canonicalAlgebra S :=
  (tensorProductRightAdjunction S).homEquiv _ _
    ((capPairIso (dual D X) X).hom ≫ ε_ X (dual D X))

/-- Its actual adjunction evaluation is exactly the chosen rigid cap. -/
lemma capGenerator_counit (X : D) :
    (tensorProductFunctor (C := D)).map (capGenerator S X) ≫ canonicalAlgebraCounit S =
      (capPairIso (dual D X) X).hom ≫ ε_ X (dual D X) := by
  exact ((tensorProductRightAdjunction S).homEquiv_counit _ _ _).symm.trans
    (((tensorProductRightAdjunction S).homEquiv _ _).symm_apply_apply _)

/-- The actual cap generator of a simple object cannot vanish. -/
lemma capGenerator_ne_zero (X : D) [Simple X] : capGenerator S X ≠ 0 := by
  letI := S.simple_rightDual X
  intro hz
  have h := capGenerator_counit S X
  rw [hz, Functor.map_zero, zero_comp] at h
  apply exactPairing_evaluation_ne_zero X (dual D X)
  exact (cancel_epi (capPairIso (dual D X) X).hom).mp (by simpa using h.symm)

/-- Actual retracts of objects give actual factorizations of their cap
generators, by rigid mate compatibility with evaluation. -/
lemma capGenerator_retract {X Y : D} (r : Retract X Y) :
    capPairMap (dualMap D r.r) r.i ≫ capGenerator S Y = capGenerator S X := by
  apply ((tensorProductRightAdjunction S).homEquiv _ _).symm.injective
  change (tensorProductFunctor (C := D)).map
    (capPairMap (dualMap D r.r) r.i ≫ capGenerator S Y) ≫ canonicalAlgebraCounit S =
    (tensorProductFunctor (C := D)).map (capGenerator S X) ≫ canonicalAlgebraCounit S
  rw [Functor.map_comp, assoc, capGenerator_counit, capGenerator_counit,
    capPairIso_naturality_assoc]
  simp only [tensorHom_def', assoc]
  rw [rightAdjointMate_comp_evaluation r.r, ← whiskerLeft_comp_assoc, r.retract,
    whiskerLeft_id, id_comp]

end Paper18.Category.DiagonalAlgebra
