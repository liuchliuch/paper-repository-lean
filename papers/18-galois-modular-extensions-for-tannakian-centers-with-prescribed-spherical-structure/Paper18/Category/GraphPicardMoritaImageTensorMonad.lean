import Paper18.Category.GraphPicardMoritaImageTensorMonadBasic

/-! # Actual multiplication compatibility of the rigid projection monad -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open Functor.LaxMonoidal Functor.OplaxMonoidal
open scoped MonObj
universe v u w u'
namespace Paper18.Category.GraphPicard.MoritaImage

/-- Closing two adjacent legs is the actual associative algebra closure. -/
lemma rightClosure_twice {E : Type u'} [Category.{v} E] [MonoidalCategory E]
    (X A : E) (c : A ⟶ 𝟙_ E) :
    ((X ⊗ A) ◁ c) ≫ (ρ_ (X ⊗ A)).hom ≫ (X ◁ c) ≫ (ρ_ X).hom =
      (α_ X A A).hom ≫ (X ◁ ((c ⊗ₘ c) ≫ (λ_ (𝟙_ E)).hom)) ≫ (ρ_ X).hom := by
  rw [tensorHom_def']
  simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
  monoidal

/-- The actual closure is natural in its surviving leg. -/
@[reassoc] lemma rightClosure_naturality {E : Type u'} [Category.{v} E] [MonoidalCategory E]
    {X Y A : E} (f : X ⟶ Y) (c : A ⟶ 𝟙_ E) :
    f ▷ A ≫ (Y ◁ c) ≫ (ρ_ Y).hom = (X ◁ c) ≫ (ρ_ X).hom ≫ f := by
  rw [← whisker_exchange_assoc, rightUnitor_naturality f]

attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [HasFiniteBiproducts C] [HasKernels C] [MonoidalCategory C]
  [MonoidalPreadditive C] [MonoidalLinear ℂ C] [RightRigidCategory C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {D : Type u'} [Category.{v} D] [Preadditive D] [Linear ℂ D]
  [HasFiniteBiproducts D] [HasKernels D] [MonoidalCategory D]
  [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  (F : C ⥤ D) [F.Additive] [F.Linear ℂ] [F.Monoidal]
open DiagonalAlgebra

/-- Genuine multiplication compatibility of the actual rigid projection
comparison, proved by the actual counit and actual tensor coherence. -/
lemma rightTensorComparison_mul (X : C) :
    (α_ X (semisimpleAdjointAlgebra S F) (semisimpleAdjointAlgebra S F)).hom ≫
      (X ◁ μ[semisimpleAdjointAlgebra S F]) ≫ rightTensorComparison S F X =
    ((rightTensorComparison S F X) ▷ semisimpleAdjointAlgebra S F) ≫
      rightTensorComparison S F ((semisimpleRightAdjoint S F).obj (F.obj X)) ≫
        (semisimpleRightAdjoint S F).map
          ((semisimpleRightAdjunction S F).counit.app (F.obj X)) := by
  let A := semisimpleAdjointAlgebra S F
  let c := semisimpleAdjointAlgebraCounit S F
  let adj := semisimpleRightAdjunction S F
  apply (adj.homEquiv ((X ⊗ A) ⊗ A) (F.obj X)).symm.injective
  change F.map ((α_ X A A).hom ≫ (X ◁ μ[A]) ≫ rightTensorComparison S F X) ≫
    adj.counit.app (F.obj X) =
    F.map (((rightTensorComparison S F X) ▷ A) ≫
      rightTensorComparison S F ((semisimpleRightAdjoint S F).obj (F.obj X)) ≫
        (semisimpleRightAdjoint S F).map (adj.counit.app (F.obj X))) ≫
          adj.counit.app (F.obj X)
  calc
    _ = δ F (X ⊗ A) A ≫ (δ F X A ▷ F.obj A) ≫
        (α_ (F.obj X) (F.obj A) (F.obj A)).hom ≫
          (F.obj X ◁ ((c ⊗ₘ c) ≫ (λ_ (𝟙_ D)).hom)) ≫ (ρ_ (F.obj X)).hom := by
      simp only [F.map_comp, Category.assoc]
      rw [rightTensorComparison_counit, ← δ_natural_right_assoc]
      rw [← MonoidalCategory.whiskerLeft_comp_assoc,
        semisimpleAdjointAlgebra_mul_counit]
      simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
      rw [← Functor.OplaxMonoidal.associativity_assoc]
    _ = _ := by
      symm
      simp only [F.map_comp, Category.assoc]
      have hn := adj.counit.naturality (adj.counit.app (F.obj X))
      simp only [Functor.comp_map, Functor.id_map, Functor.comp_obj, Functor.id_obj] at hn
      rw [hn, rightTensorComparison_counit_assoc, ← δ_natural_left_assoc,
        rightClosure_naturality_assoc, rightTensorComparison_counit,
        ← rightClosure_naturality_assoc (δ F X A) c,
        rightClosure_twice (F.obj X) (F.obj A) c]

/-- The actual adjunction monad is isomorphic to actual right tensoring
by its actual right-adjoint unit algebra. -/
def rightTensorMonadIso :
    ModuleInternalHom.rightTensorMonad (semisimpleAdjointAlgebra S F) ≅
      (semisimpleRightAdjunction S F).toMonad :=
  MonadIso.mk (rightTensorComparisonIso S F)
    (fun X => by
      simpa only [ModuleInternalHom.rightTensorMonad_unit,
        NatIso.ofComponents_hom_app, asIso_hom, Category.assoc] using
          rightTensorComparison_unit S F X)
    (fun X => by
      rw [ModuleInternalHom.rightTensorMonad_mul]
      change ((α_ X (semisimpleAdjointAlgebra S F) (semisimpleAdjointAlgebra S F)).hom ≫
        (X ◁ μ[semisimpleAdjointAlgebra S F])) ≫ rightTensorComparison S F X =
          ((rightTensorComparison S F X ▷ semisimpleAdjointAlgebra S F) ≫
            rightTensorComparison S F ((semisimpleRightAdjoint S F).obj (F.obj X))) ≫
              (semisimpleRightAdjoint S F).map
                ((semisimpleRightAdjunction S F).counit.app (F.obj X))
      simpa only [Category.assoc] using rightTensorComparison_mul S F X)

end Paper18.Category.GraphPicard.MoritaImage
