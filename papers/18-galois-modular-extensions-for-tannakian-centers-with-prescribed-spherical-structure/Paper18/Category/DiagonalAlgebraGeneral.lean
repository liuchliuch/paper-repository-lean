import Paper18.Category.DiagonalAlgebraSemisimpleUnit
import Paper18.Category.DiagonalAlgebraCenter
import Paper18.Category.FactorizationDeligneBraided
import Paper18.Category.FactorizationEssentialSurjectiveProduct

/-! # The actual diagonal algebra for every finite braided fusion category

The actual central tensor-product functor has an actual right adjoint,
constructed by finite semisimple Hom spaces. Its value at the unit is the
canonical diagonal algebra. No nondegeneracy or factorization-equivalence
hypothesis is used.
-/
noncomputable section
set_option maxHeartbeats 1000000
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped MonObj
universe v u w
namespace Paper18.Category.DiagonalAlgebra
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [RightRigidCategory C] [Preadditive C] [Linear ℂ C]
  [MonoidalPreadditive C] [MonoidalLinear ℂ C] [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ C)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)


/-- The actual central tensor-product functor, with its genuine tensorator. -/
def tensorProductFunctor : DeligneProduct C C ⥤ C :=
  Drinfeld.deligneFactorization C ⋙ Center.forget C

instance tensorProductFunctor_additive : (tensorProductFunctor (C := C)).Additive :=
  inferInstanceAs ((Drinfeld.deligneFactorization C ⋙ Center.forget C).Additive)
instance tensorProductFunctor_linear : (tensorProductFunctor (C := C)).Linear ℂ :=
  inferInstanceAs ((Drinfeld.deligneFactorization C ⋙ Center.forget C).Linear ℂ)
instance tensorProductFunctor_monoidal : (tensorProductFunctor (C := C)).Monoidal :=
  inferInstanceAs ((Drinfeld.deligneFactorization C ⋙ Center.forget C).Monoidal)

/-- The actual right adjoint to tensor product, for arbitrary braided C. -/
def tensorProductRightAdjoint : C ⥤ DeligneProduct C C := by
  letI := DeligneProduct.hasKernels S S
  exact semisimpleRightAdjoint (DeligneProduct.skeleton S S) (tensorProductFunctor (C := C))

/-- Its actual right adjunction. -/
def tensorProductRightAdjunction : tensorProductFunctor (C := C) ⊣ tensorProductRightAdjoint S := by
  letI := DeligneProduct.hasKernels S S
  exact semisimpleRightAdjunction (DeligneProduct.skeleton S S) (tensorProductFunctor (C := C))

instance tensorProductRightAdjoint_laxMonoidal : (tensorProductRightAdjoint S).LaxMonoidal := by
  letI := DeligneProduct.hasKernels S S
  exact inferInstanceAs ((semisimpleRightAdjoint (DeligneProduct.skeleton S S)
    (tensorProductFunctor (C := C))).LaxMonoidal)

/-- The general actual diagonal algebra. -/
def canonicalAlgebra : DeligneProduct C C := by
  letI := DeligneProduct.hasKernels S S
  exact semisimpleAdjointAlgebra (DeligneProduct.skeleton S S) (tensorProductFunctor (C := C))

instance canonicalAlgebraMonObj : MonObj (canonicalAlgebra S) := by
  letI := DeligneProduct.hasKernels S S
  exact inferInstanceAs (MonObj (semisimpleAdjointAlgebra (DeligneProduct.skeleton S S)
    (tensorProductFunctor (C := C))))

/-- Its actual underlying tensor-product counit. -/
def canonicalAlgebraCounit : (tensorProductFunctor (C := C)).obj (canonicalAlgebra S) ⟶ 𝟙_ C := by
  letI := DeligneProduct.hasKernels S S
  exact semisimpleAdjointAlgebraCounit (DeligneProduct.skeleton S S) (tensorProductFunctor (C := C))

/-- The actual algebra is connected for every braided C. -/
theorem canonicalAlgebra_connected :
    Module.finrank ℂ (𝟙_ (DeligneProduct C C) ⟶ canonicalAlgebra S) = 1 := by
  letI := DeligneProduct.hasKernels S S
  exact semisimpleAdjointAlgebra_connected (DeligneProduct.skeleton S S) (tensorProductFunctor (C := C))

/-- The actual canonical diagonal multiplication is commutative for the
explicit reverse-second braiding, without nondegeneracy assumptions. -/
def canonicalAlgebra_commutative :
    letI : BraidedCategory (DeligneProduct C C) := Drinfeld.deligneReverseSecondBraiding C
    IsCommMonObj (canonicalAlgebra S) := by
  letI := DeligneProduct.hasKernels S S
  letI : BraidedCategory (DeligneProduct C C) := Drinfeld.deligneReverseSecondBraiding C
  let G := Drinfeld.deligneFactorization C
  letI : G.Braided := Drinfeld.deligneFactorizationBraided C
  let F := tensorProductFunctor (C := C)
  let A := canonicalAlgebra S
  let e := canonicalAlgebraCounit S
  let a := tensorProductRightAdjunction S
  have hm : μ[A] = a.homEquiv (A ⊗ A) (𝟙_ C)
      (Functor.OplaxMonoidal.δ F A A ≫ (e ⊗ₘ e) ≫ (λ_ (𝟙_ C)).hom) :=
    semisimpleAdjointAlgebra_mul (DeligneProduct.skeleton S S) F
  refine ⟨?_⟩
  change (β_ A A).hom ≫ μ[A] = μ[A]
  rw [hm, ← a.homEquiv_naturality_left]
  apply congrArg (a.homEquiv (A ⊗ A) (𝟙_ C))
  have hb : Functor.LaxMonoidal.μ F A A ≫ F.map (β_ A A).hom =
      ((G.obj A).2.β (F.obj A)).hom ≫ Functor.LaxMonoidal.μ F A A := by
    have h := congrArg (fun f => f.f) (Functor.LaxBraided.braided (F := G) A A)
    simpa only [F, G, tensorProductFunctor, Functor.LaxMonoidal.comp_μ, Functor.comp_map,
      Functor.comp_obj, Center.forget_μ, comp_id, id_comp, Center.comp_f] using h
  apply (cancel_epi (Functor.LaxMonoidal.μ F A A)).1
  rw [← assoc (Functor.LaxMonoidal.μ F A A), hb]
  simp only [assoc, Functor.Monoidal.μ_δ_assoc]
  exact halfBraiding_counit_square (G.obj A) e

end Paper18.Category.DiagonalAlgebra
