import Paper18.Category.DiagonalAlgebraSemisimpleAdjoint
import Paper18.Category.ModuleFunctorFinite
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

/-! # Actual linear natural transformations from their simple components -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.Limits
universe v u v' u' w w'
namespace Paper18.Category.ModuleFunctor
variable {M : Type u} [Category.{v} M] [Preadditive M] [Linear ℂ M]
  [HasKernels M] [HasFiniteBiproducts M]
  [∀ X Y : M, FiniteDimensional ℂ (X ⟶ Y)]
  {N : Type u'} [Category.{v'} N] [Preadditive N] [Linear ℂ N]
  [HasFiniteBiproducts N] [∀ X Y : N, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton M ι)
  (F G : M ⥤ N) [F.Additive] [F.Linear ℂ] [G.Additive] [G.Linear ℂ]

/-- A family on the actual simple representatives determines linear maps
on all actual simple inclusions. -/
def naturalSimpleFamily (a : ∀ i, F.obj (S.simpleObject i) ⟶ G.obj (S.simpleObject i))
    (X : M) (i : ι) :
    (S.simpleObject i ⟶ X) →ₗ[ℂ] (F.obj (S.simpleObject i) ⟶ G.obj X) where
  toFun f := a i ≫ G.map f
  map_add' f g := by simp
  map_smul' r f := by simp

/-- The actual extension of arbitrary simple components to a natural
transformation, constructed from the actual source decompositions. -/
def naturalFromSimpleFamily
    (a : ∀ i, F.obj (S.simpleObject i) ⟶ G.obj (S.simpleObject i)) : F ⟶ G where
  app X := DiagonalAlgebra.homFromImageSimpleFamily S F (naturalSimpleFamily S F G a X)
  naturality {X Y} f := by
    apply DiagonalAlgebra.image_hom_ext S F
    intro i g
    rw [← assoc, ← F.map_comp, DiagonalAlgebra.map_comp_homFromImageSimpleFamily]
    rw [← assoc, DiagonalAlgebra.map_comp_homFromImageSimpleFamily]
    change a i ≫ G.map (g ≫ f) = (a i ≫ G.map g) ≫ G.map f
    rw [G.map_comp, assoc]

@[simp]
lemma naturalFromSimpleFamily_app_simple
    (a : ∀ i, F.obj (S.simpleObject i) ⟶ G.obj (S.simpleObject i)) (i : ι) :
    (naturalFromSimpleFamily S F G a).app (S.simpleObject i) = a i := by
  have h := DiagonalAlgebra.map_comp_homFromImageSimpleFamily S F
    (naturalSimpleFamily S F G a (S.simpleObject i)) i (𝟙 _)
  dsimp only [naturalSimpleFamily, LinearMap.coe_mk, AddHom.coe_mk] at h
  erw [F.map_id, G.map_id, id_comp, comp_id] at h
  exact h

/-- Evaluation at the actual source simples is an actual linear
isomorphism, rather than merely an injectivity bound. -/
def simpleComponentsLinearEquiv : (F ⟶ G) ≃ₗ[ℂ]
    (∀ i, F.obj (S.simpleObject i) ⟶ G.obj (S.simpleObject i)) where
  toFun τ i := τ.app (S.simpleObject i)
  invFun := naturalFromSimpleFamily S F G
  left_inv τ := natTrans_ext_simples S F G _ _ (by intro i; simp)
  right_inv a := funext (naturalFromSimpleFamily_app_simple S F G a)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable [HasKernels N] [HasFiniteLimits N]
  {κ : Type w'} [Fintype κ] (T : FiniteSemisimpleSkeleton N κ)

/-- An ordinary monomorphism between actual additive complex-linear
functors out of a finite semisimple category splits by extending actual
simple-component retractions. No module averaging has been assumed. -/
def splitMonoNatural (τ : F ⟶ G) [Mono τ] : SplitMono τ := by
  let a := fun i => (T.splitMono (τ.app (S.simpleObject i))).retraction
  refine ⟨naturalFromSimpleFamily S G F a, ?_⟩
  apply (simpleComponentsLinearEquiv S F F).injective
  funext i
  change τ.app (S.simpleObject i) ≫
    (naturalFromSimpleFamily S G F a).app (S.simpleObject i) = 𝟙 _
  rw [naturalFromSimpleFamily_app_simple]
  exact (T.splitMono (τ.app (S.simpleObject i))).id

end Paper18.Category.ModuleFunctor
