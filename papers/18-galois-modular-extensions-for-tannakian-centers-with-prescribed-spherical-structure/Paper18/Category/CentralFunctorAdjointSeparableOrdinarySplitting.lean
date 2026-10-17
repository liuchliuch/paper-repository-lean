import Paper18.Category.ModuleFunctorSemisimpleNatural

/-! # Actual ordinary counit sections from finite semisimple coordinates

This only supplies an ordinary natural section. Its later averaging into
a module natural section is a separate proved operation.
-/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
universe v u v' u' w w'
namespace Paper18.Category.CentralFunctorAdjointSeparable
variable {M : Type u} [Category.{v} M] [Preadditive M] [Linear ℂ M]
  [HasKernels M] [HasFiniteBiproducts M]
  [∀ X Y : M, FiniteDimensional ℂ (X ⟶ Y)]
  {N : Type u'} [Category.{v'} N] [Preadditive N] [Linear ℂ N]
  [HasKernels N] [HasFiniteBiproducts N]
  [∀ X Y : N, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton M ι)
  {κ : Type w'} [Fintype κ] (T : FiniteSemisimpleSkeleton N κ)
  {F G : M ⥤ N} [F.Additive] [F.Linear ℂ] [G.Additive] [G.Linear ℂ]

/-- Actual pointwise epimorphisms between actual additive linear functors
have an ordinary natural section, constructed on the actual source
simple representatives and then extended linearly. -/
def ordinarySplitEpi (τ : F ⟶ G) [∀ X : M, Epi (τ.app X)] : SplitEpi τ := by
  let a := fun i => (T.splitEpi (τ.app (S.simpleObject i))).section_
  refine ⟨ModuleFunctor.naturalFromSimpleFamily S G F a, ?_⟩
  apply (ModuleFunctor.simpleComponentsLinearEquiv S G G).injective
  funext i
  change (ModuleFunctor.naturalFromSimpleFamily S G F a).app (S.simpleObject i) ≫
    τ.app (S.simpleObject i) = 𝟙 _
  rw [ModuleFunctor.naturalFromSimpleFamily_app_simple]
  exact (T.splitEpi (τ.app (S.simpleObject i))).id

end Paper18.Category.CentralFunctorAdjointSeparable
