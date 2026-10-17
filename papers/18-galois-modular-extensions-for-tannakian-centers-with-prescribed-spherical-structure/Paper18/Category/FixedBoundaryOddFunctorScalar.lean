import Paper18.Category.FixedBoundaryOddScalar
import Paper18.Category.FixedBoundaryModuleFaithful

/-!
# Scalar automorphisms of actual fully faithful homogeneous module functors

Fully faithful pullback and the actual homogeneous scalar theorem give
unique complex-unit coordinates on automorphisms of arbitrary actual
fully faithful module functors out of a homogeneous component.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped MonoidalLeftAction
universe v u w v' u'
namespace Paper18.Category.FixedBoundary
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C] [RightRigidCategory C] [Simple (𝟙_ C)]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  (χ : 𝟭 C ≅ 𝟭 C) [NatTrans.IsMonoidal χ.hom] (d : ZMod 2)
  {M : Type u'} [Category.{v'} M] [Preadditive M] [Linear ℂ M]
  [MonoidalLeftAction (SignKernel.Positive χ) M]
  (F : HomogeneousCategory χ d ⥤ M) [F.Full] [F.Faithful]
  [F.Linear ℂ] [F.LeftLinear (SignKernel.Positive χ)]

/-- The actual scalar coordinates also apply to every fully faithful
strong module functor, including genuine module equivalences. -/
theorem homogeneousFunctorAut_unique_scalar
    (τ : F ≅ F) [ModuleFunctor.IsModuleNatural (SignKernel.Positive χ) τ.hom]
    (i : {i : ι // Homogeneous χ d (S.simpleObject i)}) :
    ∃! z : ℂˣ, ∀ X : HomogeneousCategory χ d,
      τ.hom.app X = (z : ℂ) • 𝟙 (F.obj X) := by
  let σ := ModuleFunctor.fullyFaithfulModuleAut F τ
  obtain ⟨z, hz, hu⟩ := homogeneousModuleAut_unique_scalar S χ d σ i
  refine ⟨z, ?_, ?_⟩
  · intro X
    calc
      τ.hom.app X = F.map (σ.hom.app X) :=
        (ModuleFunctor.fullyFaithfulModuleAut_map F τ X).symm
      _ = F.map ((z : ℂ) • 𝟙 X) := congrArg (fun f => F.map f) (hz X)
      _ = _ := by rw [Functor.map_smul, F.map_id]
  · intro y hy
    apply hu y
    intro X
    apply F.map_injective
    calc
      F.map (σ.hom.app X) = τ.hom.app X :=
        ModuleFunctor.fullyFaithfulModuleAut_map F τ X
      _ = (y : ℂ) • 𝟙 (F.obj X) := hy X
      _ = F.map ((y : ℂ) • 𝟙 X) := by rw [Functor.map_smul, F.map_id]

end Paper18.Category.FixedBoundary
