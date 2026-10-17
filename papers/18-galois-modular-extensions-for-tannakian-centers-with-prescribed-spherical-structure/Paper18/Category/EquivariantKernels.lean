import Paper18.Category.EquivariantBasic
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# Actual kernels in a weak equivariantization

The kernel is the underlying kernel equipped with the structure induced by
its universal property. The action functors preserve kernels because they
are actual equivalences. No exactness or existence of equivariant kernels
is assumed.
-/

noncomputable section
open Classical CategoryTheory CategoryTheory.Limits
universe v u w
namespace Paper18.Category.WeakAction

section ReflectIsomorphisms
variable {G : Type w} [Group G] {C : Type u} [Category.{v} C]
  (A : WeakAction G C)

/-- An equivariant morphism whose underlying map is invertible has an
actual equivariant inverse. -/
instance forget_reflectsIsomorphisms : A.forget.ReflectsIsomorphisms where
  reflects {X Y} f hf := by
    letI : IsIso f.hom := hf
    let f' : Y ⟶ X :=
      ⟨inv f.hom, fun g => by
        apply (cancel_mono f.hom).mp
        rw [Category.assoc, ← f.comm g, ← Category.assoc, ← Functor.map_comp]
        simp⟩
    exact ⟨⟨f', by apply Equivariant.Hom.ext; simp [f'],
      by apply Equivariant.Hom.ext; simp [f']⟩⟩

end ReflectIsomorphisms

variable {G : Type w} [Group G] {C : Type u} [Category.{v} C]
  [Preadditive C] [Linear ℂ C] [HasKernels C]
  (A : WeakAction G C) [∀ g : G, (A.ρ g).Additive] [∀ g : G, (A.ρ g).Linear ℂ]
  {X Y : A.Equivariant} (f : X ⟶ Y)

/-- Translation of the underlying kernel, followed by the kernel isomorphism
of the equivariant commutative square. -/
def kernelStructureIso (g : G) : (A.ρ g).obj (kernel f.hom) ≅ kernel f.hom :=
  PreservesKernel.iso (A.ρ g) f.hom ≪≫
    kernel.mapIso ((A.ρ g).map f.hom) f.hom
      (X.structureIso g) (Y.structureIso g) (f.comm g)

omit [Linear ℂ C] [∀ g : G, (A.ρ g).Linear ℂ] in
@[reassoc (attr := simp)]
theorem kernelStructureIso_ι (g : G) :
    (A.kernelStructureIso f g).hom ≫ kernel.ι f.hom =
      (A.ρ g).map (kernel.ι f.hom) ≫ (X.structureIso g).hom := by
  simp [kernelStructureIso, kernel.mapIso, kernel.map, Category.assoc]

/-- The underlying categorical kernel with its induced coherent structure. -/
def equivariantKernelObj : A.Equivariant where
  obj := kernel f.hom
  structureIso := A.kernelStructureIso f
  unit := by
    apply (cancel_mono (kernel.ι f.hom)).mp
    rw [A.kernelStructureIso_ι, X.unit]
    exact A.unitIso.hom.naturality (kernel.ι f.hom)
  mul g h := by
    apply (cancel_mono (kernel.ι f.hom)).mp
    simp only [Category.assoc, A.kernelStructureIso_ι]
    rw [← Functor.map_comp_assoc, A.kernelStructureIso_ι, Functor.map_comp,
      Category.assoc, X.mul]
    have hn := (A.mulIso g h).hom.naturality (kernel.ι f.hom)
    simpa only [Functor.comp_map, Category.assoc] using
      congrArg (fun t => t ≫ (X.structureIso (g * h)).hom) hn

/-- The underlying kernel inclusion is equivariant. -/
def equivariantKernelι : A.equivariantKernelObj f ⟶ X :=
  ⟨kernel.ι f.hom, fun g => (A.kernelStructureIso_ι f g).symm⟩

omit [Linear ℂ C] [∀ g : G, (A.ρ g).Linear ℂ] in
@[simp] theorem equivariantKernelι_hom : (A.equivariantKernelι f).hom = kernel.ι f.hom := rfl

@[reassoc (attr := simp)]
theorem equivariantKernelι_condition : A.equivariantKernelι f ≫ f = 0 := by
  apply Equivariant.Hom.ext
  exact kernel.condition f.hom

/-- A vanishing equivariant map factors through the underlying kernel,
and uniqueness of this factorization proves equivariance of the lift. -/
def equivariantKernelLift {Z : A.Equivariant} (k : Z ⟶ X) (hk : k ≫ f = 0) :
    Z ⟶ A.equivariantKernelObj f where
  hom := kernel.lift f.hom k.hom (by simpa using congrArg Equivariant.Hom.hom hk)
  comm g := by
    apply (cancel_mono (kernel.ι f.hom)).mp
    simp only [Category.assoc, equivariantKernelObj, A.kernelStructureIso_ι]
    rw [← Functor.map_comp_assoc, kernel.lift_ι]
    exact k.comm g

@[reassoc (attr := simp)]
theorem equivariantKernelLift_ι {Z : A.Equivariant} (k : Z ⟶ X) (hk : k ≫ f = 0) :
    A.equivariantKernelLift f k hk ≫ A.equivariantKernelι f = k := by
  apply Equivariant.Hom.ext
  exact kernel.lift_ι _ _ _

instance equivariantKernelι_mono : Mono (A.equivariantKernelι f) :=
  A.forget.mono_of_mono_map (inferInstance : Mono (kernel.ι f.hom))

/-- The actual universal kernel fork in the equivariant category. -/
def equivariantKernelIsLimit :
    IsLimit (KernelFork.ofι (A.equivariantKernelι f) (A.equivariantKernelι_condition f)) :=
  KernelFork.IsLimit.ofι' _ _ (fun k hk =>
    ⟨A.equivariantKernelLift f k hk, A.equivariantKernelLift_ι f k hk⟩)

instance equivariant_hasKernel : HasKernel f where
  exists_limit := ⟨⟨KernelFork.ofι (A.equivariantKernelι f)
    (A.equivariantKernelι_condition f), A.equivariantKernelIsLimit f⟩⟩

instance equivariant_hasKernels : HasKernels A.Equivariant where
  has_limit f := A.equivariant_hasKernel f

/-- Forgetting the constructed equivariant kernel recovers a universal
underlying kernel, so the forgetful functor preserves kernels. -/
instance forget_preservesKernel : PreservesLimit (parallelPair f 0) A.forget := by
  apply preservesLimit_of_preserves_limit_cone (A.equivariantKernelIsLimit f)
  exact (KernelFork.isLimitMapConeEquiv
    (KernelFork.ofι (A.equivariantKernelι f) (A.equivariantKernelι_condition f))
      A.forget).symm (kernelIsKernel f.hom)

end Paper18.Category.WeakAction
