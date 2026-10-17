import Paper18.Category.PointedRelativeCenterObstructionKernelActionNeutralSkeleton
import Paper18.Category.EquivariantSemisimple

/-! # Actual weak kernel actions and finite semisimplicity on each coset -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.Limits
namespace Paper18.Category.PointedRelativeCenterObstruction
open FiniteCohomologyKilling
variable {Γ G : Type} [Group Γ] [Fintype Γ] [Group G]
  (p : Γ →* G) (ψ : ThreeCochain Γ ℂˣ) (ω : FourCocycle G ℂˣ)
  (hψ : ∀ a b c d, dThree ψ.val a b c d = ω.val (p a) (p b) (p c) (p d))

/-- The actual inverse-conjugation functor restricted to the actual
quotient-coset full subcategory. -/
def kernelCosetTranslation (g : G) (k : p.ker) : CosetVec p g ⥤ CosetVec p g where
  obj X := ⟨((kernelAction p ψ ω hψ).ρ k).obj X.obj,
    kernelAction_preserves_support p ψ ω hψ X.property k⟩
  map f := ((kernelAction p ψ ω hψ).ρ k).map f

instance kernelCosetTranslation_additive (g : G) (k : p.ker) :
    (kernelCosetTranslation p ψ ω hψ g k).Additive where
  map_add := by intros; rfl
instance kernelCosetTranslation_linear (g : G) (k : p.ker) :
    (kernelCosetTranslation p ψ ω hψ g k).Linear ℂ where
  map_smul _ _ := rfl

/-- The restricted unit and multiplication are actual inherited natural
isomorphisms; all weak-action laws are inherited actual arrow equations. -/
def kernelCosetAction (g : G) : WeakAction p.ker (CosetVec p g) where
  ρ := kernelCosetTranslation p ψ ω hψ g
  unitIso := NatIso.ofComponents
    (fun X => ObjectProperty.isoMk _ ((kernelAction p ψ ω hψ).unitIso.app X.obj))
    (fun f => (kernelAction p ψ ω hψ).unitIso.hom.naturality f)
  mulIso k l := NatIso.ofComponents
    (fun X => ObjectProperty.isoMk _ ((kernelAction p ψ ω hψ).mulIso k l |>.app X.obj))
    (fun f => ((kernelAction p ψ ω hψ).mulIso k l).hom.naturality f)
  assoc k l m X := by
    simpa only using (kernelAction p ψ ω hψ).assoc k l m X.obj
  one_mul k X := by
    simpa only using (kernelAction p ψ ω hψ).one_mul k X.obj
  mul_one k X := by
    simpa only using (kernelAction p ψ ω hψ).mul_one k X.obj

instance kernelCosetAction_rho_additive (g : G) (k : p.ker) :
    ((kernelCosetAction p ψ ω hψ g).ρ k).Additive :=
  kernelCosetTranslation_additive p ψ ω hψ g k
instance kernelCosetAction_rho_linear (g : G) (k : p.ker) :
    ((kernelCosetAction p ψ ω hψ g).ρ k).Linear ℂ :=
  kernelCosetTranslation_linear p ψ ω hψ g k

instance cosetHasKernels (g : G) : HasKernels (CosetVec p g) :=
  (PointedVec.skeleton (Additive Γ)).fullSubcategoryHasKernels (Supported p g)

instance cosetHom_finiteDimensional (g : G) (X Y : CosetVec p g) :
    FiniteDimensional ℂ (X ⟶ Y) :=
  inferInstanceAs (FiniteDimensional ℂ (X.obj ⟶ Y.obj))

/-- Actual finite simple labels of the genuine projective-equivariant
coset category, constructed from actual induced homogeneous generators. -/
def cosetEquivariantSimpleIndex (g : G) :=
  (kernelCosetAction p ψ ω hψ g).SimpleIndex (cosetSkeleton p g)
instance cosetEquivariantSimpleIndex_fintype (g : G) :
    Fintype (cosetEquivariantSimpleIndex p ψ ω hψ g) := inferInstanceAs
  (Fintype ((kernelCosetAction p ψ ω hψ g).SimpleIndex (cosetSkeleton p g)))

/-- Genuine finite semisimplicity of the actual kernel-equivariant coset
category; no semisimplicity or projectivity certificate is an input. -/
def cosetEquivariantSkeleton (g : G) :
    FiniteSemisimpleSkeleton (kernelCosetAction p ψ ω hψ g).Equivariant
      (cosetEquivariantSimpleIndex p ψ ω hψ g) :=
  (kernelCosetAction p ψ ω hψ g).equivariantSkeleton (cosetSkeleton p g)

end Paper18.Category.PointedRelativeCenterObstruction
