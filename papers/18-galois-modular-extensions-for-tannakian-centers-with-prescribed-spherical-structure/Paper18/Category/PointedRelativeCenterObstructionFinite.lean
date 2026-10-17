import Paper18.Category.PointedRelativeCenterObstructionNeutralKernel

/-! # The finite-extension quasi relative center for an arbitrary fourth cocycle

The finite extension and primitive are the actual constructed ones. No
primitive or pentagon-defect certificate is an input of these definitions.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
namespace Paper18.Category.PointedRelativeCenterObstruction
open FiniteCohomologyKilling QuasiFusion
variable {G : Type} [Group G] [Fintype G] (ω : FourCocycle G ℂˣ)

/-- Actual homogeneous relative-central objects over the constructed finite
extension, with its actual normalized primitive associator. -/
abbrev FiniteQuasiRelativeCenter :=
  QuasiRelativeCenter
    (UniversalExtension.projection (G := G) (R := ZMod (Fintype.card G)))
    ω.finitePrimitive ω (fun a b c d => ω.finitePrimitive_spec a b c d)

/-- The actual neutral component, with its derived genuine monoidal structure. -/
abbrev FiniteNeutralComponent :=
  NeutralComponent
    (UniversalExtension.projection (G := G) (R := ZMod (Fintype.card G)))
    ω.finitePrimitive ω (fun a b c d => ω.finitePrimitive_spec a b c d)

/-- Genuine neutral realization for every actual normalized fourth cocycle:
no finite primitive, neutral-center identification, or coherence witness is
supplied by the caller. -/
def finiteNeutralCenterEquivalence : FiniteNeutralComponent ω ≌
    Center (CocycleVec (kernelCocycle ω)) :=
  NeutralComponent.kernelCenterEquivalence
    (UniversalExtension.projection (G := G) (R := ZMod (Fintype.card G)))
    ω.finitePrimitive ω (fun a b c d => ω.finitePrimitive_spec a b c d)

instance finiteNeutralCenterEquivalence_monoidal :
    (finiteNeutralCenterEquivalence ω).functor.Monoidal :=
  NeutralComponent.toKernelCenter_monoidal _ _ _ _
instance finiteNeutralCenterEquivalence_braided :
    (finiteNeutralCenterEquivalence ω).functor.Braided :=
  NeutralComponent.toKernelCenter_braided _ _ _ _
instance finiteNeutralCenterEquivalence_additive :
    (finiteNeutralCenterEquivalence ω).functor.Additive :=
  NeutralComponent.toKernelCenter_additive _ _ _ _
instance finiteNeutralCenterEquivalence_linear :
    (finiteNeutralCenterEquivalence ω).functor.Linear ℂ :=
  NeutralComponent.toKernelCenter_linear _ _ _ _

/-- The actual associator has the derived positive fourth-cocycle defect.
Identifying the inverse Picard-obstruction convention is a separate step. -/
theorem finite_pentagon_defect (W X Y Z : FiniteQuasiRelativeCenter ω) :
    (α_ W X Y).hom ▷ Z ≫ (α_ W (X ⊗ Y) Z).hom ≫ W ◁ (α_ X Y Z).hom =
      (ω.val W.degree X.degree Y.degree Z.degree : ℂ) •
        ((α_ (W ⊗ X) Y Z).hom ≫ (α_ W X (Y ⊗ Z)).hom) :=
  QuasiRelativeCenter.pentagon_defect
    (UniversalExtension.projection (G := G) (R := ZMod (Fintype.card G)))
    ω.finitePrimitive ω (fun a b c d => ω.finitePrimitive_spec a b c d) W X Y Z

end Paper18.Category.PointedRelativeCenterObstruction
