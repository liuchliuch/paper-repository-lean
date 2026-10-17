import Paper18.Category.FixedBoundaryEquivariantMonoidal
import Paper18.Category.FixedBoundaryModuleTransformationMonoidal
import Paper18.Category.FixedBoundaryEquivariantBoundary

/-! # Monoidal natural isomorphisms after actual fixed-boundary transport -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
universe v u
namespace Paper18.Category
variable {G : Type} [Group G] [Fintype G]
  {N : Type u} [Category.{v} N] [Preadditive N] [Linear ℂ N]
  [MonoidalCategory N] [BraidedCategory N]
  [MonoidalPreadditive N] [MonoidalLinear ℂ N]
  [RightRigidCategory N] [HasCoequalizers N]
  (i : FDRep ℂ G ⥤ N) [i.Braided] {P Q : BoundaryAutoequivalence i}

/-- The actual transformation of regular-action intertwiners retains the
original ambient monoidality. -/
instance BoundaryIso.regularActionTransformationMonoidal (f : BoundaryIso i P Q) :
    NatTrans.IsMonoidal (f.regularActionTransformation i).natTrans := by
  change NatTrans.IsMonoidal (f.moduleNatIso Representation.functions).hom
  infer_instance

/-- The fixed-boundary module natural isomorphism is genuinely monoidal
also after actual equivariantization. -/
instance BoundaryIso.equivariantModuleNatIsoMonoidal (f : BoundaryIso i P Q) :
    NatTrans.IsMonoidal (f.equivariantModuleNatIso i).hom := by
  change NatTrans.IsMonoidal (f.regularActionTransformation i).equivariantNatTrans
  infer_instance

end Paper18.Category
