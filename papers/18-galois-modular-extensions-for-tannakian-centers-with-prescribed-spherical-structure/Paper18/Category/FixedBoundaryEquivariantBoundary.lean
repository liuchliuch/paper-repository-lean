import Paper18.Category.FixedBoundaryEquivariantTransport

/-!
# The specified boundary on equivariantized modules

Fixed-boundary natural isomorphisms retain their compatibility with regular
translations. They therefore give actual natural isomorphisms after
passing to the genuine equivariantization, with the original components.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
universe v u
namespace Paper18.Category
variable {G : Type} [Group G] [Fintype G]
  {N : Type u} [Category.{v} N] [Preadditive N] [Linear ℂ N]
  [MonoidalCategory N] [BraidedCategory N]
  (i : FDRep ℂ G ⥤ N) [i.Monoidal]
  {P Q : BoundaryAutoequivalence i}

/-- Equation A.1 retains the actual action comparison as well as the
module structure. -/
def BoundaryIso.regularActionTransformation (f : BoundaryIso i P Q) :
    WeakAction.Intertwiner.Transformation P.regularActionIntertwiner Q.regularActionIntertwiner where
  natTrans := (f.moduleNatIso (Representation.functions (G := G))).hom
  comm g M := by
    apply Mod_.Hom.ext
    change 𝟙 _ ≫ f.iso.hom.app M.X = f.iso.hom.app M.X ≫ 𝟙 _
    rw [Category.id_comp, Category.comp_id]

/-- The original boundary-compatible natural isomorphism descends to a
natural isomorphism on actual equivariantized modules. -/
def BoundaryIso.equivariantModuleNatIso (f : BoundaryIso i P Q) :
    P.regularActionIntertwiner.equivariantFunctor ≅
      Q.regularActionIntertwiner.equivariantFunctor := by
  let τ := f.regularActionTransformation i
  letI : IsIso τ.natTrans := inferInstanceAs
    (IsIso (f.moduleNatIso (Representation.functions (G := G))).hom)
  exact τ.equivariantNatIso

@[simp] theorem BoundaryIso.equivariantModuleNatIso_hom (f : BoundaryIso i P Q)
    (M : (FixedBoundary.regularAction i).Equivariant) :
    (((f.equivariantModuleNatIso i).hom.app M).hom).hom = f.iso.hom.app M.obj.X := rfl

/-- A genuine functor from the fixed-boundary groupoid to endofunctors of
the actual equivariantization. -/
def fixedBoundaryEquivariantModuleFunctor :
    BoundaryAutoequivalence i ⥤
      ((FixedBoundary.regularAction i).Equivariant ⥤
        (FixedBoundary.regularAction i).Equivariant) where
  obj P := P.regularActionIntertwiner.equivariantFunctor
  map f := (f.equivariantModuleNatIso i).hom
  map_id P := by
    ext M
    apply WeakAction.Equivariant.Hom.ext
    apply Mod_.Hom.ext
    rfl
  map_comp f g := by
    ext M
    apply WeakAction.Equivariant.Hom.ext
    apply Mod_.Hom.ext
    rfl

end Paper18.Category
