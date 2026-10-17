import Paper18.Category.DrinfeldInductionHexagon

/-!
# The actual central-induction object

The object is the proved finite semisimple coend. Its half-braiding is the
universal cup-insertion map, whose naturality, unit and tensor hexagon have
been proved. Invertibility follows from the actual pivotal left duals.
-/
noncomputable section
universe v u w
namespace Paper18.Category.Drinfeld
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
attribute [local instance 2000] RightRigidCategory.rightDual

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]

/-- The prescribed pivotal maps provide actual left duals of all objects. -/
def pivotalLeftRigidCategory (J : PivotalStructure C) : LeftRigidCategory C where
  leftDual U := { leftDual := dual C U, exact := J.leftExactPairing U }

variable [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι) (J : PivotalStructure C)

/-- The actual induction commutation maps, with all coherence proved. -/
def inductionLaxHalfBraiding (X : C) : LaxHalfBraiding (inductionUnderlying S X) where
  hom := inductionHalfBraidingHom S J X
  naturality := inductionHalfBraidingHom_naturality S J X
  monoidal := inductionHalfBraidingHom_tensor S J X
  unit := inductionHalfBraidingHom_unit S J X

/-- Actual central induction, on objects. Its underlying object is canonically
the finite direct sum of `Si ⊗ X ⊗ Si*`. -/
def inductionObj (X : C) : Center C :=
  letI := pivotalLeftRigidCategory J
  ⟨inductionUnderlying S X, (inductionLaxHalfBraiding S J X).toHalfBraiding⟩

@[simp] lemma inductionObj_fst (X : C) : (inductionObj S J X).1 = inductionUnderlying S X := rfl

@[simp] lemma inductionObj_halfBraiding_hom (X U : C) :
    ((inductionObj S J X).2.β U).hom = inductionHalfBraidingHom S J X U := rfl

end Paper18.Category.Drinfeld
