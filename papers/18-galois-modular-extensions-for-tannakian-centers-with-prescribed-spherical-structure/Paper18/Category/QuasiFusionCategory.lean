import Paper18.Category.QuasiFusionFusion

/-! # The actual fusion category attached to a normalized third cocycle

The type wrapper records the chosen associator, so its actual monoidal and
rigid structures can be inferred without choosing among different twists
of the same underlying category.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped BigOperators
namespace Paper18.Category.QuasiFusion
variable {G : Type} [Group G] [Fintype G]

/-- Finite-dimensional complex vector spaces with actual convolution and
the actual associator prescribed by `ψ`. -/
def CocycleVec (_ψ : ThreeCocycle G) := PointedVec (Additive G)

namespace CocycleVec
variable (ψ : ThreeCocycle G)

instance : Category (CocycleVec ψ) := inferInstanceAs (Category (PointedVec (Additive G)))
instance : Preadditive (CocycleVec ψ) := inferInstanceAs (Preadditive (PointedVec (Additive G)))
instance : Linear ℂ (CocycleVec ψ) := inferInstanceAs (Linear ℂ (PointedVec (Additive G)))
instance (X Y : CocycleVec ψ) : FiniteDimensional ℂ (X ⟶ Y) :=
  inferInstanceAs (FiniteDimensional ℂ (∀ a : Additive G, X a ⟶ Y a))
instance : HasKernels (CocycleVec ψ) := inferInstanceAs (HasKernels (PointedVec (Additive G)))
instance : HasFiniteBiproducts (CocycleVec ψ) :=
  inferInstanceAs (HasFiniteBiproducts (PointedVec (Additive G)))
instance : MonoidalCategory (CocycleVec ψ) := twistedMonoidalCategory ψ
instance : MonoidalPreadditive (CocycleVec ψ) :=
  scalarMonoidalPreadditive
    (fun (a b c : Additive G) => ψ.val a.toMul b.toMul c.toMul)
    (fun (a b c d : Additive G) => ψ.pentagon a.toMul b.toMul c.toMul d.toMul)
    (fun (a c : Additive G) => ψ.one₂ a.toMul c.toMul)
instance : MonoidalLinear ℂ (CocycleVec ψ) :=
  scalarMonoidalLinear
    (fun (a b c : Additive G) => ψ.val a.toMul b.toMul c.toMul)
    (fun (a b c d : Additive G) => ψ.pentagon a.toMul b.toMul c.toMul d.toMul)
    (fun (a c : Additive G) => ψ.one₂ a.toMul c.toMul)
instance : RightRigidCategory (CocycleVec ψ) := twistedRightRigid ψ
instance : Simple (𝟙_ (CocycleVec ψ)) := by
  change Simple (PointedVec.simpleObject (Additive G) 0)
  exact PointedVec.simple_simpleObject 0

/-- The actual homogeneous-line skeleton with its actual finite decompositions. -/
def skeleton : FiniteSemisimpleSkeleton (CocycleVec ψ) (Additive G) :=
  PointedVec.skeleton (Additive G)

/-- Every homogeneous line has a constructed actual two-sided tensor inverse. -/
def homogeneousTensorInverse (a : Additive G) :
    TensorInverse ((skeleton ψ).simpleObject a) :=
  scalarHomogeneousTensorInverse
    (fun (a b c : Additive G) => ψ.val a.toMul b.toMul c.toMul)
    (fun (a b c d : Additive G) => ψ.pentagon a.toMul b.toMul c.toMul d.toMul)
    (fun (a c : Additive G) => ψ.one₂ a.toMul c.toMul) a

/-- The genuine categorical fusion basis, derived from the twisted category. -/
def fusionBasis : Paper18.FusionBasis (Additive G) := (skeleton ψ).fusionBasis

@[simp] theorem fpdim_simple (a : Additive G) : (fusionBasis ψ).fpdim a = 1 := by
  have h := (skeleton ψ).fpdim_eq_one_of_tensorInvertible ⟨homogeneousTensorInverse ψ a⟩
  rw [FiniteSemisimpleSkeleton.fpdim_simple] at h
  exact h

/-- All actual simple objects of the twisted category have integral FP dimension. -/
theorem integral : (skeleton ψ).Integral := by
  apply (skeleton ψ).integral_iff_basis.mpr
  intro a
  exact ⟨1, by simpa only [Int.cast_one] using fpdim_simple ψ a⟩

theorem totalFPdim : (fusionBasis ψ).totalFPdim = Fintype.card G := by
  simp [Paper18.FusionBasis.totalFPdim, Fintype.card_additive]

end CocycleVec
end Paper18.Category.QuasiFusion
