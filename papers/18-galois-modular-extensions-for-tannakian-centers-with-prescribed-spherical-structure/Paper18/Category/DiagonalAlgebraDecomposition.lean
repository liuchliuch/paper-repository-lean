import Paper18.Category.DiagonalAlgebraDeligne
import Paper18.Category.RigidMultiplicity

/-! # The actual diagonal simple-object decomposition

The multiplicities of the transported right-adjoint algebra are computed
from its actual adjunction, not specified as data. Actual Hom coordinates
then assemble the diagonal biproduct isomorphism.
-/
noncomputable section
set_option maxHeartbeats 1000000
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped BigOperators
universe v u w
namespace Paper18.Category.DiagonalAlgebra
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [RightRigidCategory C] [Preadditive C] [Linear ℂ C]
  [MonoidalPreadditive C] [MonoidalLinear ℂ C] [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ C)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι) (J : PivotalStructure C)
  (hC : IsNondegenerate (C := C))

/-- The actual Hom multiplicity of the canonical algebra is the rigid
Kronecker delta pairing of a simple with its actual dual. -/
theorem diagonalAlgebra_multiplicity (i j : ι) :
    Module.finrank ℂ (DeligneProduct.pairObject S S i j ⟶ diagonalAlgebra S J hC) =
      if i = S.dualLabel j then 1 else 0 := by
  let E := Drinfeld.factorizationEquivalence S J hC
  let X := DeligneProduct.pairObject S S i j
  let e := fullyFaithfulHomLinearEquiv E.functor X (diagonalAlgebra S J hC)
  calc
    _ = Module.finrank ℂ (E.functor.obj X ⟶ centerAlgebra S J) := by
      rw [e.finrank_eq]
      exact finrank_hom_iso (Iso.refl _) (E.counitIso.app (centerAlgebra S J))
    _ = Module.finrank ℂ ((Center.forget C).obj (E.functor.obj X) ⟶ 𝟙_ C) :=
      (rigidRightAdjointHomLinearEquiv (Center.forget C)
        (Drinfeld.inductionFunctor S J) (Drinfeld.inductionAdjunction S J)
        (E.functor.obj X) (𝟙_ C)).finrank_eq.symm
    _ = Module.finrank ℂ (S.simpleObject i ⊗ S.simpleObject j ⟶ 𝟙_ C) :=
      finrank_hom_iso ((Center.forget C).mapIso
        (Drinfeld.deligneFactorizationPairIso (S.simpleObject i) (S.simpleObject j)))
        (Iso.refl _)
    _ = Module.finrank ℂ (S.simpleObject i ⟶ (S.simpleObject j)ᘁ) := by
      rw [(tensorRightHomLinearEquiv (S.simpleObject i) (S.simpleObject j)
        ((S.simpleObject j)ᘁ) (𝟙_ C)).finrank_eq]
      exact finrank_hom_iso (Iso.refl _) (λ_ ((S.simpleObject j)ᘁ))
    _ = Module.finrank ℂ (S.simpleObject i ⟶ S.simpleObject (S.dualLabel j)) :=
      finrank_hom_iso (Iso.refl _) (S.dualIso j).symm
    _ = _ := S.finrank_simple_hom_simple i (S.dualLabel j)

/-- The actual finite diagonal sum of simple pairs. -/
def diagonalObject : DeligneProduct C C :=
  ⨁ fun i : ι => DeligneProduct.pairObject S S i (S.dualLabel i)

/-- The actual diagonal biproduct has the same computed Hom multiplicities. -/
theorem diagonalObject_multiplicity (i j : ι) :
    Module.finrank ℂ (DeligneProduct.pairObject S S i j ⟶ diagonalObject S) =
      if i = S.dualLabel j then 1 else 0 := by
  unfold diagonalObject
  rw [finrank_hom_biproduct]
  have hfin (k : ι) :
      Module.finrank ℂ (DeligneProduct.pairObject S S i j ⟶
        DeligneProduct.pairObject S S k (S.dualLabel k)) =
      if (i, j) = (k, S.dualLabel k) then 1 else 0 :=
    DeligneProduct.finrank_pair_hom S S (i, j) (k, S.dualLabel k)
  simp_rw [hfin]
  have h (k : ι) : ((i, j) = (k, S.dualLabel k)) ↔
      (k = i ∧ i = S.dualLabel j) := by
    constructor
    · intro he
      have hi := congrArg Prod.fst he
      have hj := congrArg Prod.snd he
      dsimp only at hi hj
      refine ⟨hi.symm, ?_⟩
      rw [hj, S.dualLabel_involutive, hi]
    · rintro ⟨rfl, he⟩
      have hj := congrArg S.dualLabel he
      rw [S.dualLabel_involutive] at hj
      exact Prod.ext rfl hj.symm
  simp_rw [h]
  by_cases he : i = S.dualLabel j <;> simp [he]

/-- The coordinatewise linear isomorphism is obtained from proved equality
of finite Hom dimensions. -/
def diagonalCoordinatesIso :
    (DeligneProduct.coordinates S S).obj (diagonalAlgebra S J hC) ≅
      (DeligneProduct.coordinates S S).obj (diagonalObject S) where
  hom p := (Classical.choice (FiniteDimensional.nonempty_linearEquiv_of_finrank_eq
    ((diagonalAlgebra_multiplicity S J hC p.1 p.2).trans
      (diagonalObject_multiplicity S p.1 p.2).symm))).toFGModuleCatIso.hom
  inv p := (Classical.choice (FiniteDimensional.nonempty_linearEquiv_of_finrank_eq
    ((diagonalAlgebra_multiplicity S J hC p.1 p.2).trans
      (diagonalObject_multiplicity S p.1 p.2).symm))).toFGModuleCatIso.inv
  hom_inv_id := by
    funext p
    exact (Classical.choice (FiniteDimensional.nonempty_linearEquiv_of_finrank_eq
      ((diagonalAlgebra_multiplicity S J hC p.1 p.2).trans
        (diagonalObject_multiplicity S p.1 p.2).symm))).toFGModuleCatIso.hom_inv_id
  inv_hom_id := by
    funext p
    exact (Classical.choice (FiniteDimensional.nonempty_linearEquiv_of_finrank_eq
      ((diagonalAlgebra_multiplicity S J hC p.1 p.2).trans
        (diagonalObject_multiplicity S p.1 p.2).symm))).toFGModuleCatIso.inv_hom_id

/-- The algebra constructed from the actual adjunction is actually
isomorphic to the diagonal sum Σᵢ Sᵢ ⊠ Sᵢ*. -/
def diagonalAlgebraIso : diagonalAlgebra S J hC ≅ diagonalObject S :=
  (DeligneProduct.coordinates S S).preimageIso (diagonalCoordinatesIso S J hC)

end Paper18.Category.DiagonalAlgebra
