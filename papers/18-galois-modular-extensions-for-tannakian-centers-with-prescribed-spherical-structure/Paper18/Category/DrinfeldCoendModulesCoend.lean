import Paper18.Category.DrinfeldCoendModulesDiagram
import Paper18.Category.DiagonalAlgebraPerfect

/-! # The diagonal algebra is the actual dual-pair coend

The coend map is fixed by actual cap generators. It is epi by cap generation,
and an isomorphism by proved finite simple-pair multiplicities. The resulting
coend comparison therefore has a specified, proved normalization.
-/
noncomputable section
set_option maxHeartbeats 2000000
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits Opposite
universe v u w
namespace Paper18.Category.DrinfeldCoendModules
attribute [local instance 2000] RightRigidCategory.rightDual
open DiagonalAlgebra
variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
  [RightRigidCategory D] [Preadditive D] [Linear ℂ D]
  [MonoidalPreadditive D] [MonoidalLinear ℂ D] [HasKernels D] [HasFiniteBiproducts D]
  [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ D)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton D ι)

/-- The actual cap-pair simple sum has the actual canonical diagonal
multiplicities. -/
lemma capCoendObject_multiplicity (i j : ι) :
    Module.finrank ℂ (DeligneProduct.pairObject S S i j ⟶
      S.semisimpleCoendObject (capDiagram (D := D))) =
        if i = S.dualLabel j then 1 else 0 := by
  rw [FiniteSemisimpleSkeleton.semisimpleCoendObject, finrank_hom_biproduct]
  have hfin (k : ι) :
      Module.finrank ℂ (DeligneProduct.pairObject S S i j ⟶
        (capDiagram.obj (op (S.simpleObject k))).obj (S.simpleObject k)) =
          if (i,j) = (S.dualLabel k,k) then 1 else 0 := by
    calc
      _ = Module.finrank ℂ (DeligneProduct.pairObject S S i j ⟶
          DeligneProduct.pairObject S S (S.dualLabel k) k) :=
        finrank_hom_iso (Iso.refl _) (capSimplePairIso S k).symm
      _ = _ := DeligneProduct.finrank_pair_hom S S (i,j) (S.dualLabel k,k)
  simp_rw [hfin]
  have h (k : ι) : ((i,j) = (S.dualLabel k,k)) ↔
      (k = j ∧ i = S.dualLabel j) := by
    constructor
    · intro he
      have hi := congrArg Prod.fst he
      have hj := congrArg Prod.snd he
      dsimp only at hi hj
      exact ⟨hj.symm, hj ▸ hi⟩
    · rintro ⟨rfl, he⟩
      exact Prod.ext he rfl
  simp_rw [h]
  by_cases he : i = S.dualLabel j <;> simp [he]

/-- Finite simple Hom coordinates provide an object isomorphism, used
only to compare actual endomorphism dimensions of the specified coend map. -/
def capCoendCoordinatesIso :
    (DeligneProduct.coordinates S S).obj (S.semisimpleCoendObject (capDiagram (D := D))) ≅
      (DeligneProduct.coordinates S S).obj (canonicalAlgebra S) where
  hom p := (Classical.choice (FiniteDimensional.nonempty_linearEquiv_of_finrank_eq
    ((capCoendObject_multiplicity S p.1 p.2).trans
      (canonicalAlgebra_multiplicity S p.1 p.2).symm))).toFGModuleCatIso.hom
  inv p := (Classical.choice (FiniteDimensional.nonempty_linearEquiv_of_finrank_eq
    ((capCoendObject_multiplicity S p.1 p.2).trans
      (canonicalAlgebra_multiplicity S p.1 p.2).symm))).toFGModuleCatIso.inv
  hom_inv_id := by
    funext p
    exact (Classical.choice (FiniteDimensional.nonempty_linearEquiv_of_finrank_eq
      ((capCoendObject_multiplicity S p.1 p.2).trans
        (canonicalAlgebra_multiplicity S p.1 p.2).symm))).toFGModuleCatIso.hom_inv_id
  inv_hom_id := by
    funext p
    exact (Classical.choice (FiniteDimensional.nonempty_linearEquiv_of_finrank_eq
      ((capCoendObject_multiplicity S p.1 p.2).trans
        (canonicalAlgebra_multiplicity S p.1 p.2).symm))).toFGModuleCatIso.inv_hom_id

/-- An auxiliary object comparison obtained from the proved multiplicities.
The actual coend comparison below is instead the specified cap-generator map. -/
def capCoendObjectIso : S.semisimpleCoendObject (capDiagram (D := D)) ≅ canonicalAlgebra S :=
  (DeligneProduct.coordinates S S).preimageIso (capCoendCoordinatesIso S)

/-- The actual cap-generator map is an isomorphism. -/
theorem capCoendMap_isIso :
    letI := capHasCoend S
    IsIso (capCoendMap S) := by
  letI := capHasCoend S
  letI := DeligneProduct.hasKernels S S
  let T := DeligneProduct.skeleton S S
  let q := capCoendMap S
  letI : Epi q := capCoendMap_epi S
  let s := T.splitEpi q
  letI : Mono s.section_ := s.splitMono.mono
  let e := S.semisimpleCoendIso (capDiagram (D := D)) ≪≫ capCoendObjectIso S
  have hd : Module.finrank ℂ (canonicalAlgebra S ⟶ canonicalAlgebra S) =
      Module.finrank ℂ (coend (capDiagram (D := D)) ⟶ coend (capDiagram (D := D))) :=
    finrank_hom_iso e.symm e.symm
  letI : IsIso s.section_ := isIso_of_mono_end_finrank_eq T s.section_ hd
  refine ⟨⟨s.section_, ?_, s.id⟩⟩
  apply (cancel_epi s.section_).mp
  change s.section_ ≫ (q ≫ s.section_) = s.section_ ≫ 𝟙 _
  rw [← assoc, s.id, id_comp, comp_id]

/-- The canonical algebra's actual coend identification, fixed by the
actual rigid-cap generator at every actual object. -/
def capCoendIso :
    letI := capHasCoend S
    coend (capDiagram (D := D)) ≅ canonicalAlgebra S := by
  letI := capHasCoend S
  letI := capCoendMap_isIso S
  exact asIso (capCoendMap S)

@[reassoc]
lemma capCoendIso_ι (X : D) :
    letI := capHasCoend S
    coend.ι (capDiagram (D := D)) X ≫ (capCoendIso S).hom = capGenerator S X :=
  capCoendMap_ι S X

end Paper18.Category.DrinfeldCoendModules
