import Paper18.Category.DrinfeldCoendModulesBasic
import Paper18.Category.DrinfeldInductionBasic
import Paper18.Category.SemisimpleCoend

/-! # The actual dual-pair coend diagram in the Deligne product -/
noncomputable section
set_option maxHeartbeats 2000000
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits Opposite
open scoped TensorProduct
universe v u w
namespace Paper18.Category.DrinfeldCoendModules
attribute [local instance 2000] RightRigidCategory.rightDual
open DiagonalAlgebra
variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
  [RightRigidCategory D] [Preadditive D] [Linear ℂ D]
  [MonoidalPreadditive D] [MonoidalLinear ℂ D] [HasKernels D] [HasFiniteBiproducts D]
  [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ D)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton D ι)

lemma capPairMap_comp {X X' X'' Y Y' Y'' : D}
    (f : X ⟶ X') (f' : X' ⟶ X'') (g : Y ⟶ Y') (g' : Y' ⟶ Y'') :
    capPairMap f g ≫ capPairMap f' g' = capPairMap (f ≫ f') (g ≫ g') := by
  dsimp only [capPairMap]
  rw [← Functor.map_comp]
  congr 1

lemma capPairMap_id (X Y : D) : capPairMap (𝟙 X) (𝟙 Y) =
    𝟙 (DeligneProduct.externalObject X Y) :=
  (Mat_.embedding (LinearTensor D D)).map_id _

/-- The actual bilinear diagram whose diagonal values are dual cap pairs. -/
def capDiagram : Dᵒᵖ ⥤ D ⥤ DeligneProduct D D where
  obj U :=
    { obj V := DeligneProduct.externalObject (dual D U.unop) V
      map f := capPairMap (𝟙 _) f
      map_id V := capPairMap_id _ _
      map_comp f g := by rw [capPairMap_comp]; simp }
  map f :=
    { app V := capPairMap (dualMap D f.unop) (𝟙 V)
      naturality {V W} f := by
        dsimp
        rw [capPairMap_comp, capPairMap_comp]
        simp }
  map_id U := by
    apply NatTrans.ext
    funext V
    change capPairMap (dualMap D (𝟙 U.unop)) (𝟙 V) = 𝟙 _
    simpa only [dualMap, rightAdjointMate_id] using
      (capPairMap_id (dual D U.unop) V)
  map_comp f g := by
    apply NatTrans.ext
    funext V
    change capPairMap (dualMap D (g.unop ≫ f.unop)) (𝟙 V) =
      capPairMap (dualMap D f.unop) (𝟙 V) ≫ capPairMap (dualMap D g.unop) (𝟙 V)
    rw [capPairMap_comp]
    simp only [dualMap, comp_rightAdjointMate, id_comp]

instance capDiagram_obj_additive (U : Dᵒᵖ) : ((capDiagram (D := D)).obj U).Additive where
  map_add := by
    intros
    ext ⟨⟩ ⟨⟩
    exact TensorProduct.tmul_add _ _ _
instance capDiagram_obj_linear (U : Dᵒᵖ) : ((capDiagram (D := D)).obj U).Linear ℂ where
  map_smul f c := by
    ext ⟨⟩ ⟨⟩
    exact TensorProduct.tmul_smul c _ _
instance capDiagram_additive : (capDiagram (D := D)).Additive where
  map_add := by
    intros
    ext V
    simp [capDiagram, capPairMap, dualMap, Drinfeld.rightAdjointMate_add,
      TensorProduct.add_tmul]
instance capDiagram_linear : (capDiagram (D := D)).Linear ℂ where
  map_smul f c := by
    ext V
    simp [capDiagram, capPairMap, dualMap, Drinfeld.rightAdjointMate_smul,
      TensorProduct.smul_tmul]

/-- The actual adjunction cap generators form an actual cowedge. -/
def capCowedge : Cowedge (capDiagram (D := D)) :=
  Cowedge.mk (canonicalAlgebra S) (capGenerator S)
    (fun _ _ f => capGenerator_dinaturality S f)

/-- The canonical finite simple-diagonal coend exists in the actual
Deligne product, with no pivotal structure. -/
def capHasCoend : HasCoend (capDiagram (D := D)) :=
  S.semisimpleHasCoend capDiagram

/-- The actual coend map is fixed by its actual cap generators. -/
def capCoendMap :
    letI := capHasCoend S
    coend (capDiagram (D := D)) ⟶ canonicalAlgebra S := by
  letI := capHasCoend S
  exact coend.desc (capGenerator S) (fun _ _ f => capGenerator_dinaturality S f)

@[reassoc]
lemma capCoendMap_ι (X : D) :
    letI := capHasCoend S
    coend.ι (capDiagram (D := D)) X ≫ capCoendMap S = capGenerator S X := by
  letI := capHasCoend S
  exact coend.ι_desc _ _ X

/-- Actual cap generation proves that this particular coend map is epi. -/
theorem capCoendMap_epi :
    letI := capHasCoend S
    Epi (capCoendMap S) := by
  letI := capHasCoend S
  exact epi_of_capGenerators S (capCoendMap S) (fun X => ⟨coend.ι capDiagram X, capCoendMap_ι S X⟩)

end Paper18.Category.DrinfeldCoendModules
