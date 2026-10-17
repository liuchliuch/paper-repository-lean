import Paper18.Category.DrinfeldCoendModulesCoend
import Paper18.Category.DrinfeldInductionCoend

/-! # The proved universal property of actual diagonal cap generators -/
noncomputable section
set_option maxHeartbeats 2000000
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits Opposite
universe v u w v' u'
namespace Paper18.Category.DrinfeldCoendModules
attribute [local instance 2000] RightRigidCategory.rightDual
open DiagonalAlgebra
variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
  [RightRigidCategory D] [Preadditive D] [Linear ℂ D]
  [MonoidalPreadditive D] [MonoidalLinear ℂ D] [HasKernels D] [HasFiniteBiproducts D]
  [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ D)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton D ι)
  {E : Type u'} [Category.{v'} E] (G : DeligneProduct D D ⥤ E)
  [PreservesColimit (multispanIndexCoend (capDiagram (D := D))).multispan G]

/-- Actual dinatural families descend through the actual canonical algebra,
after any functor preserving this actual coend. -/
def capGeneratorDesc {W : E}
    (k : ∀ X : D, G.obj (DeligneProduct.externalObject (dual D X) X) ⟶ W)
    (hk : ∀ {X Y : D} (f : X ⟶ Y),
      G.map (capPairMap (dualMap D f) (𝟙 X)) ≫ k X =
        G.map (capPairMap (𝟙 (dual D Y)) f) ≫ k Y) :
    G.obj (canonicalAlgebra S) ⟶ W := by
  letI := capHasCoend S
  exact G.map (capCoendIso S).inv ≫
    Drinfeld.mappedCoendDesc (capDiagram (D := D)) G k hk

@[reassoc]
lemma capGenerator_desc {W : E}
    (k : ∀ X : D, G.obj (DeligneProduct.externalObject (dual D X) X) ⟶ W)
    (hk : ∀ {X Y : D} (f : X ⟶ Y),
      G.map (capPairMap (dualMap D f) (𝟙 X)) ≫ k X =
        G.map (capPairMap (𝟙 (dual D Y)) f) ≫ k Y) (X : D) :
    G.map (capGenerator S X) ≫ capGeneratorDesc S G k hk = k X := by
  letI := capHasCoend S
  dsimp only [capGeneratorDesc]
  have hc : G.map (capCoendIso S).hom ≫ G.map (capCoendIso S).inv = 𝟙 _ :=
    (G.mapIso (capCoendIso S)).hom_inv_id
  rw [← capCoendIso_ι S X, Functor.map_comp]
  simp only [assoc, reassoc_of% hc]
  exact Drinfeld.mappedCoendDesc_ι _ _ _ _ X

/-- The actual preserved cap generators determine all actual morphisms
out of the transported canonical algebra. -/
lemma capGenerator_hom_ext {W : E} {f g : G.obj (canonicalAlgebra S) ⟶ W}
    (h : ∀ X : D, G.map (capGenerator S X) ≫ f = G.map (capGenerator S X) ≫ g) :
    f = g := by
  letI := capHasCoend S
  apply (cancel_epi (G.map (capCoendIso S).hom)).mp
  apply Drinfeld.mappedCoend_hom_ext (capDiagram (D := D)) G
  intro X
  simpa only [← Functor.map_comp_assoc, capCoendIso_ι] using h X

end Paper18.Category.DrinfeldCoendModules
