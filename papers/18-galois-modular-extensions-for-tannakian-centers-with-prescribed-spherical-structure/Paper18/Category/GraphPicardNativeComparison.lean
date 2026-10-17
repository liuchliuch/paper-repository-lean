import Paper18.Category.GraphPicardCentralFunctor
import Paper18.Category.MonoidalOppositeFusion

/-! # Exact comparison with the two native alpha-induction functors

The source is the actual monoidal opposite. The positive center embedding
of the original category becomes native negative alpha induction, and
vice versa. These genuine ordinary natural isomorphisms keep that sign
and source convention explicit.
-/
noncomputable section
set_option maxHeartbeats 2000000
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open MonoidalOpposite MonoidalLeftAction
universe v u vM uM
namespace Paper18.Category.GraphPicard
variable (D : Type u) [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
  (M : Type uM) [Category.{vM} M] [Preadditive M] [Linear ℂ M]
  [MonoidalLeftAction Dᴹᵒᵖ M]
  [∀ X : Dᴹᵒᵖ, (MonoidalLeftAction.actionLeft M X).Additive]
  [∀ X : Dᴹᵒᵖ, (MonoidalLeftAction.actionLeft M X).Linear ℂ]

/-- The actual positive central action is native negative alpha
induction after the actual ordinary opposite equivalence. -/
def rightPositiveNativeIso : Drinfeld.positive D ⋙ rightCentralAction D M ≅
    mopFunctor D ⋙ ModuleAlphaInduction.negative Dᴹᵒᵖ M :=
  NatIso.ofComponents (fun X =>
    (ModuleAlphaInduction.centralAction Dᴹᵒᵖ M).mapIso (oppositePositiveIso X))
    (fun {X Y} f => by
      apply ModuleFunctor.bundled_hom_ext
      ext m
      change f.mop ⊵ₗ m ≫ (𝟙 (mop Y)) ⊵ₗ m =
        (𝟙 (mop X)) ⊵ₗ m ≫ f.mop ⊵ₗ m
      simp)

/-- The actual negative central action is native positive alpha
induction after the same actual ordinary opposite equivalence. -/
def rightNegativeNativeIso : Drinfeld.negative D ⋙ rightCentralAction D M ≅
    mopFunctor D ⋙ ModuleAlphaInduction.positive Dᴹᵒᵖ M :=
  NatIso.ofComponents (fun X =>
    (ModuleAlphaInduction.centralAction Dᴹᵒᵖ M).mapIso (oppositeNegativeIso X))
    (fun {X Y} f => by
      apply ModuleFunctor.bundled_hom_ext
      ext m
      change f.mop ⊵ₗ m ≫ (𝟙 (mop Y)) ⊵ₗ m =
        (𝟙 (mop X)) ⊵ₗ m ≫ f.mop ⊵ₗ m
      simp)

end Paper18.Category.GraphPicard
