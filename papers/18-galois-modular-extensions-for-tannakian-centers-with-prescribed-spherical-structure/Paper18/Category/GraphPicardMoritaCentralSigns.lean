import Paper18.Category.GraphPicardMoritaCentralLinear
import Paper18.Category.DrinfeldBasic
import Paper18.Category.RelativeTensorCentralImage

/-! # Actual signed central lifts with frozen original half-braidings

Native endofunctor composition reverses the center braiding. Consequently
the positive lift has reversed source braiding and the negative lift has
the original source braiding. The underlying original functors are frozen
before changing local braiding instances.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open MonoidalOpposite MonoidalLeftAction
universe v u vM uM
namespace Paper18.Category.GraphPicard
variable (D : Type u) [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
  (M : Type uM) [Category.{vM} M] [Preadditive M] [Linear ℂ M]
  [MonoidalLeftAction Dᴹᵒᵖ M]
  [∀ X : Dᴹᵒᵖ, (MonoidalLeftAction.actionLeft M X).Additive]
  [∀ X : Dᴹᵒᵖ, (MonoidalLeftAction.actionLeft M X).Linear ℂ]

/-- The original positive half-braiding, followed by the genuine lift. -/
def positiveCentralLift : D ⥤ Center (ModuleAlphaInduction.End Dᴹᵒᵖ M) :=
  Drinfeld.positive D ⋙ rightCentralLift D M

/-- The original negative half-braiding, followed by the genuine lift. -/
def negativeCentralLift : D ⥤ Center (ModuleAlphaInduction.End Dᴹᵒᵖ M) :=
  Drinfeld.negative D ⋙ rightCentralLift D M

instance positiveCentralLift_monoidal : (positiveCentralLift D M).Monoidal := by
  unfold positiveCentralLift
  infer_instance
instance negativeCentralLift_monoidal : (negativeCentralLift D M).Monoidal := by
  unfold negativeCentralLift
  infer_instance

/-- The frozen original positive lift preserves reversed source braiding. -/
def positiveCentralLiftReverseBraided :
    let F := positiveCentralLift D M
    letI : BraidedCategory D := reverseBraiding D
    F.Braided := by
  let P := Drinfeld.positive D
  let PM : P.Monoidal := inferInstance
  let F := positiveCentralLift D M
  let b (X Y : D) := β_ X Y
  letI : BraidedCategory D := reverseBraiding D
  letI : BraidedCategory (Center D) := reverseBraiding (Center D)
  letI : P.Monoidal := PM
  letI : P.Braided :=
    { toMonoidal := PM
      braided X Y := by
        apply Center.ext
        change 𝟙 _ ≫ (b Y X).inv = (Center.braiding (P.obj Y) (P.obj X)).inv.f ≫ 𝟙 _
        rw [Center.braiding_inv_f]
        simp only [Category.id_comp, Category.comp_id]
        rfl }
  letI : (rightCentralLift D M).Braided := rightCentralLiftReverseBraided D M
  exact inferInstanceAs (P ⋙ rightCentralLift D M).Braided

/-- The frozen original negative lift preserves original source braiding. -/
instance negativeCentralLift_braided : (negativeCentralLift D M).Braided := by
  let P := Drinfeld.negative D
  let PM : P.Monoidal := inferInstance
  let b (X Y : D) := β_ X Y
  letI : BraidedCategory (Center D) := reverseBraiding (Center D)
  letI : P.Monoidal := PM
  letI : P.Braided :=
    { toMonoidal := PM
      braided X Y := by
        apply Center.ext
        change 𝟙 _ ≫ (b X Y).hom = (Center.braiding (P.obj Y) (P.obj X)).inv.f ≫ 𝟙 _
        rw [Center.braiding_inv_f]
        simp only [Category.id_comp, Category.comp_id]
        rfl }
  letI : (rightCentralLift D M).Braided := rightCentralLiftReverseBraided D M
  exact inferInstanceAs (P ⋙ rightCentralLift D M).Braided

/-- The actual lift preserves original centralization despite reversing
its source braiding, since actual centralization is reversal invariant. -/
lemma rightCentralLift_centralizes {Z W : Center D} (h : Centralizes Z W) :
    Centralizes ((rightCentralLift D M).obj Z) ((rightCentralLift D M).obj W) := by
  have hr := (RelativeTensor.centralizes_reverse_iff Z W).mpr h
  letI : BraidedCategory (Center D) := reverseBraiding (Center D)
  letI : (rightCentralLift D M).Braided := rightCentralLiftReverseBraided D M
  exact hr.map (rightCentralLift D M)

/-- The actual signed central images centralize one another. -/
lemma positiveCentralLift_centralizes_negative (X Y : D) :
    Centralizes ((positiveCentralLift D M).obj X) ((negativeCentralLift D M).obj Y) :=
  rightCentralLift_centralizes D M (Drinfeld.positive_centralizes_negative X Y)

section Linear
variable [Preadditive D] [Linear ℂ D] [MonoidalPreadditive D] [MonoidalLinear ℂ D]
  [∀ m : M, (MonoidalLeftAction.actionRight Dᴹᵒᵖ m).Additive]
  [∀ m : M, (MonoidalLeftAction.actionRight Dᴹᵒᵖ m).Linear ℂ]

instance positiveCentralLift_additive : (positiveCentralLift D M).Additive := by
  unfold positiveCentralLift
  infer_instance
instance positiveCentralLift_linear : (positiveCentralLift D M).Linear ℂ := by
  unfold positiveCentralLift
  infer_instance
instance negativeCentralLift_additive : (negativeCentralLift D M).Additive := by
  unfold negativeCentralLift
  infer_instance
instance negativeCentralLift_linear : (negativeCentralLift D M).Linear ℂ := by
  unfold negativeCentralLift
  infer_instance
end Linear

end Paper18.Category.GraphPicard
