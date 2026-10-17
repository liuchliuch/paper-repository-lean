import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Limits.Shapes.SplitCoequalizer

/-! # Actual split bar presentations from actual counit sections -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
universe vC uC vD uD
namespace Paper18.Category.BimoduleRelativeTensor.SplitBar
variable {C : Type uC} [Category.{vC} C] {E : Type uD} [Category.{vD} E]
  {F : C ⥤ E} {U : E ⥤ C} (adj : F ⊣ U) (P : E)

/-- A genuine section of an actual adjunction counit constructs the
entire actual split bar coequalizer. Its three remaining equations are
functoriality and actual naturality of the counit. -/
def ofCounitSection (r : P ⟶ F.obj (U.obj P)) (hr : r ≫ adj.counit.app P = 𝟙 P) :
    IsSplitCoequalizer
      (adj.counit.app (F.obj (U.obj P)))
      (F.map (U.map (adj.counit.app P))) (adj.counit.app P) where
  rightSection := r
  leftSection := F.map (U.map r)
  condition := by
    simpa only [Functor.comp_map] using (adj.counit.naturality (adj.counit.app P)).symm
  rightSection_π := hr
  leftSection_bottom := by
    rw [← F.map_comp, ← U.map_comp, hr, U.map_id, F.map_id]
    rfl
  leftSection_top := by
    simpa only [Functor.comp_map] using adj.counit.naturality r

/-- A genuine natural section gives the actual bar coequalizer already
in the functor category, rather than merely object by object. -/
def ofCounitNaturalSection (σ : 𝟭 E ⟶ U ⋙ F) (hσ : σ ≫ adj.counit = 𝟙 (𝟭 E)) :
    IsSplitCoequalizer (Functor.whiskerLeft (U ⋙ F) adj.counit)
      (Functor.whiskerRight adj.counit (U ⋙ F)) adj.counit where
  rightSection := σ
  leftSection := Functor.whiskerRight σ (U ⋙ F)
  condition := by
    apply NatTrans.ext
    funext Q
    exact (ofCounitSection adj Q (σ.app Q) (congrArg (fun k => k.app Q) hσ)).condition
  rightSection_π := hσ
  leftSection_bottom := by
    apply NatTrans.ext
    funext Q
    exact (ofCounitSection adj Q (σ.app Q) (congrArg (fun k => k.app Q) hσ)).leftSection_bottom
  leftSection_top := by
    apply NatTrans.ext
    funext Q
    exact (ofCounitSection adj Q (σ.app Q) (congrArg (fun k => k.app Q) hσ)).leftSection_top

end Paper18.Category.BimoduleRelativeTensor.SplitBar
