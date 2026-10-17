import Paper17.Spheres
import Mathlib.Topology.Homotopy.HomotopyGroup

/-! Literal homotopy groups of a space with a based strong contraction. -/
noncomputable section
open scoped Topology unitInterval Topology.Homotopy
namespace Paper17

/-- A contraction fixing the basepoint contracts each generalized loop
relative to its entire cube boundary. Thus the actual Mathlib homotopy group
has only its identity element. -/
theorem homotopyGroup_eq_one_of_strong_contraction {X : Type*} [TopologicalSpace X]
    (p : X) (H : X × ℝ → X) (hH : Continuous H)
    (h0 : ∀ x, H (x, 0) = x) (h1 : ∀ x, H (x, 1) = p)
    (hfix : ∀ t, H (p, t) = p) (k : ℕ) :
    ∀ a : HomotopyGroup.Pi (k + 1) X p, a = 1 := by
  intro a
  refine Quotient.inductionOn a ?_
  intro f
  apply Quotient.sound
  change Nonempty (f.val.HomotopyRel (@GenLoop.const (Fin (k + 1)) X _ p).val
    (Cube.boundary (Fin (k + 1))))
  refine ⟨{
    toFun := fun q => H (f q.2, (q.1 : ℝ))
    continuous_toFun := hH.comp
      ((f.val.continuous.comp continuous_snd).prodMk
        (continuous_subtype_val.comp continuous_fst))
    map_zero_left := fun y => h0 (f y)
    map_one_left := fun y => h1 (f y)
    prop' := ?_ }⟩
  intro t y hy
  change H (f y, (t : ℝ)) = f y
  have hfy : f y = p := f.property y hy
  rw [hfy, hfix]

end Paper17
