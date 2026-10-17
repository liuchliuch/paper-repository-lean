import Mathlib.Algebra.Group.Subgroup.Ker

/-! Native additive descent through a surjective presentation. The
kernel condition will be proved for the actual shadow sums, rather than
assuming the paper's presentation independence. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
variable {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
  (f : A →+ B) (g : A →+ C) (hker : f.ker ≤ g.ker)

include hker in
theorem additive_eq_of_presentations_eq {x y : A} (h : f x = f y) : g x = g y := by
  have hz : x-y ∈ f.ker := by
    change f (x-y) = 0
    rw [map_sub,h,sub_self]
  have hg : g (x-y) = 0 := hker hz
  rw [map_sub] at hg
  exact sub_eq_zero.mp hg

def additiveSurjectiveDescent (hf : Function.Surjective f) : B →+ C where
  toFun b := g (Classical.choose (hf b))
  map_zero' := by
    have he := additive_eq_of_presentations_eq f g hker (x := Classical.choose (hf 0)) (y := 0)
      (by rw [Classical.choose_spec (hf 0),map_zero])
    exact he.trans (map_zero g)
  map_add' b c := by
    have he := additive_eq_of_presentations_eq f g hker
      (x := Classical.choose (hf (b+c))) (y := Classical.choose (hf b)+Classical.choose (hf c))
      (by rw [Classical.choose_spec (hf (b+c)),map_add,Classical.choose_spec (hf b),Classical.choose_spec (hf c)])
    exact he.trans (map_add g _ _)

theorem additiveSurjectiveDescent_apply (hf : Function.Surjective f) (a : A) :
    additiveSurjectiveDescent f g hker hf (f a) = g a :=
  additive_eq_of_presentations_eq f g hker (Classical.choose_spec (hf (f a)))

end Paper28
