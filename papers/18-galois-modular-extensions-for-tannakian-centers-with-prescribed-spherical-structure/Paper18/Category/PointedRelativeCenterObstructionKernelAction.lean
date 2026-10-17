import Paper18.Category.PointedRelativeCenterObstructionKernelActionBasic

/-! # The actual weak kernel action on graded vectors

The endofunctors are genuine fiber pullbacks; the natural multiplication
maps have the actual cochain coefficient whose cocycle identity was
proved from mixed pentagons.
-/
noncomputable section
set_option quotPrecheck false
open Classical CategoryTheory CategoryTheory.Category
namespace Paper18.Category.PointedRelativeCenterObstruction
open FiniteCohomologyKilling CrossedExtension
variable {Γ G : Type} [Group Γ] [Fintype Γ] [Group G]
  (p : Γ →* G) (ψ : ThreeCochain Γ ℂˣ) (ω : FourCocycle G ℂˣ)
  (hψ : ∀ a b c d, dThree ψ.val a b c d = ω.val (p a) (p b) (p c) (p d))
local notation "Vec" => PointedVec.{0} (Additive Γ)

/-- A genuine weak categorical action of the actual kernel, with actual
fiber isomorphisms and derived associativity and unit laws. -/
def kernelAction : WeakAction p.ker Vec :=
  scalarPullbackAction
    (fun k a => Additive.ofMul (kernelActionDegree p k a.toMul))
    (fun a => by simp)
    (fun k l a => by simp)
    (fun k l a => kernelActionScalar p ψ k l a.toMul)
    (fun k a => kernelActionScalar_one_left p ψ k a.toMul)
    (fun k a => kernelActionScalar_one_right p ψ k a.toMul)
    (fun k l m a => kernelActionScalar_assoc p ψ ω hψ k l m a.toMul)

instance kernelAction_rho_additive (k : p.ker) : ((kernelAction p ψ ω hψ).ρ k).Additive where
  map_add := by intros; rfl

instance kernelAction_rho_linear (k : p.ker) : ((kernelAction p ψ ω hψ).ρ k).Linear ℂ where
  map_smul _ _ := rfl

@[simp] lemma kernelAction_rho_obj (k : p.ker) (X : Vec) (a : Additive Γ) :
    ((kernelAction p ψ ω hψ).ρ k).obj X a =
      X (Additive.ofMul (kernelActionDegree p k a.toMul)) := rfl

@[simp] lemma kernelAction_rho_map (k : p.ker) {X Y : Vec} (f : X ⟶ Y) (a : Additive Γ) :
    ((kernelAction p ψ ω hψ).ρ k).map f a =
      f (Additive.ofMul (kernelActionDegree p k a.toMul)) := rfl

/-- The actual action preserves every actual quotient-coset component. -/
lemma kernelAction_preserves_support {g : G} {X : Vec} (hX : Supported p g X) (k : p.ker) :
    Supported p g (((kernelAction p ψ ω hψ).ρ k).obj X) := by
  intro a ha
  exact hX (Additive.ofMul (kernelActionDegree p k a.toMul))
    (by simpa only [toMul_ofMul, kernelActionDegree_projection] using ha)

end Paper18.Category.PointedRelativeCenterObstruction
