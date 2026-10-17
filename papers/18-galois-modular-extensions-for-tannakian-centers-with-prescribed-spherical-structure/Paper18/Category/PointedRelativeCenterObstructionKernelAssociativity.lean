import Paper18.Category.PointedRelativeCenterObstructionKernelCoherence
import Paper18.Category.PointedRelativeCenterObstructionKernelCocycle

/-! # Actual twisted associativity of the kernel tensor comparison -/
noncomputable section
set_option quotPrecheck false
set_option maxHeartbeats 2000000
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
namespace Paper18.Category.PointedRelativeCenterObstruction
open GradedObject.Monoidal FiniteCohomologyKilling QuasiFusion
variable {Γ G : Type} [Group Γ] [Fintype Γ] [Group G] (p : Γ →* G)
  (ψ : ThreeCochain Γ ℂˣ) (ω : FourCocycle G ℂˣ)
  (hψ : ∀ a b c d, dThree ψ.val a b c d = ω.val (p a) (p b) (p c) (p d))
local notation "K" => p.ker
local notation "F" => kernelRestriction p
local notation "κ" => kernelCocycleOfPrimitive p ψ ω hψ

/-- The actual restriction tensorators carry the actual ambient neutral
associator to the actual derived kernel cocycle associator. -/
lemma kernelTensorHom_twisted_associativity (X Y Z : NeutralVec.{0} p) :
    kernelTensorHom p X Y ▷ (F).obj Z ≫ kernelTensorHom p (X ⊗ Y) Z ≫
      (F).map (show ((X ⊗ Y) ⊗ Z) ⟶ X ⊗ (Y ⊗ Z) from
        (quasiAssociator ψ X.obj Y.obj Z.obj).hom) =
    (scalarAssociator (fun a b c : Additive K => (κ).val a.toMul b.toMul c.toMul)
      ((F).obj X) ((F).obj Y) ((F).obj Z)).hom ≫
        (F).obj X ◁ kernelTensorHom p Y Z ≫ kernelTensorHom p X (Y ⊗ Z) := by
  apply GradedObject.hom_ext
  intro k
  apply tensorObj₃'_ext (X₁ := (F).obj X) (X₂ := (F).obj Y) (X₃ := (F).obj Z)
  intro a b c habc
  change ιTensorObj₃' _ _ _ a b c k habc ≫
    ((kernelTensorHom p X Y ▷ (F).obj Z) k ≫ kernelTensorHom p (X ⊗ Y) Z k ≫
      (quasiAssociator ψ X.obj Y.obj Z.obj).hom (kernelDegree p k)) =
    ιTensorObj₃' _ _ _ a b c k habc ≫
      ((scalarAssociator (fun a b c : Additive K => (κ).val a.toMul b.toMul c.toMul)
        ((F).obj X) ((F).obj Y) ((F).obj Z)).hom k ≫
      (((F).obj X) ◁ kernelTensorHom p Y Z) k ≫ kernelTensorHom p X (Y ⊗ Z) k)
  rw [kernelTensorHom_leftTriple_assoc]
  erw [inclusion_scalarAssociator]
  erw [inclusion_scalarAssociator_assoc]
  simp only [Linear.smul_comp, Category.assoc]
  rw [kernelTensorHom_rightTriple]
  rfl

end Paper18.Category.PointedRelativeCenterObstruction
