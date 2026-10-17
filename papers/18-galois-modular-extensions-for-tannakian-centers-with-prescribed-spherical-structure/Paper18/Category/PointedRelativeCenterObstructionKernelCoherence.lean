import Paper18.Category.PointedRelativeCenterObstructionKernelTensor
import Paper18.Category.PointedRigid

/-! # Actual generator formulas for the kernel tensor comparison -/
noncomputable section
set_option quotPrecheck false
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
namespace Paper18.Category.PointedRelativeCenterObstruction
open GradedObject.Monoidal CategoryTheory.Limits
variable {Γ G : Type} [Group Γ] [Fintype Γ] [Group G] (p : Γ →* G)
local notation "K" => p.ker
local notation "F" => kernelRestriction p

/-- The actual kernel unit fibers agree at the unit degree and are actual
zero objects at every other degree. -/
def kernelUnitIso : 𝟙_ (PointedVec.{0} (Additive K)) ≅ (F).obj (𝟙_ (NeutralVec.{0} p)) :=
  GradedObject.isoMk _ _ (fun a => by
    by_cases ha : a = 0
    · subst a
      exact (PointedVec.unitFiberIso (A := Additive K)) ≪≫
        (PointedVec.unitFiberIso (A := Additive Γ)).symm
    · have hK : IsZero ((𝟙_ (PointedVec.{0} (Additive K))) a) := by
        change IsZero ((PointedVec.simpleObject (Additive K) 0) a)
        exact PointedVec.simpleFiber_isZero (Additive K) 0 a ha
      have hΓ : IsZero ((F).obj (𝟙_ (NeutralVec.{0} p)) a) := by
        change IsZero ((PointedVec.simpleObject (Additive Γ) 0) (kernelDegree p a))
        apply PointedVec.simpleFiber_isZero
        intro hh
        apply ha
        apply Additive.toMul.injective
        apply Subtype.ext
        exact congrArg Additive.toMul hh
      exact hK.iso hΓ)

@[simp] lemma kernelUnitIso_hom_zero : (kernelUnitIso p).hom 0 =
    (PointedVec.unitFiberIso (A := Additive K)).hom ≫
      (PointedVec.unitFiberIso (A := Additive Γ)).inv := by
  simp [kernelUnitIso]

lemma kernelTensorHom_naturality {X X' Y Y' : NeutralVec.{0} p} (f : X ⟶ X') (g : Y ⟶ Y') :
    ((F).map f ⊗ₘ (F).map g) ≫ kernelTensorHom p X' Y' =
      kernelTensorHom p X Y ≫ (F).map (f ⊗ₘ g) := by
  apply GradedObject.hom_ext
  intro k
  apply tensorObj_ext
  intro a b hab
  change ιTensorObj _ _ a b k hab ≫
      (GradedObject.Monoidal.tensorHom ((F).map f) ((F).map g) k ≫
        kernelTensorHom p X' Y' k) = _
  erw [ι_tensorHom_assoc, kernelTensorHom_ι, kernelTensorHom_ι_assoc, ι_tensorHom]
  rfl

/-- The actual left-associated triple tensor comparison preserves each
actual homogeneous convolution summand. -/
@[reassoc] lemma kernelTensorHom_leftTriple (X Y Z : NeutralVec.{0} p)
    (a b c k : Additive K) (h : a + b + c = k) :
    ιTensorObj₃' ((F).obj X) ((F).obj Y) ((F).obj Z) a b c k h ≫
      (kernelTensorHom p X Y ▷ (F).obj Z) k ≫ kernelTensorHom p (X ⊗ Y) Z k =
    ιTensorObj₃' X.obj Y.obj Z.obj (kernelDegree p a) (kernelDegree p b)
      (kernelDegree p c) (kernelDegree p k) (congrArg (kernelDegree p) h) := by
  rw [ιTensorObj₃'_eq _ _ _ a b c k h (a+b) rfl]
  change (ιTensorObj _ _ a b (a+b) rfl ▷ ((F).obj Z c) ≫
    ιTensorObj _ _ (a+b) c k h) ≫
      GradedObject.Monoidal.tensorHom (kernelTensorHom p X Y) (𝟙 _) k ≫ _ = _
  rw [Category.assoc, ι_tensorHom_assoc]
  rw [← MonoidalCategory.tensorHom_id, MonoidalCategory.tensorHom_comp_tensorHom_assoc,
    kernelTensorHom_ι]
  rw [kernelTensorHom_ι]
  rw [ιTensorObj₃'_eq _ _ _ (kernelDegree p a) (kernelDegree p b)
    (kernelDegree p c) (kernelDegree p k) (congrArg (kernelDegree p) h)
    (kernelDegree p (a+b)) rfl]
  rfl

/-- The right-associated triple comparison preserves the same actual
homogeneous convolution summands. -/
@[reassoc] lemma kernelTensorHom_rightTriple (X Y Z : NeutralVec.{0} p)
    (a b c k : Additive K) (h : a + b + c = k) :
    ιTensorObj₃ ((F).obj X) ((F).obj Y) ((F).obj Z) a b c k h ≫
      ((F).obj X ◁ kernelTensorHom p Y Z) k ≫ kernelTensorHom p X (Y ⊗ Z) k =
    ιTensorObj₃ X.obj Y.obj Z.obj (kernelDegree p a) (kernelDegree p b)
      (kernelDegree p c) (kernelDegree p k) (congrArg (kernelDegree p) h) := by
  rw [ιTensorObj₃_eq _ _ _ a b c k h (b+c) rfl]
  change (((F).obj X a) ◁ ιTensorObj _ _ b c (b+c) rfl ≫
    ιTensorObj _ _ a (b+c) k _) ≫
      GradedObject.Monoidal.tensorHom (𝟙 _) (kernelTensorHom p Y Z) k ≫ _ = _
  rw [Category.assoc, ι_tensorHom_assoc]
  rw [← MonoidalCategory.id_tensorHom, MonoidalCategory.tensorHom_comp_tensorHom_assoc,
    kernelTensorHom_ι]
  rw [kernelTensorHom_ι]
  rw [ιTensorObj₃_eq _ _ _ (kernelDegree p a) (kernelDegree p b)
    (kernelDegree p c) (kernelDegree p k) (congrArg (kernelDegree p) h)
    (kernelDegree p (b+c)) rfl]
  rfl

end Paper18.Category.PointedRelativeCenterObstruction
