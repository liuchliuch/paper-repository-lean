import Paper18.Category.PointedRelativeCenterObstructionKernel

/-! # Actual convolution tensor comparison for kernel restriction -/
noncomputable section
set_option quotPrecheck false
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
namespace Paper18.Category.PointedRelativeCenterObstruction
open GradedObject.Monoidal
variable {Γ G : Type} [Group Γ] [Fintype Γ] [Group G] (p : Γ →* G)
local notation "K" => p.ker
local notation "F" => kernelRestriction p

def kernelDegree (a : Additive K) : Additive Γ := Additive.ofMul a.toMul.val

def kernelIndex (a : Additive Γ) (ha : p a.toMul = 1) : Additive K :=
  Additive.ofMul ⟨a.toMul, ha⟩

lemma kernel_second_mem {a b : Additive Γ} {k : Additive K}
    (hab : a + b = kernelDegree p k) (ha : p a.toMul = 1) : p b.toMul = 1 := by
  have hh : p a.toMul * p b.toMul = 1 := by
    rw [← map_mul]
    change p (a + b).toMul = 1
    rw [hab]
    exact k.toMul.property
  simpa only [ha, one_mul] using hh

lemma kernelIndex_add {a b : Additive Γ} {k : Additive K}
    (hab : a + b = kernelDegree p k) (ha : p a.toMul = 1) :
    kernelIndex p a ha + kernelIndex p b (kernel_second_mem p hab ha) = k := by
  apply Additive.toMul.injective
  apply Subtype.ext
  exact congrArg Additive.toMul hab

/-- Each actual kernel convolution summand maps to the same actual
summand of the ambient convolution. -/
def kernelTensorHom (X Y : NeutralVec.{0} p) :
    (F).obj X ⊗ (F).obj Y ⟶ (F).obj (X ⊗ Y) := fun k =>
  tensorObjDesc (fun a b hab =>
    ιTensorObj X.obj Y.obj (kernelDegree p a) (kernelDegree p b) (kernelDegree p k)
      (congrArg (kernelDegree p) hab))

@[reassoc (attr := simp)] lemma kernelTensorHom_ι (X Y : NeutralVec.{0} p)
    (a b k : Additive K) (hab : a + b = k) :
    ιTensorObj ((F).obj X) ((F).obj Y) a b k hab ≫ kernelTensorHom p X Y k =
      ιTensorObj X.obj Y.obj (kernelDegree p a) (kernelDegree p b) (kernelDegree p k)
        (congrArg (kernelDegree p) hab) := by
  exact ι_tensorObjDesc _ a b hab

/-- The inverse comparison discards only actual zero ambient summands. -/
def kernelTensorInv (X Y : NeutralVec.{0} p) :
    (F).obj (X ⊗ Y) ⟶ (F).obj X ⊗ (F).obj Y := fun k =>
  tensorObjDesc (fun a b hab =>
    if ha : p a.toMul = 1 then
      ιTensorObj ((F).obj X) ((F).obj Y) (kernelIndex p a ha)
        (kernelIndex p b (kernel_second_mem p hab ha)) k (kernelIndex_add p hab ha)
    else 0)

@[reassoc] lemma kernelTensorInv_ι (X Y : NeutralVec.{0} p)
    (a b : Additive Γ) (k : Additive K) (hab : a + b = kernelDegree p k)
    (ha : p a.toMul = 1) :
    ιTensorObj X.obj Y.obj a b (kernelDegree p k) hab ≫ kernelTensorInv p X Y k =
      ιTensorObj ((F).obj X) ((F).obj Y) (kernelIndex p a ha)
        (kernelIndex p b (kernel_second_mem p hab ha)) k (kernelIndex_add p hab ha) := by
  dsimp only [kernelTensorInv]
  rw [ι_tensorObjDesc, dif_pos ha]

/-- Actual kernel restriction is strong on actual convolution tensors. -/
def kernelTensorIso (X Y : NeutralVec.{0} p) :
    (F).obj X ⊗ (F).obj Y ≅ (F).obj (X ⊗ Y) where
  hom := kernelTensorHom p X Y
  inv := kernelTensorInv p X Y
  hom_inv_id := by
    apply GradedObject.hom_ext
    intro k
    apply tensorObj_ext
    intro a b hab
    simp only [PointedVec.comp_apply, kernelTensorHom_ι_assoc, PointedVec.id_apply,
      Category.comp_id]
    have hi := kernelTensorInv_ι p X Y (kernelDegree p a) (kernelDegree p b) k
      (congrArg (kernelDegree p) hab)
      (show p (kernelDegree p a).toMul = 1 from a.toMul.property)
    erw [hi]
    erw [Category.comp_id]
    rcases a with ⟨a, ha⟩
    rcases b with ⟨b, hb⟩
    rfl
  inv_hom_id := by
    apply GradedObject.hom_ext
    intro k
    apply tensorObj_ext
    intro a b hab
    by_cases ha : p a.toMul = 1
    · simp only [PointedVec.comp_apply, PointedVec.id_apply, Category.comp_id]
      erw [kernelTensorInv_ι_assoc p X Y a b k hab ha, kernelTensorHom_ι]
      erw [Category.comp_id]
      rfl
    · exact ((tensorRight (Y.obj b)).map_isZero (X.property a ha)).eq_of_src _ _

end Paper18.Category.PointedRelativeCenterObstruction
