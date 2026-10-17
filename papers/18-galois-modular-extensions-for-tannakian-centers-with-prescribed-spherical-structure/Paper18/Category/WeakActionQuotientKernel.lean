import Paper18.Category.WeakActionQuotientBasic

/-! # Actual kernel trivializations and their canonical comparison maps -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
universe v u w w'
namespace Paper18.Category.WeakAction
variable {Γ : Type w} [Group Γ] {G : Type w'} [Group G]
  {C : Type u} [Category.{v} C] (p : Γ →* G) (A : WeakAction Γ C)

/-- The actual kernel element comparing two lifts of the same quotient element. -/
def fiberKernel (x y : Γ) (h : p x = p y) : p.ker :=
  ⟨x * y⁻¹, by change p (x * y⁻¹) = 1; simp only [map_mul, map_inv, h, mul_inv_cancel]⟩

lemma fiberKernel_mul (x y : Γ) (h : p x = p y) :
    (fiberKernel p x y h).val * y = x := by simp [fiberKernel]

/-- Equality of group elements gives the actual identity comparison of their
translating functors, with transport only in the group index. -/
def rhoEqIso {x y : Γ} (h : x = y) : A.ρ x ≅ A.ρ y := eqToIso (congrArg A.ρ h)

/-- The canonical comparison is the inverse action multiplication followed
by the actual kernel trivialization at the remaining translating functor. -/
def kernelComparison (τ : ∀ k : p.ker, A.ρ k.val ≅ 𝟭 C)
    (x y : Γ) (h : p x = p y) : A.ρ x ≅ A.ρ y :=
  rhoEqIso A (by simp [fiberKernel]) ≪≫
    (A.mulIso (fiberKernel p x y h).val y).symm ≪≫
    Functor.isoWhiskerLeft (A.ρ y) (τ (fiberKernel p x y h)) ≪≫ Functor.rightUnitor (A.ρ y)

/-- The actual component formula available for checking the kernel laws
by concrete underlying maps or scalar cochains. -/
lemma kernelComparison_hom_app (τ : ∀ k : p.ker, A.ρ k.val ≅ 𝟭 C)
    (x y : Γ) (h : p x = p y) (X : C) :
    (kernelComparison p A τ x y h).hom.app X =
      (rhoEqIso A (fiberKernel_mul p x y h).symm).hom.app X ≫
        (A.mulIso (fiberKernel p x y h).val y).inv.app X ≫
          (τ (fiberKernel p x y h)).hom.app ((A.ρ y).obj X) := by
  simp only [kernelComparison, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Functor.rightUnitor_hom_app]
  erw [Category.comp_id]

/-- Kernel trivializations with their actual multiplication/conjugation
compatibility, expressed through the canonical comparisons in Γ. There is
no quotient action or quotient coherence field in these data. -/
structure KernelTrivialization where
  trivialization : ∀ k : p.ker, A.ρ k.val ≅ 𝟭 C
  comparison_refl (x : Γ) (X : C) :
    (kernelComparison p A trivialization x x rfl).hom.app X = 𝟙 _
  comparison_trans (x y z : Γ) (hxy : p x = p y) (hyz : p y = p z) (X : C) :
    (kernelComparison p A trivialization x y hxy).hom.app X ≫
      (kernelComparison p A trivialization y z hyz).hom.app X =
        (kernelComparison p A trivialization x z (hxy.trans hyz)).hom.app X
  comparison_mul (x x' y y' : Γ) (hx : p x = p x') (hy : p y = p y') (X : C) :
    (A.mulIso x y).hom.app X ≫
      (kernelComparison p A trivialization (x * y) (x' * y')
        (by simp only [map_mul, hx, hy])).hom.app X =
    (A.ρ x).map ((kernelComparison p A trivialization y y' hy).hom.app X) ≫
      (kernelComparison p A trivialization x x' hx).hom.app ((A.ρ y').obj X) ≫
        (A.mulIso x' y').hom.app X

/-- The actual kernel equations supply the coherent comparisons used by descent. -/
def KernelTrivialization.fiberComparisons (K : KernelTrivialization p A) :
    FiberComparisons p A where
  iso := kernelComparison p A K.trivialization
  refl := K.comparison_refl
  trans := K.comparison_trans
  mul := K.comparison_mul

section Monoidal
variable [MonoidalCategory C] [∀ g : Γ, (A.ρ g).Monoidal] [A.IsMonoidal]

instance whiskerLeft_monoidal {F H J : C ⥤ C} [F.Monoidal] [H.Monoidal] [J.Monoidal]
    (τ : H ⟶ J) [NatTrans.IsMonoidal τ] :
    NatTrans.IsMonoidal (Functor.whiskerLeft F τ) := by
  have hm : NatTrans.IsMonoidal ((𝟙 F) ◫ τ) := inferInstance
  convert hm using 1
  ext X
  simp

instance rhoEqIso_monoidal {x y : Γ} (h : x = y) :
    NatTrans.IsMonoidal (rhoEqIso A h).hom := by
  subst y
  dsimp [rhoEqIso]
  infer_instance

instance kernelComparison_monoidal
    (τ : ∀ k : p.ker, A.ρ k.val ≅ 𝟭 C)
    [∀ k, NatTrans.IsMonoidal (τ k).hom]
    (x y : Γ) (h : p x = p y) :
    NatTrans.IsMonoidal (kernelComparison p A τ x y h).hom := by
  unfold kernelComparison
  dsimp only [Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerLeft_hom]
  infer_instance

end Monoidal
end Paper18.Category.WeakAction
