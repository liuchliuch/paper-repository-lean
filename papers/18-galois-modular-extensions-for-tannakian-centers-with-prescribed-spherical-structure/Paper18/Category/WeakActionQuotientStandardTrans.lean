import Paper18.Category.WeakActionQuotientStandardBasic

/-! # Actual transitivity from the standard kernel multiplication law -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category
universe v u w w'
namespace Paper18.Category.WeakAction
variable {Γ : Type w} [Group Γ] {G : Type w'} [Group G]
  {C : Type u} [Category.{v} C] (p : Γ →* G) (A : WeakAction Γ C)
  (D : StandardKernelTrivialization p A)

lemma StandardKernelTrivialization.comparison_trans_left_mul
    (k l : p.ker) (z : Γ)
    (hxy : p (k.val * (l.val * z)) = p (l.val * z))
    (hyz : p (l.val * z) = p z) (X : C) :
    (kernelComparison p A D.trivialization (k.val * (l.val * z)) (l.val * z) hxy).hom.app X ≫
      (kernelComparison p A D.trivialization (l.val * z) z hyz).hom.app X =
    (kernelComparison p A D.trivialization (k.val * (l.val * z)) z (hxy.trans hyz)).hom.app X := by
  rw [kernelComparison_left_mul p A D k, kernelComparison_left_mul p A D l,
    kernelComparison_of_mul p A D (k*l) z _ (_root_.mul_assoc k.val l.val z)]
  apply (cancel_epi ((A.ρ k.val).map ((A.mulIso l.val z).hom.app X) ≫
    (A.mulIso k.val (l.val*z)).hom.app X)).mp
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  have hn := (D.trivialization k).hom.naturality ((A.mulIso l.val z).hom.app X)
  change (A.ρ k.val).map ((A.mulIso l.val z).hom.app X) ≫
    (D.trivialization k).hom.app ((A.ρ (l.val*z)).obj X) =
    (D.trivialization k).hom.app ((A.ρ l.val).obj ((A.ρ z).obj X)) ≫
      (A.mulIso l.val z).hom.app X at hn
  rw [reassoc_of% hn]
  simp only [Iso.hom_inv_id_app_assoc]
  have hn₂ := (D.trivialization k).hom.naturality
    ((D.trivialization l).hom.app ((A.ρ z).obj X))
  dsimp only [Functor.id_map] at hn₂
  rw [← hn₂]
  dsimp only [Functor.id_obj]
  rw [← D.mul k l ((A.ρ z).obj X)]
  rw [← Category.assoc, A.assoc]
  simp only [Category.assoc, rhoEqIso, eqToIso.hom, eqToHom_app,
    eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  change (A.mulIso k.val l.val).hom.app ((A.ρ z).obj X) ≫
    (D.trivialization (k*l)).hom.app ((A.ρ z).obj X) =
    (A.mulIso k.val l.val).hom.app ((A.ρ z).obj X) ≫
      (A.mulIso (k.val*l.val) z).hom.app X ≫
        (A.mulIso (k.val*l.val) z).inv.app X ≫
          (D.trivialization (k*l)).hom.app ((A.ρ z).obj X)
  simp only [Iso.hom_inv_id_app_assoc]

/-- Standard kernel multiplication gives actual transitivity of all
canonical comparisons, with all group-index transports retained. -/
lemma StandardKernelTrivialization.comparison_trans
    (x y z : Γ) (hxy : p x = p y) (hyz : p y = p z) (X : C) :
    (kernelComparison p A D.trivialization x y hxy).hom.app X ≫
      (kernelComparison p A D.trivialization y z hyz).hom.app X =
    (kernelComparison p A D.trivialization x z (hxy.trans hyz)).hom.app X := by
  have hgen (k l : p.ker) (x y z : Γ) (hk : k.val * y = x) (hl : l.val * z = y)
      (hxy : p x = p y) (hyz : p y = p z) :
      (kernelComparison p A D.trivialization x y hxy).hom.app X ≫
        (kernelComparison p A D.trivialization y z hyz).hom.app X =
      (kernelComparison p A D.trivialization x z (hxy.trans hyz)).hom.app X := by
    subst x
    subst y
    exact StandardKernelTrivialization.comparison_trans_left_mul p A D k l z hxy hyz X
  exact hgen (fiberKernel p x y hxy) (fiberKernel p y z hyz) x y z
    (fiberKernel_mul p x y hxy) (fiberKernel_mul p y z hyz) hxy hyz

end Paper18.Category.WeakAction
