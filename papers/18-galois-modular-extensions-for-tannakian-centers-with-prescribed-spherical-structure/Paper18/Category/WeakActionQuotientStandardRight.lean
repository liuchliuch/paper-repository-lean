import Paper18.Category.WeakActionQuotientStandardTrans

/-! # Actual compatibility of canonical comparisons with right multiplication -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category
universe v u w w'
namespace Paper18.Category.WeakAction
variable {Γ : Type w} [Group Γ] {G : Type w'} [Group G]
  {C : Type u} [Category.{v} C] (p : Γ →* G) (A : WeakAction Γ C)
  (D : StandardKernelTrivialization p A)

lemma StandardKernelTrivialization.comparison_right_mul_kernel
    (k : p.ker) (a b : Γ) (h : p (k.val*a) = p a) (X : C) :
    (A.mulIso (k.val*a) b).hom.app X ≫
      (kernelComparison p A D.trivialization ((k.val*a)*b) (a*b)
        (by simp only [map_mul, h])).hom.app X =
    (kernelComparison p A D.trivialization (k.val*a) a h).hom.app ((A.ρ b).obj X) ≫
      (A.mulIso a b).hom.app X := by
  rw [kernelComparison_left_mul p A D k,
    kernelComparison_of_mul p A D k (a*b) _ (_root_.mul_assoc k.val a b).symm]
  apply (cancel_epi ((A.mulIso k.val a).hom.app ((A.ρ b).obj X))).mp
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc, rhoEqIso, eqToIso.hom, eqToHom_app]
  slice_lhs 1 3 => rw [← A.assoc k.val a b X]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  exact (D.trivialization k).hom.naturality ((A.mulIso a b).hom.app X)

/-- Standard kernel trivializations commute with translating on the right.
This is derived from original action associativity and actual naturality. -/
@[reassoc] lemma StandardKernelTrivialization.comparison_right_mul
    (x x' y : Γ) (h : p x = p x') (X : C) :
    (A.mulIso x y).hom.app X ≫
      (kernelComparison p A D.trivialization (x*y) (x'*y)
        (by simp only [map_mul, h])).hom.app X =
    (kernelComparison p A D.trivialization x x' h).hom.app ((A.ρ y).obj X) ≫
      (A.mulIso x' y).hom.app X := by
  have hgen (k : p.ker) (a x : Γ) (e : k.val*a = x) (h : p x = p a) :
      (A.mulIso x y).hom.app X ≫
        (kernelComparison p A D.trivialization (x*y) (a*y)
          (by simp only [map_mul, h])).hom.app X =
      (kernelComparison p A D.trivialization x a h).hom.app ((A.ρ y).obj X) ≫
        (A.mulIso a y).hom.app X := by
    subst x
    exact D.comparison_right_mul_kernel p A k a y h X
  exact hgen (fiberKernel p x x' h) x' x (fiberKernel_mul p x x' h) h

end Paper18.Category.WeakAction
