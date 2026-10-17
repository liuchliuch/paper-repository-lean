import Paper18.Category.WeakActionQuotientStandardRight

/-! # Conjugation gives actual compatibility with left multiplication -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category
universe v u w w'
namespace Paper18.Category.WeakAction
variable {Γ : Type w} [Group Γ] {G : Type w'} [Group G]
  {C : Type u} [Category.{v} C] (p : Γ →* G) (A : WeakAction Γ C)
  (D : StandardKernelTrivialization p A)

lemma StandardKernelTrivialization.comparison_left_mul_kernel
    (x : Γ) (k : p.ker) (z : Γ) (h : p (k.val*z) = p z) (X : C) :
    (A.mulIso x (k.val*z)).hom.app X ≫
      (kernelComparison p A D.trivialization (x*(k.val*z)) (x*z)
        (by simp only [map_mul, h])).hom.app X =
    (A.ρ x).map ((kernelComparison p A D.trivialization (k.val*z) z h).hom.app X) ≫
      (A.mulIso x z).hom.app X := by
  rw [kernelComparison_left_mul p A D k]
  rw [kernelComparison_eq_rhoEqIso_comp p A D (_root_.mul_assoc x k.val z).symm]
  apply (cancel_epi ((A.ρ x).map ((A.mulIso k.val z).hom.app X))).mp
  simp only [Category.assoc, Functor.map_comp]
  slice_lhs 1 2 => rw [A.assoc x k.val z X]
  simp only [Category.assoc, rhoEqIso, eqToIso.hom, eqToHom_app,
    eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rw [← Functor.map_comp_assoc]
  simp only [Iso.hom_inv_id_app, Functor.map_id, Category.id_comp]
  rw [D.conjugation x k ((A.ρ z).obj X)]
  rw [Category.assoc]
  have hid : (A.ρ x).map (𝟙 ((A.ρ z ⋙ A.ρ k.val).obj X)) = 𝟙 _ :=
    (A.ρ x).map_id _
  erw [hid, Category.id_comp]
  apply (cancel_epi ((A.mulIso x k.val).hom.app ((A.ρ z).obj X))).mpr
  exact StandardKernelTrivialization.comparison_right_mul p A D (x*k.val) x z
    (by rw [map_mul, k.property, _root_.mul_one]) X

/-- Standard conjugation and actual action associativity give compatibility
of all canonical kernel comparisons with left multiplication. -/
@[reassoc] lemma StandardKernelTrivialization.comparison_left_mul
    (x y y' : Γ) (h : p y = p y') (X : C) :
    (A.mulIso x y).hom.app X ≫
      (kernelComparison p A D.trivialization (x*y) (x*y')
        (by simp only [map_mul, h])).hom.app X =
    (A.ρ x).map ((kernelComparison p A D.trivialization y y' h).hom.app X) ≫
      (A.mulIso x y').hom.app X := by
  have hgen (k : p.ker) (z y : Γ) (e : k.val*z = y) (h : p y = p z) :
      (A.mulIso x y).hom.app X ≫
        (kernelComparison p A D.trivialization (x*y) (x*z)
          (by simp only [map_mul, h])).hom.app X =
      (A.ρ x).map ((kernelComparison p A D.trivialization y z h).hom.app X) ≫
        (A.mulIso x z).hom.app X := by
    subst y
    exact StandardKernelTrivialization.comparison_left_mul_kernel p A D x k z h X
  exact hgen (fiberKernel p y y' h) y' y (fiberKernel_mul p y y' h) h

end Paper18.Category.WeakAction
