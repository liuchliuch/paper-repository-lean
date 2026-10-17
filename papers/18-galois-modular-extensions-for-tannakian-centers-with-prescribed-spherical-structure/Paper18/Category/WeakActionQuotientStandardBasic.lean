import Paper18.Category.WeakActionQuotient

/-! # Standard kernel laws in original group-action coordinates -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category
universe v u w w'
namespace Paper18.Category.WeakAction
variable {Γ : Type w} [Group Γ] {G : Type w'} [Group G]
  {C : Type u} [Category.{v} C] (p : Γ →* G) (A : WeakAction Γ C)

/-- The standard unit, kernel multiplication and conjugation equations
for actual kernel trivializations. These equations refer only to the
original action and actual comparisons, not to any quotient action. -/
structure StandardKernelTrivialization where
  trivialization : ∀ k : p.ker, A.ρ k.val ≅ 𝟭 C
  unit (X : C) : (trivialization 1).hom.app X = A.unitIso.hom.app X
  mul (k l : p.ker) (X : C) :
    (A.mulIso k.val l.val).hom.app X ≫ (trivialization (k*l)).hom.app X =
      (A.ρ k.val).map ((trivialization l).hom.app X) ≫ (trivialization k).hom.app X
  conjugation (g : Γ) (k : p.ker) (X : C) :
    (A.ρ g).map ((trivialization k).hom.app X) =
      (A.mulIso g k.val).hom.app X ≫
        (kernelComparison p A trivialization (g*k.val) g
          (by rw [map_mul, show p k.val = 1 from k.property, _root_.mul_one])).hom.app X

variable (D : StandardKernelTrivialization p A)

/-- Canonical comparisons respect actual equality in the source group index. -/
@[reassoc] lemma kernelComparison_rhoEqIso_comp {x y z : Γ} (e : x = y)
    (h : p y = p z) (X : C) :
    (rhoEqIso A e).hom.app X ≫
      (kernelComparison p A D.trivialization y z h).hom.app X =
    (kernelComparison p A D.trivialization x z ((congrArg p e).trans h)).hom.app X := by
  subst y
  simp [rhoEqIso]

/-- The same equality transport, solved for the canonical comparison. -/
lemma kernelComparison_eq_rhoEqIso_comp {x y z : Γ} (e : x = y)
    (h : p x = p z) (X : C) :
    (kernelComparison p A D.trivialization x z h).hom.app X =
      (rhoEqIso A e).hom.app X ≫
        (kernelComparison p A D.trivialization y z ((congrArg p e).symm.trans h)).hom.app X := by
  subst y
  simp [rhoEqIso]

/-- The canonical comparison from a kernel multiple is the actual inverse
multiplication followed by that kernel trivialization. -/
lemma kernelComparison_left_mul (k : p.ker) (y : Γ) (h : p (k.val*y) = p y) (X : C) :
    (kernelComparison p A D.trivialization (k.val*y) y h).hom.app X =
      (A.mulIso k.val y).inv.app X ≫ (D.trivialization k).hom.app ((A.ρ y).obj X) := by
  rw [kernelComparison_hom_app]
  have hgen (k' : p.ker) (e : k'.val * y = k.val * y) :
      (rhoEqIso A e.symm).hom.app X ≫ (A.mulIso k'.val y).inv.app X ≫
        (D.trivialization k').hom.app ((A.ρ y).obj X) =
          (A.mulIso k.val y).inv.app X ≫ (D.trivialization k).hom.app ((A.ρ y).obj X) := by
    have hk' : k' = k := Subtype.ext (_root_.mul_right_cancel e)
    subst k'
    simp [rhoEqIso]
  exact hgen _ (fiberKernel_mul p (k.val * y) y h)

/-- A chosen actual kernel element gives the comparison formula with
exactly the group-index transport attached to its actual multiplication. -/
lemma kernelComparison_of_mul (k : p.ker) (y x : Γ) (e : k.val * y = x)
    (h : p x = p y) (X : C) :
    (kernelComparison p A D.trivialization x y h).hom.app X =
      (rhoEqIso A e.symm).hom.app X ≫ (A.mulIso k.val y).inv.app X ≫
        (D.trivialization k).hom.app ((A.ρ y).obj X) := by
  subst x
  rw [kernelComparison_left_mul p A D]
  simp [rhoEqIso]

/-- The standard unit equation gives the normalized canonical comparison. -/
lemma StandardKernelTrivialization.comparison_refl (x : Γ) (X : C) :
    (kernelComparison p A D.trivialization x x rfl).hom.app X = 𝟙 _ := by
  rw [kernelComparison_hom_app]
  have hgen (k : p.ker) (e : k.val*x = x) :
      (rhoEqIso A e.symm).hom.app X ≫ (A.mulIso k.val x).inv.app X ≫
        (D.trivialization k).hom.app ((A.ρ x).obj X) = 𝟙 _ := by
    have hk : k = 1 := by
      apply Subtype.ext
      apply _root_.mul_right_cancel (b := x)
      change k.val * x = 1 * x
      simpa only [_root_.one_mul] using e
    subst k
    rw [D.unit, ← A.one_mul x X]
    simp [rhoEqIso]
  exact hgen _ (fiberKernel_mul p x x rfl)

end Paper18.Category.WeakAction
