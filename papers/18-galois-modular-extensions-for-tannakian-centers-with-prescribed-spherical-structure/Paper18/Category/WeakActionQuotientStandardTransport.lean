import Paper18.Category.WeakActionQuotientStandard

/-! # Actual standard kernel trivializations under isomorphisms of weak actions -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category
universe v u w w'
namespace Paper18.Category.WeakAction
variable {Γ : Type w} [Group Γ] {G : Type w'} [Group G]
  {C : Type u} [Category.{v} C] (p : Γ →* G) {A B : WeakAction Γ C}

/-- The actual kernel trivialization transported to the source action. -/
def actionIsoTrivialization (i : ActionIso A B)
    (τ : ∀ k : p.ker, B.ρ k.val ≅ 𝟭 C) (k : p.ker) : A.ρ k.val ≅ 𝟭 C :=
  i.iso k.val ≪≫ τ k

lemma kernelComparison_left_mul_raw (A : WeakAction Γ C)
    (τ : ∀ k : p.ker, A.ρ k.val ≅ 𝟭 C)
    (k : p.ker) (y : Γ) (h : p (k.val*y) = p y) (X : C) :
    (kernelComparison p A τ (k.val*y) y h).hom.app X =
      (A.mulIso k.val y).inv.app X ≫ (τ k).hom.app ((A.ρ y).obj X) := by
  rw [kernelComparison_hom_app]
  have hgen (k' : p.ker) (e : k'.val*y = k.val*y) :
      (rhoEqIso A e.symm).hom.app X ≫ (A.mulIso k'.val y).inv.app X ≫
        (τ k').hom.app ((A.ρ y).obj X) =
      (A.mulIso k.val y).inv.app X ≫ (τ k).hom.app ((A.ρ y).obj X) := by
    have hk : k' = k := Subtype.ext (_root_.mul_right_cancel e)
    subst k'
    simp [rhoEqIso]
  exact hgen _ (fiberKernel_mul p (k.val*y) y h)

/-- The canonical formula for any actual kernel trivialization family,
without assuming any of the standard laws being constructed. -/
lemma kernelComparison_of_mul_raw (A : WeakAction Γ C)
    (τ : ∀ k : p.ker, A.ρ k.val ≅ 𝟭 C)
    (k : p.ker) (y x : Γ) (e : k.val*y=x) (h : p x=p y) (X : C) :
    (kernelComparison p A τ x y h).hom.app X =
      (rhoEqIso A e.symm).hom.app X ≫ (A.mulIso k.val y).inv.app X ≫
        (τ k).hom.app ((A.ρ y).obj X) := by
  subst x
  rw [kernelComparison_left_mul_raw]
  simp [rhoEqIso]

lemma kernelComparison_actionIso_left_mul (i : ActionIso A B)
    (τ : ∀ k : p.ker, B.ρ k.val ≅ 𝟭 C)
    (k : p.ker) (y : Γ) (h : p (k.val*y) = p y) (X : C) :
    (kernelComparison p A (actionIsoTrivialization p i τ) (k.val*y) y h).hom.app X ≫
        (i.iso y).hom.app X =
      (i.iso (k.val*y)).hom.app X ≫ (kernelComparison p B τ (k.val*y) y h).hom.app X := by
  rw [kernelComparison_left_mul_raw, kernelComparison_left_mul_raw]
  apply (cancel_epi ((A.mulIso k.val y).hom.app X)).mp
  simp only [actionIsoTrivialization, Iso.trans_hom, NatTrans.comp_app, Category.assoc,
    Iso.hom_inv_id_app_assoc]
  rw [reassoc_of% (i.mul k.val y X)]
  simp only [Iso.hom_inv_id_app_assoc]
  have ht := (τ k).hom.naturality ((i.iso y).hom.app X)
  dsimp only [Functor.id_map] at ht
  rw [← ht]
  rw [reassoc_of% (i.iso k.val).hom.naturality ((i.iso y).hom.app X)]

/-- Canonical kernel comparisons commute with actual isomorphisms of weak
actions. The group-index transports are retained in this proof. -/
@[reassoc] lemma kernelComparison_actionIso (i : ActionIso A B)
    (τ : ∀ k : p.ker, B.ρ k.val ≅ 𝟭 C)
    (x y : Γ) (h : p x = p y) (X : C) :
    (kernelComparison p A (actionIsoTrivialization p i τ) x y h).hom.app X ≫
        (i.iso y).hom.app X =
      (i.iso x).hom.app X ≫ (kernelComparison p B τ x y h).hom.app X := by
  have hgen (k : p.ker) (x y : Γ) (e : k.val*y=x) (h : p x=p y) :
      (kernelComparison p A (actionIsoTrivialization p i τ) x y h).hom.app X ≫
          (i.iso y).hom.app X =
        (i.iso x).hom.app X ≫ (kernelComparison p B τ x y h).hom.app X := by
    subst x
    exact kernelComparison_actionIso_left_mul p i τ k y h X
  exact hgen (fiberKernel p x y h) x y (fiberKernel_mul p x y h) h

/-- Standard kernel laws transfer through an actual weak-action isomorphism. -/
def StandardKernelTrivialization.ofActionIso (i : ActionIso A B)
    (D : StandardKernelTrivialization p B) : StandardKernelTrivialization p A where
  trivialization := actionIsoTrivialization p i D.trivialization
  unit X := by
    dsimp only [actionIsoTrivialization, Iso.trans_hom, NatTrans.comp_app]
    rw [D.unit]
    exact i.unit X
  mul k l X := by
    dsimp only [actionIsoTrivialization, Iso.trans_hom, NatTrans.comp_app]
    rw [Functor.map_comp]
    simp only [Category.assoc]
    erw [reassoc_of% (i.mul k.val l.val X)]
    erw [reassoc_of% (i.iso k.val).hom.naturality ((D.trivialization l).hom.app X)]
    erw [D.mul k l X]
  conjugation g k X := by
    apply (cancel_mono ((i.iso g).hom.app X)).mp
    dsimp only [actionIsoTrivialization, Iso.trans_hom, NatTrans.comp_app]
    rw [Functor.map_comp]
    simp only [Category.assoc]
    erw [(i.iso g).hom.naturality ((D.trivialization k).hom.app X)]
    rw [D.conjugation]
    rw [← reassoc_of% (i.mul g k.val X)]
    rw [kernelComparison_actionIso]

section Monoidal
variable [MonoidalCategory C] [∀ g : Γ, (A.ρ g).Monoidal] [A.IsMonoidal]
  [∀ g : Γ, (B.ρ g).Monoidal] [B.IsMonoidal]
  (i : ActionIso A B) [i.IsMonoidal] (D : StandardKernelTrivialization p B) [D.IsMonoidal p B]

instance StandardKernelTrivialization.ofActionIso_monoidal :
    (D.ofActionIso p i).IsMonoidal p A where
  trivialization_monoidal k := by
    change NatTrans.IsMonoidal ((i.iso k.val) ≪≫ D.trivialization k).hom
    dsimp only [Iso.trans_hom]
    infer_instance
end Monoidal
end Paper18.Category.WeakAction
