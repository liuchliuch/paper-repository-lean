import Paper18.Category.QuasiFusionCategory
import Paper18.Category.QuasiFusionPivotalDual

/-! # The actual weighted double-dual natural isomorphism -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
namespace Paper18.Category.QuasiFusion.CocycleVec
attribute [local instance 2000] RightRigidCategory.rightDual
variable {G : Type} [Group G] [Fintype G] (ψ : ThreeCocycle G)

/-- The actual double dual of a homogeneous fiber, with the inverse-degree
transport made explicit. -/
def bidualFiberIso (X : CocycleVec ψ) (a : Additive G) :
    ((doubleDualFunctor (CocycleVec ψ)).obj X) a ≅
      (doubleDualFunctor (FGModuleCat ℂ)).obj (X a) :=
  eqToIso (congrArg (fun b => (doubleDualFunctor (FGModuleCat ℂ)).obj (X b)) (neg_neg a))

private lemma doubleMate_transport {A : Type} {X Y : A → FGModuleCat ℂ}
    (f : ∀ a, X a ⟶ Y a) {a b : A} (h : a = b) :
    (doubleDualFunctor (FGModuleCat ℂ)).map (f a) ≫
        eqToHom (congrArg (fun c => (doubleDualFunctor (FGModuleCat ℂ)).obj (Y c)) h) =
      eqToHom (congrArg (fun c => (doubleDualFunctor (FGModuleCat ℂ)).obj (X c)) h) ≫
        (doubleDualFunctor (FGModuleCat ℂ)).map (f b) := by
  subst b
  simp

lemma bidualFiberIso_naturality {X Y : CocycleVec ψ} (f : X ⟶ Y) (a : Additive G) :
    ((doubleDualFunctor (CocycleVec ψ)).map f) a ≫ (bidualFiberIso ψ Y a).hom =
      (bidualFiberIso ψ X a).hom ≫ (doubleDualFunctor (FGModuleCat ℂ)).map (f a) := by
  change (dualMap (CocycleVec ψ) (dualMap (CocycleVec ψ) f)) a ≫ _ = _
  have h₁ := QuasiFusion.dualMap_fiber ψ f
  have h₂ := QuasiFusion.dualMap_fiber ψ (dualMap (CocycleVec ψ) f)
  rw [h₂]
  change dualMap (FGModuleCat ℂ) ((dualMap (CocycleVec ψ) f) (-a)) ≫ _ = _
  rw [h₁]
  exact doubleMate_transport f (neg_neg a)

/-- The ordinary vector double-dual identification, with the actual
inverse-degree transports of the chosen graded duals. -/
def unweightedPivotalFiber (X : CocycleVec ψ) (a : Additive G) :
    X a ≅ ((doubleDualFunctor (CocycleVec ψ)).obj X) a :=
  drinfeldIso (X a) ≪≫ (bidualFiberIso ψ X a).symm

lemma unweightedPivotalFiber_naturality {X Y : CocycleVec ψ} (f : X ⟶ Y) (a : Additive G) :
    f a ≫ (unweightedPivotalFiber ψ Y a).hom =
      (unweightedPivotalFiber ψ X a).hom ≫ ((doubleDualFunctor (CocycleVec ψ)).map f) a := by
  apply (cancel_mono (bidualFiberIso ψ Y a).hom).mp
  simp only [unweightedPivotalFiber, Iso.trans_hom, Iso.symm_hom, assoc,
    Iso.inv_hom_id, comp_id]
  rw [bidualFiberIso_naturality]
  simp only [← assoc, Iso.inv_hom_id, comp_id]
  exact drinfeldIso_naturality (f a)

/-- The cocycle correction is the actual scalar ψ(g,g⁻¹,g). -/
def pivotalWeight (a : Additive G) : ℂˣ := ψ.val a.toMul a.toMul⁻¹ a.toMul

/-- The actual weighted bidual isomorphism on a graded object. -/
def pivotalComponent (X : CocycleVec ψ) : X ≅ (doubleDualFunctor (CocycleVec ψ)).obj X where
  hom a := (pivotalWeight ψ a : ℂ) • (unweightedPivotalFiber ψ X a).hom
  inv a := (((pivotalWeight ψ a)⁻¹ : ℂˣ) : ℂ) • (unweightedPivotalFiber ψ X a).inv
  hom_inv_id := by
    funext a
    change ((pivotalWeight ψ a : ℂ) • (unweightedPivotalFiber ψ X a).hom) ≫
      ((((pivotalWeight ψ a)⁻¹ : ℂˣ) : ℂ) • (unweightedPivotalFiber ψ X a).inv) = 𝟙 (X a)
    simp [Linear.smul_comp, Linear.comp_smul, smul_smul]
  inv_hom_id := by
    funext a
    change ((((pivotalWeight ψ a)⁻¹ : ℂˣ) : ℂ) • (unweightedPivotalFiber ψ X a).inv) ≫
      ((pivotalWeight ψ a : ℂ) • (unweightedPivotalFiber ψ X a).hom) = 𝟙 _
    simp [Linear.smul_comp, Linear.comp_smul, smul_smul]

/-- The actual ψ-weighted degreewise vector bidual map is natural. -/
def pivotalNatIso : 𝟭 (CocycleVec ψ) ≅ doubleDualFunctor (CocycleVec ψ) :=
  NatIso.ofComponents (pivotalComponent ψ) (by
    intro X Y f
    funext a
    change f a ≫ ((pivotalWeight ψ a : ℂ) • (unweightedPivotalFiber ψ Y a).hom) =
      ((pivotalWeight ψ a : ℂ) • (unweightedPivotalFiber ψ X a).hom) ≫
        ((doubleDualFunctor (CocycleVec ψ)).map f) a
    rw [Linear.comp_smul, Linear.smul_comp, unweightedPivotalFiber_naturality])

end Paper18.Category.QuasiFusion.CocycleVec
