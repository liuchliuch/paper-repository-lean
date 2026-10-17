import Paper18.Category.DrinfeldInnerTrivializationLines
import Paper18.Category.QuasiFusionCategory

/-! # Actual homogeneous crossing isomorphisms of a central graded object -/
noncomputable section
set_option maxHeartbeats 1200000
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
namespace Paper18.Category.DrinfeldInner
open PointedVec QuasiFusion
variable {K : Type} [Group K] [Fintype K] (ψ : ThreeCocycle K)

/-- The actual half-braiding with the degree-`k` line, expressed in the
unique supported convolution fibers. -/
def crossingTotal (Z : Center (CocycleVec ψ)) (k s : Additive K) :
    Z.1 (s - k) ≅ Z.1 (-k + s) :=
  (rightLineFiberIso Z.1 k s).symm ≪≫
    (GradedObject.eval s).mapIso (Z.2.β (simpleObject (Additive K) k)) ≪≫
      leftLineFiberIso Z.1 k s

@[reassoc]
lemma crossingTotal_naturality {Z W : Center (CocycleVec ψ)} (f : Z ⟶ W)
    (k s : Additive K) :
    f.f (s - k) ≫ (crossingTotal ψ W k s).hom =
      (crossingTotal ψ Z k s).hom ≫ f.f (-k + s) := by
  have hc := congrFun (f.comm (simpleObject (Additive K) k)) s
  change GradedObject.Monoidal.tensorHom f.f (𝟙 (simpleObject (Additive K) k)) s ≫
      (W.2.β (simpleObject (Additive K) k)).hom s =
    (Z.2.β (simpleObject (Additive K) k)).hom s ≫
      GradedObject.Monoidal.tensorHom (𝟙 (simpleObject (Additive K) k)) f.f s at hc
  change f.f (s-k) ≫ rightLineInclusion W.1 k s ≫
      (W.2.β (simpleObject (Additive K) k)).hom s ≫ leftLineProjection W.1 k s =
    (rightLineInclusion Z.1 k s ≫ (Z.2.β (simpleObject (Additive K) k)).hom s ≫
      leftLineProjection Z.1 k s) ≫ f.f (-k+s)
  calc
    _ = rightLineInclusion Z.1 k s ≫
        (GradedObject.Monoidal.tensorHom f.f (𝟙 (simpleObject (Additive K) k)) s ≫
          (W.2.β (simpleObject (Additive K) k)).hom s) ≫ leftLineProjection W.1 k s := by
      rw [rightLineInclusion_naturality_assoc]
      simp only [Category.assoc]
    _ = rightLineInclusion Z.1 k s ≫
        ((Z.2.β (simpleObject (Additive K) k)).hom s ≫
          GradedObject.Monoidal.tensorHom (𝟙 (simpleObject (Additive K) k)) f.f s) ≫
            leftLineProjection W.1 k s :=
      congrArg (fun q => rightLineInclusion Z.1 k s ≫ q ≫ leftLineProjection W.1 k s) hc
    _ = _ := by
      have hl := leftLineProjection_naturality (X := Z.1) (Y := W.1) f.f k s
      have hh := congrArg (fun q => rightLineInclusion Z.1 k s ≫
        (Z.2.β (simpleObject (Additive K) k)).hom s ≫ q) hl
      simpa only [Category.assoc] using hh

/-- Crossing with the line changes a homogeneous degree by actual conjugation. -/
def crossing (Z : Center (CocycleVec ψ)) (k a : Additive K) :
    Z.1 a ≅ Z.1 (-k + (a + k)) :=
  eqToIso (congrArg Z.1 (show a = (a + k) - k by simp)) ≪≫
    crossingTotal ψ Z k (a + k)

@[reassoc]
lemma crossing_naturality {Z W : Center (CocycleVec ψ)} (f : Z ⟶ W)
    (k a : Additive K) :
    f.f a ≫ (crossing ψ W k a).hom =
      (crossing ψ Z k a).hom ≫ f.f (-k + (a + k)) := by
  have ht := eqToHom_naturality f.f (show a = (a+k)-k by simp)
  simp only [crossing, Iso.trans_hom, eqToIso.hom, Category.assoc]
  rw [reassoc_of% ht, crossingTotal_naturality]

/-- Actual pullback by inverse inner conjugation on degrees. -/
def innerPullback (k : Additive K) : CocycleVec ψ ⥤ CocycleVec ψ :=
  GradedObject.comap (FGModuleCat ℂ) (fun a => -k + (a + k))

/-- The concrete half-braiding provides the actual natural isomorphism
after forgetting central structure. Its monoidal and central coherence are
proved separately from the half-braiding hexagon. -/
def underlyingTrivialization (k : Additive K) :
    Center.forget (CocycleVec ψ) ⋙ innerPullback ψ k ≅ Center.forget (CocycleVec ψ) :=
  NatIso.ofComponents (fun Z => GradedObject.isoMk _ _ (fun a => (crossing ψ Z k a).symm))
    (by
      intro Z W f
      funext a
      change f.f (-k+(a+k)) ≫ (crossing ψ W k a).inv =
        (crossing ψ Z k a).inv ≫ f.f a
      apply (cancel_epi (crossing ψ Z k a).hom).mp
      simp only [← Category.assoc, Iso.hom_inv_id, id_comp]
      rw [Category.assoc, ← crossing_naturality_assoc, Iso.hom_inv_id, comp_id])

@[simp] lemma underlyingTrivialization_hom_app (k a : Additive K)
    (Z : Center (CocycleVec ψ)) :
    (underlyingTrivialization ψ k).hom.app Z a = (crossing ψ Z k a).inv := rfl

end Paper18.Category.DrinfeldInner
