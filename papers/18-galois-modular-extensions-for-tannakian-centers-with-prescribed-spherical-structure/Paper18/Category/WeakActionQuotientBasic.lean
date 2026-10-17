import Paper18.Category.EquivariantMonoidal

/-! # Coherent comparison maps over a group quotient

These comparison data live entirely in the original action. They identify
the translating functors above the same quotient element and commute with
the original multiplication maps.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category
universe v u w w'
namespace Paper18.Category.WeakAction
variable {Γ : Type w} [Group Γ] {G : Type w'} [Group G]
  {C : Type u} [Category.{v} C] (p : Γ →* G) (A : WeakAction Γ C)

/-- Actual natural comparisons between translating functors in one fiber.
The equations are normalization, composition and compatibility with the
given Γ-action multiplication; they mention no quotient action. -/
structure FiberComparisons where
  iso : ∀ (x y : Γ) (_h : p x = p y), A.ρ x ≅ A.ρ y
  refl (x : Γ) (X : C) : (iso x x rfl).hom.app X = 𝟙 _
  trans (x y z : Γ) (hxy : p x = p y) (hyz : p y = p z) (X : C) :
    (iso x y hxy).hom.app X ≫ (iso y z hyz).hom.app X =
      (iso x z (hxy.trans hyz)).hom.app X
  mul (x x' y y' : Γ) (hx : p x = p x') (hy : p y = p y') (X : C) :
    (A.mulIso x y).hom.app X ≫
      (iso (x * y) (x' * y') (by simp only [map_mul, hx, hy])).hom.app X =
    (A.ρ x).map ((iso y y' hy).hom.app X) ≫
      (iso x x' hx).hom.app ((A.ρ y').obj X) ≫ (A.mulIso x' y').hom.app X

namespace FiberComparisons
variable {p A} (D : FiberComparisons p A)

@[reassoc] lemma iso_trans (x y z : Γ) (hxy : p x = p y) (hyz : p y = p z) (X : C) :
    (D.iso x y hxy).hom.app X ≫ (D.iso y z hyz).hom.app X =
      (D.iso x z (hxy.trans hyz)).hom.app X := D.trans x y z hxy hyz X

@[simp] lemma iso_refl (x : Γ) (X : C) : (D.iso x x rfl).hom.app X = 𝟙 _ := D.refl x X

@[reassoc] lemma iso_mul (x x' y y' : Γ) (hx : p x = p x') (hy : p y = p y') (X : C) :
    (A.mulIso x y).hom.app X ≫
      (D.iso (x * y) (x' * y') (by simp only [map_mul, hx, hy])).hom.app X =
    (A.ρ x).map ((D.iso y y' hy).hom.app X) ≫
      (D.iso x x' hx).hom.app ((A.ρ y').obj X) ≫ (A.mulIso x' y').hom.app X :=
  D.mul x x' y y' hx hy X

lemma iso_of_eq {x y : Γ} (h : x = y) (X : C) :
    (D.iso x y (congrArg p h)).hom.app X =
      eqToHom (congrArg (fun g => (A.ρ g).obj X) h) := by
  subst y
  simp

@[reassoc] lemma eqToHom_comp_iso {x y z : Γ} (h : x = y) (hyz : p y = p z) (X : C) :
    eqToHom (congrArg (fun g => (A.ρ g).obj X) h) ≫ (D.iso y z hyz).hom.app X =
      (D.iso x z ((congrArg p h).trans hyz)).hom.app X := by
  subst y
  simp

@[reassoc] lemma iso_comp_eqToHom {x y z : Γ} (hxy : p x = p y) (h : y = z) (X : C) :
    (D.iso x y hxy).hom.app X ≫ eqToHom (congrArg (fun g => (A.ρ g).obj X) h) =
      (D.iso x z (hxy.trans (congrArg p h))).hom.app X := by
  subst z
  simp

/-- Compatibility when only the inner translating functor is changed. -/
@[reassoc] lemma transport_left (a b c d : Γ) (h : p b = p c)
    (hd : p (a * c) = p d) (X : C) :
    (A.ρ a).map ((D.iso b c h).hom.app X) ≫
      (A.mulIso a c).hom.app X ≫ (D.iso (a * c) d hd).hom.app X =
    (A.mulIso a b).hom.app X ≫
      (D.iso (a * b) d (by simpa only [map_mul, h] using hd)).hom.app X := by
  have hm := D.mul a a b c rfl h X
  simp only [iso_refl, Category.id_comp] at hm
  rw [← Category.assoc, ← hm, Category.assoc, iso_trans]

/-- Compatibility when only the outer translating functor is changed. -/
@[reassoc] lemma transport_right (a b c d : Γ) (h : p a = p b)
    (hd : p (b * c) = p d) (X : C) :
    (D.iso a b h).hom.app ((A.ρ c).obj X) ≫
      (A.mulIso b c).hom.app X ≫ (D.iso (b * c) d hd).hom.app X =
    (A.mulIso a c).hom.app X ≫
      (D.iso (a * c) d (by simpa only [map_mul, h] using hd)).hom.app X := by
  have hm := D.mul a b c c h rfl X
  simp only [iso_refl] at hm
  rw [(A.ρ a).map_id, Category.id_comp] at hm
  rw [← Category.assoc, ← hm, Category.assoc, iso_trans]

end FiberComparisons

/-- A normalized set-theoretic section of an actual group quotient. -/
structure QuotientSection where
  lift : G → Γ
  map_lift : ∀ g, p (lift g) = g
  lift_one : lift 1 = 1

/-- Surjectivity supplies a normalized section; it need not be a group homomorphism. -/
def chosenQuotientSection (hp : Function.Surjective p) : QuotientSection p where
  lift g := if g = 1 then 1 else Classical.choose (hp g)
  map_lift g := by
    split_ifs with h
    · simp only [h, map_one]
    · exact Classical.choose_spec (hp g)
  lift_one := by simp

end Paper18.Category.WeakAction
