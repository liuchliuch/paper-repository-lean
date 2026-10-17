import Paper18.Category.WeakActionQuotientStandardBasic

/-! # The product law already forces the standard unit trivialization -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category
universe v u w w'
namespace Paper18.Category.WeakAction
variable {Γ : Type w} [Group Γ] {G : Type w'} [Group G]
  {C : Type u} [Category.{v} C] (p : Γ →* G) (A : WeakAction Γ C)

/-- Invertibility and the actual product law force the unit component.
This permits concrete constructions to establish product and conjugation
without a separate normalization argument at the unit. -/
lemma kernelTrivialization_unit_of_mul
    (τ : ∀ k : p.ker, A.ρ k.val ≅ 𝟭 C)
    (hm : ∀ (k l : p.ker) (X : C),
      (A.mulIso k.val l.val).hom.app X ≫ (τ (k*l)).hom.app X =
        (A.ρ k.val).map ((τ l).hom.app X) ≫ (τ k).hom.app X)
    (X : C) : (τ 1).hom.app X = A.unitIso.hom.app X := by
  have ht (k l : p.ker) (h : k = l) :
      (τ k).hom.app X =
        (rhoEqIso A (congrArg Subtype.val h)).hom.app X ≫ (τ l).hom.app X := by
    subst l
    simp [rhoEqIso]
  have hh := hm 1 1 X
  rw [ht (1*1) 1 (_root_.one_mul 1), ← Category.assoc] at hh
  have he := (cancel_mono ((τ 1).hom.app X)).mp hh
  have hu : (A.mulIso 1 1).hom.app X ≫
        (rhoEqIso A (congrArg Subtype.val (_root_.one_mul (1 : p.ker)))).hom.app X =
      (A.ρ 1).map (A.unitIso.hom.app X) := by
    simpa only [rhoEqIso, eqToIso.hom, eqToHom_app] using A.mul_one (1 : Γ) X
  exact (A.ρ 1).map_injective (he.symm.trans hu)

/-- The standard data can be constructed from product and conjugation alone:
the unit normalization is a theorem. -/
def StandardKernelTrivialization.ofMulConjugation
    (τ : ∀ k : p.ker, A.ρ k.val ≅ 𝟭 C)
    (hm : ∀ (k l : p.ker) (X : C),
      (A.mulIso k.val l.val).hom.app X ≫ (τ (k*l)).hom.app X =
        (A.ρ k.val).map ((τ l).hom.app X) ≫ (τ k).hom.app X)
    (hc : ∀ (g : Γ) (k : p.ker) (X : C),
      (A.ρ g).map ((τ k).hom.app X) =
        (A.mulIso g k.val).hom.app X ≫
          (kernelComparison p A τ (g*k.val) g
            (by rw [map_mul, k.property, _root_.mul_one])).hom.app X) :
    StandardKernelTrivialization p A where
  trivialization := τ
  unit := kernelTrivialization_unit_of_mul p A τ hm
  mul := hm
  conjugation := hc

end Paper18.Category.WeakAction
