import Paper18.Category.SemisimpleCokernels
import Mathlib.CategoryTheory.Abelian.Basic

/-!
# Actual Abelian structure from a finite semisimple skeleton

Splittings give explicit normal presentations: a split monomorphism is the
kernel of its complementary idempotent, and a split epimorphism is the
cokernel of its complementary idempotent. Together with the cokernels
constructed from kernel complements, this proves that the category is
Abelian without assuming an Abelian structure.
-/

noncomputable section
open Classical CategoryTheory CategoryTheory.Limits
universe v u w
namespace Paper18.Category

section NormalPresentations
variable {C : Type u} [Category.{v} C] [Preadditive C] {X Y : C}

/-- A chosen split monomorphism is the kernel of its complementary idempotent. -/
def normalMonoOfSplitMono (f : X ⟶ Y) (s : SplitMono f) : NormalMono f where
  Z := Y
  g := 𝟙 Y - s.retraction ≫ f
  w := by
    rw [Preadditive.comp_sub, Category.comp_id, ← Category.assoc, s.id,
      Category.id_comp, sub_self]
  isLimit := KernelFork.IsLimit.ofι _ _
    (fun {_} a _ => a ≫ s.retraction)
    (fun {_} a ha => by
      have h : a - (a ≫ s.retraction) ≫ f = 0 := by
        simpa only [Preadditive.comp_sub, Category.comp_id, Category.assoc] using ha
      exact (sub_eq_zero.mp h).symm)
    (fun {_} a _ m hm => by
      calc
        m = (m ≫ f) ≫ s.retraction := by
          rw [Category.assoc, s.id, Category.comp_id]
        _ = a ≫ s.retraction := by rw [hm])

/-- A chosen split epimorphism is the cokernel of its complementary idempotent. -/
def normalEpiOfSplitEpi (f : X ⟶ Y) (s : SplitEpi f) : NormalEpi f where
  W := X
  g := 𝟙 X - f ≫ s.section_
  w := by
    rw [Preadditive.sub_comp, Category.id_comp, Category.assoc, s.id,
      Category.comp_id, sub_self]
  isColimit := CokernelCofork.IsColimit.ofπ _ _
    (fun {_} a _ => s.section_ ≫ a)
    (fun {_} a ha => by
      have h : a - f ≫ s.section_ ≫ a = 0 := by
        simpa only [Preadditive.sub_comp, Category.id_comp, Category.assoc] using ha
      exact (sub_eq_zero.mp h).symm)
    (fun {_} a _ m hm => by
      calc
        m = s.section_ ≫ f ≫ m := by rw [← Category.assoc, s.id, Category.id_comp]
        _ = s.section_ ≫ a := by rw [hm])

end NormalPresentations

namespace FiniteSemisimpleSkeleton
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)

/-- Every actual monomorphism is normal, by its proved semisimple splitting. -/
def isNormalMonoCategory : IsNormalMonoCategory C where
  normalMonoOfMono f _ := ⟨normalMonoOfSplitMono f (S.splitMono f)⟩

/-- Every actual epimorphism is normal, by its proved semisimple splitting. -/
def isNormalEpiCategory : IsNormalEpiCategory C where
  normalEpiOfEpi f _ := ⟨normalEpiOfSplitEpi f (S.splitEpi f)⟩

/-- An actual finite semisimple complex-linear category with kernels is Abelian.
The cokernels and both normality conditions are constructed, not supplied. -/
def abelian : Abelian C := by
  letI := S.hasCokernels
  letI := S.isNormalMonoCategory
  letI := S.isNormalEpiCategory
  exact { }

end FiniteSemisimpleSkeleton
end Paper18.Category
