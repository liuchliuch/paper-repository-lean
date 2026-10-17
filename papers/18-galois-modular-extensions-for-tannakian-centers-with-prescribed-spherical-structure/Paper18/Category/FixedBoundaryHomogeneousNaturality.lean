import Paper18.Category.FixedBoundaryGlue

/-!
# Actual homogeneous components detect natural transformations

The actual split kernels supply a two-component expansion of every natural
transformation. Equality, including action-intertwining equalities, can
therefore be checked on the actual neutral and odd objects and then holds
on the original category without a chosen simple skeleton.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.Limits
universe v u v' u'
namespace Paper18.Category.FixedBoundary
open SignKernel
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C] [HasKernels C]
  (χ : 𝟭 C ≅ 𝟭 C)
  (hχ : ∀ X : C, χ.hom.app X ≫ χ.hom.app X = 𝟙 X)
  {D : Type u'} [Category.{v'} D] [Preadditive D]
  {F G : C ⥤ D} [F.Additive]
include hχ

/-- The two actual kernel projections expand every natural component. -/
theorem natTrans_homogeneous_expansion (τ : F ⟶ G) (X : C) :
    τ.app X =
      F.map (plusπ χ hχ X) ≫ τ.app (plusObject χ X) ≫ G.map (plusι χ X) +
        F.map (minusπ χ hχ X) ≫ τ.app (minusObject χ X) ≫ G.map (minusι χ X) := by
  calc
    τ.app X = F.map (𝟙 X) ≫ τ.app X := by rw [F.map_id, Category.id_comp]
    _ = F.map (plusπ χ hχ X ≫ plusι χ X + minusπ χ hχ X ≫ minusι χ X) ≫ τ.app X := by
      rw [split_resolution]
    _ = _ := by
      rw [F.map_add, Preadditive.add_comp, F.map_comp, F.map_comp]
      simp only [Category.assoc]
      rw [τ.naturality, τ.naturality]

/-- The actual homogeneous subcategories jointly detect all natural
transformations out of an additive functor. -/
theorem natTrans_ext_homogeneous (τ σ : F ⟶ G)
    (hp : ∀ X : C, Homogeneous χ 0 X → τ.app X = σ.app X)
    (hm : ∀ X : C, Homogeneous χ 1 X → τ.app X = σ.app X) : τ = σ := by
  ext X
  rw [natTrans_homogeneous_expansion χ hχ τ, natTrans_homogeneous_expansion χ hχ σ,
    hp _ (plusObject_positive χ X), hm _ (minusObject_negative χ X)]

section Glued
variable (H : C ⥤ C) [H.Additive]
  (a : SignKernel.inclusion χ ⋙ H ≅ SignKernel.inclusion χ)
  (b : ObjectProperty.ι (Homogeneous χ 1) ⋙ H ≅ ObjectProperty.ι (Homogeneous χ 1))

/-- The constructed ambient comparison is the unique ordinary comparison
with the two prescribed actual homogeneous restrictions. -/
theorem glueNatIso_unique (e : H ≅ 𝟭 C)
    (hp : ∀ X : SignKernel.Positive χ, e.hom.app X.obj = a.hom.app X)
    (hm : ∀ X : HomogeneousCategory χ 1, e.hom.app X.obj = b.hom.app X) :
    e = glueNatIso χ hχ H a b := by
  apply Iso.ext
  apply natTrans_ext_homogeneous χ hχ
  · intro X hX
    exact (hp ⟨X, hX⟩).trans (glueNatIso_positive χ hχ H a b ⟨X, hX⟩).symm
  · intro X hX
    exact (hm ⟨X, hX⟩).trans (glueNatIso_negative χ hχ H a b ⟨X, hX⟩).symm

end Glued
end Paper18.Category.FixedBoundary
