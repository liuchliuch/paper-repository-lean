import Paper18.Category.FusionSubcategoryBasic

/-! # Checking actual centralization on complete simple families -/
noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
universe v u w v' u'
namespace Paper18.Category
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  [MonoidalCategory C] [MonoidalPreadditive C] [BraidedCategory C]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)

/-- An actual object is transparent precisely when it centralizes a complete
family of actual simple representatives. -/
lemma mem_mugerCenter_iff_simples (X : C) : X ∈ mugerCenter ↔
    ∀ i, Centralizes X (S.simpleObject i) := by
  constructor
  · intro h i
    exact h _ (Set.mem_univ _)
  · intro h Y _
    apply (centralizes_iso_right (S.decomposition Y)).mpr
    exact (centralizes_biproduct_left _ X (fun a => (h (S.label Y a)).symm)).symm

variable {D : Type u'} [Category.{v'} D] [Preadditive D] [HasFiniteBiproducts D]
  [MonoidalCategory D] [MonoidalPreadditive D] [BraidedCategory D]
  (F : C ⥤ D) [F.Additive]

omit [MonoidalCategory C] [MonoidalPreadditive C] [BraidedCategory C] in
/-- Centralizing every image object is equivalent to centralizing the images
of the actual source simples. Additivity supplies the decompositions. -/
lemma mem_centralizer_functor_iff_simples (X : D) :
    X ∈ centralizer (Set.range F.obj) ↔ ∀ i, Centralizes X (F.obj (S.simpleObject i)) := by
  constructor
  · intro h i
    exact h _ ⟨S.simpleObject i, rfl⟩
  · intro h Y hY
    obtain ⟨Z, rfl⟩ := hY
    apply (centralizes_iso_right (S.mapDecomposition F Z)).mpr
    exact (centralizes_biproduct_left _ X (fun a => (h (S.label Z a)).symm)).symm

omit [MonoidalCategory C] [MonoidalPreadditive C] [BraidedCategory C] in
/-- Equality of the actual categorical centralizer and the centralizer tested
on source simple images. -/
lemma centralizer_functor_eq_simples :
    centralizer (Set.range F.obj) =
      centralizer (Set.range (fun i => F.obj (S.simpleObject i))) := by
  ext X
  rw [mem_centralizer_functor_iff_simples S F]
  constructor
  · intro h Y hY
    obtain ⟨i, rfl⟩ := hY
    exact h i
  · intro h i
    exact h _ ⟨i, rfl⟩

end Paper18.Category
