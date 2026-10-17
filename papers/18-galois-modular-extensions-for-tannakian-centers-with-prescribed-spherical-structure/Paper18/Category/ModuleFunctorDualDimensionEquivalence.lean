import Paper18.Category.FunctorImage

/-! # Actual equivalences reindex weighted simple sums -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Limits
open scoped BigOperators
universe v u v' u' w w'
namespace Paper18.Category.ModuleFunctor
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C] [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {D : Type u'} [Category.{v'} D] [Preadditive D] [Linear ℂ D]
  [HasKernels D] [HasFiniteBiproducts D] [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  {κ : Type w'} [Fintype κ] (T : FiniteSemisimpleSkeleton D κ)
  (F : C ⥤ D) [F.Additive] [F.Linear ℂ] [F.Full] [F.Faithful] [F.EssSurj]

/-- Actual essential surjectivity makes the actual simple-label injection
surjective, without any tensor or dimension comparison premise. -/
lemma simpleImageLabel_surjective_of_essSurj : Function.Surjective (S.simpleImageLabel T F) := by
  intro j
  let X := F.objPreimage (T.simpleObject j)
  let e := F.objObjPreimageIso (T.simpleObject j)
  letI : Simple X := S.simple_of_finrank_end_eq_one X (by
    rw [(fullyFaithfulHomLinearEquiv F X X).finrank_eq, finrank_hom_iso e e]
    exact CategoryTheory.finrank_endomorphism_simple_eq_one ℂ (T.simpleObject j))
  obtain ⟨i, ⟨a⟩⟩ := S.simple_isomorphic_representative X
  refine ⟨i, T.iso_injective _ _ ?_⟩
  exact ⟨(S.simpleImageIso T F i).symm ≪≫ F.mapIso a.symm ≪≫ e⟩

/-- Weighted sums are transported by actual isomorphisms and the actual
bijection of simple classes. -/
theorem weighted_simple_sum_equivalence (q : D → ℝ)
    (hq : ∀ {X Y : D}, (X ≅ Y) → q X = q Y) :
    (∑ i, q (F.obj (S.simpleObject i))) = ∑ j, q (T.simpleObject j) := by
  let e : ι ≃ κ := Equiv.ofBijective (S.simpleImageLabel T F)
    ⟨S.simpleImageLabel_injective T F, simpleImageLabel_surjective_of_essSurj S T F⟩
  apply Fintype.sum_equiv e
  intro i
  exact hq (S.simpleImageIso T F i)

end Paper18.Category.ModuleFunctor
