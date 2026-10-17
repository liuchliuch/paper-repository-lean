import Paper18.Category.DeligneProductNondegenerateBasic

/-! # Actual Müger nondegeneracy of Deligne products -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
universe v u w v' u' w'
namespace Paper18.Category.DeligneProduct
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C] [BraidedCategory C]
  [HasKernels C] [HasFiniteBiproducts C] [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {D : Type u'} [Category.{v'} D] [Preadditive D] [Linear ℂ D]
  [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalLinear ℂ D] [BraidedCategory D]
  [HasKernels D] [HasFiniteBiproducts D] [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  {κ : Type w'} [Fintype κ] (T : FiniteSemisimpleSkeleton D κ)

/-- An actual simple pair is transparent precisely when both of its actual
simple factors are transparent. -/
theorem pair_transparent_iff (i : ι) (j : κ) :
    pairObject S T i j ∈ mugerCenter ↔
      S.simpleObject i ∈ mugerCenter ∧ T.simpleObject j ∈ mugerCenter := by
  constructor
  · intro h
    have hr (Y : LinearTensor C D) :
        Centralizes (⟨S.simpleObject i, T.simpleObject j⟩ : LinearTensor C D) Y :=
      (centralizes_map_iff (Mat_.embedding (LinearTensor C D)) _ Y).mp
        (h _ (Set.mem_univ _))
    constructor
    · intro Z _
      exact centralizes_left_test Z (hr ⟨Z, 𝟙_ D⟩)
    · intro Z _
      exact centralizes_right_test Z (hr ⟨𝟙_ C, Z⟩)
  · rintro ⟨hi, hj⟩
    apply (mem_mugerCenter_iff_simples (skeleton S T) _).mpr
    intro p
    exact (raw_centralizes (hi _ (Set.mem_univ _)) (hj _ (Set.mem_univ _))).map
      (Mat_.embedding (LinearTensor C D))

variable [Simple (𝟙_ C)] [Simple (𝟙_ D)]

/-- A transparent actual simple pair in a product of nondegenerate factors
is the actual unit pair. -/
theorem transparent_pair_label (hC : IsNondegenerate (C := C))
    (hD : IsNondegenerate (C := D)) (i : ι) (j : κ)
    (h : pairObject S T i j ∈ mugerCenter) : (i, j) = (S.unitLabel, T.unitLabel) := by
  obtain ⟨hi, hj⟩ := (pair_transparent_iff S T i j).mp h
  exact Prod.ext ((nondegenerate_iff_simple_center S).mp hC i hi)
    ((nondegenerate_iff_simple_center T).mp hD j hj)

include S T in
/-- The componentwise actual braiding on the actual Deligne product of two
nondegenerate finite semisimple categories is nondegenerate. The proof
decomposes every actual transparent object into the actual unit pair. -/
theorem isNondegenerate (hC : IsNondegenerate (C := C))
    (hD : IsNondegenerate (C := D)) :
    IsNondegenerate (C := DeligneProduct C D) := by
  intro X hX
  let P := skeleton S T
  have hp (a : Fin (P.length X)) :
      P.label X a = (S.unitLabel, T.unitLabel) := by
    apply transparent_pair_label S T hC hD
    exact P.property_label (centralizerProperty (Set.univ : Set (DeligneProduct C D)))
      (⟨X, hX⟩ : CentralizerCategory (Set.univ : Set (DeligneProduct C D))) a
  refine ⟨P.length X, ⟨P.decomposition X ≪≫ biproduct.mapIso (fun a => ?_)⟩⟩
  exact eqToIso (congrArg P.simpleObject (hp a)) ≪≫ unitPairIso S T

end Paper18.Category.DeligneProduct
