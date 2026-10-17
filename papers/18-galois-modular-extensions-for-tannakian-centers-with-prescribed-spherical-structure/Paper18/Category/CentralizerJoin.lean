import Paper18.Category.CentralizerDoubleDimension

/-! # The actual fusion-subcategory join and categorical centralizers -/
noncomputable section
open Classical
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
universe v u w
namespace Paper18.Category
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

/-- Centralizing a union is exactly centralizing both actual collections. -/
lemma centralizer_union_set (T V : Set C) :
    centralizer (T ∪ V) = centralizer T ∩ centralizer V := by
  ext X
  constructor
  · intro h
    exact ⟨fun Y hY => h Y (Or.inl hY), fun Y hY => h Y (Or.inr hY)⟩
  · rintro ⟨hT, hV⟩ Y (hY | hY)
    · exact hT Y hY
    · exact hV Y hY

/-- The centralizer closure of the union. In a nondegenerate braided pivotal
fusion category it is proved below to be the least actual fusion full
subcategory containing both given full subcategories. -/
def fusionJoin (P Q : ObjectProperty C) : ObjectProperty C :=
  centralizerProperty (centralizer ((P : Set C) ∪ (Q : Set C)))

lemma subset_fusionJoin_left (P Q : ObjectProperty C) :
    ∀ X, P X → fusionJoin P Q X :=
  fun _ h => subset_double_centralizer ((P : Set C) ∪ (Q : Set C)) (Or.inl h)

lemma subset_fusionJoin_right (P Q : ObjectProperty C) :
    ∀ X, Q X → fusionJoin P Q X :=
  fun _ h => subset_double_centralizer ((P : Set C) ∪ (Q : Set C)) (Or.inr h)

lemma fusionJoin_comm (P Q : ObjectProperty C) : fusionJoin P Q = fusionJoin Q P := by
  simp only [fusionJoin, Set.union_comm]

/-- The centralizer of the actual join is the intersection of the two
actual centralizers; this identity needs no dimension premise. -/
lemma centralizer_fusionJoin (P Q : ObjectProperty C) :
    centralizer (fusionJoin P Q : Set C) =
      centralizer (P : Set C) ∩ centralizer (Q : Set C) := by
  change centralizer (centralizer (centralizer ((P : Set C) ∪ (Q : Set C)))) = _
  rw [triple_centralizer, centralizer_union_set]

variable [Preadditive C] [HasFiniteBiproducts C] [MonoidalPreadditive C]

instance fusionJoin_isAdditive (P Q : ObjectProperty C) : IsAdditiveFullProperty (fusionJoin P Q) :=
  inferInstanceAs (IsAdditiveFullProperty (centralizerProperty _))

instance fusionJoin_isMonoidal (P Q : ObjectProperty C) : (fusionJoin P Q).IsMonoidal :=
  inferInstanceAs ((centralizerProperty _).IsMonoidal)

variable [Linear ℂ C] [HasKernels C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalLinear ℂ C] [RightRigidCategory C] [Simple (𝟙_ C)]
  {ι : Type w} [Fintype ι]
namespace FiniteSemisimpleSkeleton
variable (S : FiniteSemisimpleSkeleton C ι) (J : PivotalStructure C)

include S J in
/-- The constructed actual join has the defining least-fusion-subcategory
property. The proof derives closure of every candidate under the actual
double centralizer rather than assuming a join formula. -/
lemma fusionJoin_le_iff (hC : IsNondegenerate (C := C)) (P Q R : ObjectProperty C)
    [IsAdditiveFullProperty R] [R.IsMonoidal] :
    (∀ X, fusionJoin P Q X → R X) ↔
      (∀ X, P X → R X) ∧ (∀ X, Q X → R X) := by
  constructor
  · intro h
    exact ⟨fun X hX => h X (subset_fusionJoin_left P Q X hX),
      fun X hX => h X (subset_fusionJoin_right P Q X hX)⟩
  · rintro ⟨hP, hQ⟩
    have hi : Set.Subset (Set.union (P : Set C) (Q : Set C)) (R : Set C) := by
      rintro X (hX | hX)
      · exact hP X hX
      · exact hQ X hX
    have hm := centralizer_antitone (centralizer_antitone hi)
    rw [S.double_centralizer_eq J hC R] at hm
    exact hm

include S J in
lemma fusionJoin_idem (hC : IsNondegenerate (C := C)) (P : ObjectProperty C)
    [IsAdditiveFullProperty P] [P.IsMonoidal] : fusionJoin P P = P := by
  change centralizer (centralizer ((P : Set C) ∪ (P : Set C))) = (P : Set C)
  rw [Set.union_self, S.double_centralizer_eq J hC P]

include S J in
/-- The centralizer of an intersection is the actual fusion join of the
centralizers. Both double-centralizer identities used here are proved from
actual restricted Hopf averaging. -/
lemma centralizer_inter_eq_fusionJoin (hC : IsNondegenerate (C := C))
    (P Q : ObjectProperty C) [IsAdditiveFullProperty P] [P.IsMonoidal]
    [IsAdditiveFullProperty Q] [Q.IsMonoidal] :
    centralizer ((P : Set C) ∩ (Q : Set C)) =
      (fusionJoin (centralizerProperty (P : Set C)) (centralizerProperty (Q : Set C)) : Set C) := by
  change _ = centralizer (centralizer (centralizer (P : Set C) ∪ centralizer (Q : Set C)))
  rw [centralizer_union_set, S.double_centralizer_eq J hC P, S.double_centralizer_eq J hC Q]

end FiniteSemisimpleSkeleton
end Paper18.Category
