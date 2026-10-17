import Paper18.Category.DiagonalCondensationIntersectionBasic

/-! # Recognition of the actual shared image after diagonal condensation -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped BigOperators TensorProduct MonObj
universe v u v' u' vE uE w wC wD wM
namespace Paper18.Category.DiagonalCondensation
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {D : Type u'} [Category.{v'} D] [Preadditive D] [Linear ℂ D]
  [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalLinear ℂ D]
  [BraidedCategory D] [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)]
  {E : Type uE} [Category.{vE} E] [Preadditive E] [Linear ℂ E]
  [MonoidalCategory E] [MonoidalPreadditive E] [MonoidalLinear ℂ E]
  [RightRigidCategory E] [HasKernels E] [HasFiniteBiproducts E]
  [∀ X Y : E, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ E)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton E ι)
  (F : E ⥤ C) [F.Monoidal] [F.Full] [F.Faithful] [F.Additive] [F.Linear ℂ]
  (G : E ⥤ D) [G.Monoidal] [G.Full] [G.Faithful] [G.Additive] [G.Linear ℂ]


variable [HasKernels C] [HasFiniteBiproducts C]
  {κ : Type wC} [Fintype κ] (T : FiniteSemisimpleSkeleton C κ)
  [HasKernels D] [HasFiniteBiproducts D]
  {ν : Type wD} [Fintype ν] (U : FiniteSemisimpleSkeleton D ν)
  {A : DeligneProduct C D} [MonObj A]
  (e : A ≅ ⨁ fun i => pair (F.obj (S.simpleObject i))
    (G.obj (dual E (S.simpleObject i))))

/-- For actual simple objects, positive Hom dimension is equivalent to an
actual isomorphism. -/
lemma simpleHom_finrank_pos_iff {X Y : C} [Simple X] [Simple Y] :
    0 < Module.finrank ℂ (X ⟶ Y) ↔ Nonempty (X ≅ Y) := by
  rw [CategoryTheory.finrank_hom_simple_simple ℂ]
  split_ifs <;> simp_all

include e T in
/-- A shared object in the two actual free images comes from the common
category in the first factor. The proof recognizes each genuine simple
summand through the nonzero mixed Hom coordinate it supplies. -/
lemma left_source_in_image_of_iso (X : C) (V : D)
    (h : Nonempty ((leftFreeFunctor (A := A)).obj X ≅
      (rightFreeFunctor (A := A)).obj V)) : F.essImage X := by
  let L := leftFreeFunctor (A := A)
  letI := (leftFreeFunctorFullyFaithful S F G e T).faithful
  obtain ⟨h⟩ := h
  have hl (a : Fin (T.length X)) : ∃ i : ι,
      Nonempty (T.simpleObject (T.label X a) ≅ F.obj (S.simpleObject i)) := by
    let Q := T.simpleObject (T.label X a)
    letI : Simple Q := T.simple _
    have hin : T.coendInclusion X a ≠ 0 := by
      intro hz
      have hc : T.coendInclusion X a ≫ T.coendProjection X a = 𝟙 Q := by
        simp [FiniteSemisimpleSkeleton.coendInclusion,
          FiniteSemisimpleSkeleton.coendProjection, assoc, Q]
      rw [hz, zero_comp] at hc
      exact CategoryTheory.id_nonzero Q hc.symm
    have hn : L.map (T.coendInclusion X a) ≫ h.hom ≠ 0 := by
      intro hz
      have hh : L.map (T.coendInclusion X a) = 0 := by
        apply (cancel_mono h.hom).mp
        simpa using hz
      apply hin
      apply L.map_injective
      simpa using hh
    have hp : 0 < Module.finrank ℂ (L.obj Q ⟶ (rightFreeFunctor (A := A)).obj V) :=
      Module.finrank_pos_iff_exists_ne_zero.mpr ⟨_, hn⟩
    rw [finrank_freeMixedHom_normalized S F G e] at hp
    obtain ⟨i, hi, hp⟩ := Finset.sum_pos_iff.mp hp
    letI : Simple (F.obj (S.simpleObject i)) := T.simple_map F _
    exact ⟨i, simpleHom_finrank_pos_iff.mp (pos_of_mul_pos_left hp (Nat.zero_le _))⟩
  choose k hk using hl
  let H : Fin (T.length X) → E := fun a => S.simpleObject (k a)
  let hx : X ≅ F.obj (⨁ H) := T.decomposition X ≪≫
    biproduct.mapIso (fun a => Classical.choice (hk a)) ≪≫ (F.mapBiproduct H).symm
  exact ⟨⨁ H, ⟨hx.symm⟩⟩

include e in
/-- On objects from the shared category, the normalized mixed Hom formula
recovers its actual Hom dimension by its genuine simple resolutions. -/
lemma finrank_freeMixedHom_common (X Y : E) :
    Module.finrank ℂ ((leftFreeFunctor (A := A)).obj (F.obj X) ⟶
      (rightFreeFunctor (A := A)).obj (G.obj Y)) = Module.finrank ℂ (X ⟶ Y) := by
  rw [finrank_freeMixedHom_normalized S F G e, S.finrank_hom_eq_sum X Y]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← (fullyFaithfulHomLinearEquiv F X (S.simpleObject i)).finrank_eq,
    ← (fullyFaithfulHomLinearEquiv G (S.simpleObject i) Y).finrank_eq]
  exact congrArg (fun n => n * S.multiplicity Y i) (S.multiplicity_eq_finrank_hom X i).symm

end Paper18.Category.DiagonalCondensation
