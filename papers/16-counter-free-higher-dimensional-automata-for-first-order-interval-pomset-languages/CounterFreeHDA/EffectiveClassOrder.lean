import CounterFreeHDA.EffectiveClassComposition

namespace CounterFreeHDA.Cubical.Effective
universe u v
variable {Lab : Type u} {k : ℕ} [Fintype Lab] [DecidableEq Lab]
variable (C : FinCat.{u,v} (Cube Lab k)) (image : ∀ {U V}, Step U V → C.Hom U V)
    (K : ∀ {U V}, Finset (C.Hom U V))
    (L : ∀ {U V : Cube Lab k}, Word U V → Prop)
    (recognises : ∀ {U V} (p : Word U V), L p ↔ wordImage C image p ∈ K)

theorem contextBelow_refl {U V : Cube Lab k} (p : C.Hom U V) : ContextBelow C image K p p :=
  fun _ _ _ _ _ _ h => h

theorem contextBelow_trans {U V : Cube Lab k} {p q r : C.Hom U V}
    (hpq : ContextBelow C image K p q) (hqr : ContextBelow C image K q r) : ContextBelow C image K p r :=
  fun S T a b ha hb h => hpq S T a b ha hb (hqr S T a b ha hb h)

def canonicalLE {U V : Cube Lab k} (I J : CanonicalHom C image K U V) : Prop :=
  ∀ a ∈ I.val, ∀ b ∈ J.val, ContextBelow C image K a b

instance canonicalLEDecidable {U V : Cube Lab k} (I J : CanonicalHom C image K U V) :
    Decidable (canonicalLE C image K I J) := by
  unfold canonicalLE
  infer_instance

include recognises in
theorem canonicalLE_word {U V : Cube Lab k} (p q : Word U V) :
    canonicalLE C image K (wordClass C image K p) (wordClass C image K q) ↔
      Recognition.Syntactic.Below (STCategory.category Lab k) L p q := by
  constructor
  · intro H
    exact (contextBelow_iff C image K L recognises p q).mp
      (H _ (classOf_self C image K (Finset.mem_filter.mpr ⟨Finset.mem_univ _,imageEnum_complete C image p⟩))
        _ (classOf_self C image K (Finset.mem_filter.mpr ⟨Finset.mem_univ _,imageEnum_complete C image q⟩)))
  · intro H a ha b hb
    have ha' := (signature_eq_iff C image K a (wordImage C image p)).mp (Finset.mem_filter.mp ha).2
    have hb' := (signature_eq_iff C image K b (wordImage C image q)).mp (Finset.mem_filter.mp hb).2
    exact contextBelow_trans C image K ha'.1
      (contextBelow_trans C image K ((contextBelow_iff C image K L recognises p q).mpr H) hb'.2)

/-- The order relation of the effective quotient is decidable by finite
context tests; all order and composition laws follow from their exactness. -/
def canonicalOrder : (canonicalCategory C image K L recognises).IsOrdered where
  homLE := canonicalLE C image K
  homLE_refl I := by
    obtain ⟨p,rfl⟩ := wordClass_surjective C image K L recognises I
    exact (canonicalLE_word C image K L recognises p p).mpr (Recognition.Syntactic.below_refl (STCategory.category Lab k) L p)
  homLE_trans := by
    intro U V I J H hIJ hJH
    obtain ⟨p,rfl⟩ := wordClass_surjective C image K L recognises I
    obtain ⟨q,rfl⟩ := wordClass_surjective C image K L recognises J
    obtain ⟨r,rfl⟩ := wordClass_surjective C image K L recognises H
    exact (canonicalLE_word C image K L recognises p r).mpr
      (Recognition.Syntactic.below_trans (STCategory.category Lab k) L ((canonicalLE_word C image K L recognises p q).mp hIJ)
        ((canonicalLE_word C image K L recognises q r).mp hJH))
  homLE_antisymm := by
    intro U V I J hIJ hJI
    obtain ⟨p,rfl⟩ := wordClass_surjective C image K L recognises I
    obtain ⟨q,rfl⟩ := wordClass_surjective C image K L recognises J
    exact (wordClass_eq_iff C image K L recognises p q).mpr
      ⟨(canonicalLE_word C image K L recognises p q).mp hIJ,(canonicalLE_word C image K L recognises q p).mp hJI⟩
  comp_mono_left := by
    intro U V W I I' J hII'
    obtain ⟨p,rfl⟩ := wordClass_surjective C image K L recognises I
    obtain ⟨p',rfl⟩ := wordClass_surjective C image K L recognises I'
    obtain ⟨q,rfl⟩ := wordClass_surjective C image K L recognises J
    change canonicalLE C image K
      (canonicalComp C image K L recognises (wordClass C image K p) (wordClass C image K q))
      (canonicalComp C image K L recognises (wordClass C image K p') (wordClass C image K q))
    rw [canonicalComp_word,canonicalComp_word]
    exact (canonicalLE_word C image K L recognises (p.append q) (p'.append q)).mpr
      (Recognition.Syntactic.below_comp (STCategory.category Lab k) L
        ((canonicalLE_word C image K L recognises p p').mp hII') (Recognition.Syntactic.below_refl (STCategory.category Lab k) L q))
  comp_mono_right := by
    intro U V W I J J' hJJ'
    obtain ⟨p,rfl⟩ := wordClass_surjective C image K L recognises I
    obtain ⟨q,rfl⟩ := wordClass_surjective C image K L recognises J
    obtain ⟨q',rfl⟩ := wordClass_surjective C image K L recognises J'
    change canonicalLE C image K
      (canonicalComp C image K L recognises (wordClass C image K p) (wordClass C image K q))
      (canonicalComp C image K L recognises (wordClass C image K p) (wordClass C image K q'))
    rw [canonicalComp_word,canonicalComp_word]
    exact (canonicalLE_word C image K L recognises (p.append q) (p.append q')).mpr
      (Recognition.Syntactic.below_comp (STCategory.category Lab k) L (Recognition.Syntactic.below_refl (STCategory.category Lab k) L p)
        ((canonicalLE_word C image K L recognises q q').mp hJJ'))

def canonicalAccept {U V : Cube Lab k} (I : CanonicalHom C image K U V) : Prop :=
  ∃ a ∈ I.val, a ∈ K (U := U) (V := V)

instance canonicalAcceptDecidable {U V : Cube Lab k} (I : CanonicalHom C image K U V) :
    Decidable (canonicalAccept C image K I) := by
  unfold canonicalAccept
  infer_instance

include recognises in
theorem canonicalAccept_word {U V : Cube Lab k} (p : Word U V) :
    canonicalAccept C image K (wordClass C image K p) ↔ L p := by
  constructor
  · rintro ⟨a,ha,hK⟩
    have hbelow := ((signature_eq_iff C image K a (wordImage C image p)).mp (Finset.mem_filter.mp ha).2).2
    have hleft := imageEnum_complete C image (.nil U)
    have hright := imageEnum_complete C image (.nil V)
    have hm := hbelow U V (C.id U) (C.id V) hleft hright
      (by simpa only [C.id_comp,C.comp_id] using hK)
    exact (recognises p).mpr (by simpa only [C.id_comp,C.comp_id] using hm)
  · intro hp
    exact ⟨wordImage C image p,classOf_self C image K
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _,imageEnum_complete C image p⟩),(recognises p).mp hp⟩

include recognises in
theorem canonicalAccept_lower (U V : Cube Lab k) :
    IsLowerSet (canonicalOrder C image K L recognises).homLE
      {I : CanonicalHom C image K U V | canonicalAccept C image K I} := by
  intro I J hI hJI
  obtain ⟨p,rfl⟩ := wordClass_surjective C image K L recognises I
  obtain ⟨q,rfl⟩ := wordClass_surjective C image K L recognises J
  apply (canonicalAccept_word C image K L recognises q).mpr
  have hp := (canonicalAccept_word C image K L recognises p).mp hI
  have hqp : Recognition.Syntactic.Below (STCategory.category Lab k) L q p :=
    (canonicalLE_word C image K L recognises q p).mp hJI
  have hh : L p → L q := by
    simpa only [STCategory.category,Word.append_nil] using hqp (.nil U) (.nil V)
  exact hh hp

end CounterFreeHDA.Cubical.Effective
