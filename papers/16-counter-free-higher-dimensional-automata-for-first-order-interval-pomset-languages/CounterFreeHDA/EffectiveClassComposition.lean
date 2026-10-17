import CounterFreeHDA.EffectiveSignatures

namespace CounterFreeHDA.Cubical.Effective
universe u v
variable {Lab : Type u} {k : ℕ} [Fintype Lab] [DecidableEq Lab]
variable (C : FinCat.{u,v} (Cube Lab k)) (image : ∀ {U V}, Step U V → C.Hom U V)
    (K : ∀ {U V}, Finset (C.Hom U V))
    (L : ∀ {U V : Cube Lab k}, Word U V → Prop)
    (recognises : ∀ {U V} (p : Word U V), L p ↔ wordImage C image p ∈ K)

theorem generated_comp {U V W : Cube Lab k} {p : C.Hom U V} {q : C.Hom V W}
    (hp : p ∈ generatedEnum C image U V) (hq : q ∈ generatedEnum C image V W) :
    C.comp p q ∈ generatedEnum C image U W := by
  obtain ⟨a,ha⟩ := (imageEnum_iff C image p).mp (Finset.mem_filter.mp hp).2
  obtain ⟨b,hb⟩ := (imageEnum_iff C image q).mp (Finset.mem_filter.mp hq).2
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩
  have he := imageEnum_complete C image (a.append b)
  simpa only [STCategory.fold_append,ha,hb] using he

include recognises in
theorem signature_comp_congr {U V W : Cube Lab k} {p p' : C.Hom U V} {q q' : C.Hom V W}
    (hp : p ∈ generatedEnum C image U V) (hp' : p' ∈ generatedEnum C image U V)
    (hq : q ∈ generatedEnum C image V W) (hq' : q' ∈ generatedEnum C image V W)
    (he : signature C image K p = signature C image K p')
    (hf : signature C image K q = signature C image K q') :
    signature C image K (C.comp p q) = signature C image K (C.comp p' q') := by
  obtain ⟨a,ha⟩ := (imageEnum_iff C image p).mp (Finset.mem_filter.mp hp).2
  obtain ⟨a',ha'⟩ := (imageEnum_iff C image p').mp (Finset.mem_filter.mp hp').2
  obtain ⟨b,hb⟩ := (imageEnum_iff C image q).mp (Finset.mem_filter.mp hq).2
  obtain ⟨b',hb'⟩ := (imageEnum_iff C image q').mp (Finset.mem_filter.mp hq').2
  have hpa : (Recognition.Syntactic.equiv (STCategory.category Lab k) L).r a a' := by
    apply (wordClass_eq_iff C image K L recognises a a').mp
    apply Subtype.ext
    simpa only [wordClass,ha,ha'] using (classOf_eq_iff C image K hp).mpr he
  have hqb : (Recognition.Syntactic.equiv (STCategory.category Lab k) L).r b b' := by
    apply (wordClass_eq_iff C image K L recognises b b').mp
    apply Subtype.ext
    simpa only [wordClass,hb,hb'] using (classOf_eq_iff C image K hq).mpr hf
  have hr : (Recognition.Syntactic.equiv (STCategory.category Lab k) L).r (a.append b) (a'.append b') :=
    ⟨Recognition.Syntactic.below_comp (STCategory.category Lab k) L hpa.1 hqb.1,Recognition.Syntactic.below_comp (STCategory.category Lab k) L hpa.2 hqb.2⟩
  have hs := (wordClass_eq_iff C image K L recognises (a.append b) (a'.append b')).mpr hr
  have hs' := (classOf_eq_iff C image K (Finset.mem_filter.mpr
    ⟨Finset.mem_univ _,imageEnum_complete C image (a.append b)⟩)).mp (congrArg Subtype.val hs)
  simpa only [STCategory.fold_append,ha,ha',hb,hb'] using hs'

def classComp {U V W : Cube Lab k} (I : Finset (C.Hom U V)) (J : Finset (C.Hom V W)) : Finset (C.Hom U W) :=
  (generatedEnum C image U W).filter (fun c => ∃ a ∈ I, ∃ b ∈ J,
    signature C image K c = signature C image K (C.comp a b))

include recognises in
theorem classComp_classOf {U V W : Cube Lab k} {p : C.Hom U V} {q : C.Hom V W}
    (hp : p ∈ generatedEnum C image U V) (hq : q ∈ generatedEnum C image V W) :
    classComp C image K (classOf C image K p) (classOf C image K q) = classOf C image K (C.comp p q) := by
  ext c
  simp only [classComp,classOf,Finset.mem_filter]
  constructor
  · rintro ⟨hc,a,⟨ha,hea⟩,b,⟨hb,heb⟩,hec⟩
    exact ⟨hc,hec.trans (signature_comp_congr C image K L recognises ha hp hb hq hea heb)⟩
  · rintro ⟨hc,hec⟩
    exact ⟨hc,p,⟨hp,rfl⟩,q,⟨hq,rfl⟩,hec⟩

/-- Canonical class composition is a finite set computation, never a choice
of an unbounded ST representative. -/
def canonicalComp {U V W : Cube Lab k} (I : CanonicalHom C image K U V) (J : CanonicalHom C image K V W) :
    CanonicalHom C image K U W :=
  ⟨classComp C image K I.val J.val,by
    obtain ⟨p,hp,hI⟩ := Finset.mem_image.mp I.property
    obtain ⟨q,hq,hJ⟩ := Finset.mem_image.mp J.property
    rw [← hI,← hJ,classComp_classOf C image K L recognises hp hq]
    exact Finset.mem_image.mpr ⟨C.comp p q,generated_comp C image hp hq,rfl⟩⟩

def canonicalId (U : Cube Lab k) : CanonicalHom C image K U U := wordClass C image K (.nil U)

include recognises in
theorem canonicalComp_word {U V W : Cube Lab k} (p : Word U V) (q : Word V W) :
    canonicalComp C image K L recognises (wordClass C image K p) (wordClass C image K q) =
      wordClass C image K (p.append q) := by
  apply Subtype.ext
  change classComp C image K (classOf C image K (wordImage C image p))
    (classOf C image K (wordImage C image q)) = classOf C image K (wordImage C image (p.append q))
  rw [classComp_classOf C image K L recognises
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _,imageEnum_complete C image p⟩)
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _,imageEnum_complete C image q⟩),STCategory.fold_append]

include recognises in
theorem wordClass_surjective {U V : Cube Lab k} (I : CanonicalHom C image K U V) :
    ∃ p : Word U V, wordClass C image K p = I := by
  obtain ⟨q,hq⟩ := (quotientClass_bijective C image K L recognises).2 I
  induction q using Quotient.inductionOn with
  | _ p => exact ⟨p,hq⟩

/-- The finite canonical multiplication table has all category laws. -/
def canonicalCategory : FinCat (Cube Lab k) where
  Hom := CanonicalHom C image K
  id := canonicalId C image K
  comp := canonicalComp C image K L recognises
  id_comp I := by
    obtain ⟨p,rfl⟩ := wordClass_surjective C image K L recognises I
    rw [canonicalId,canonicalComp_word]
    rfl
  comp_id I := by
    obtain ⟨p,rfl⟩ := wordClass_surjective C image K L recognises I
    rw [canonicalId,canonicalComp_word,Word.append_nil]
  assoc I J H := by
    obtain ⟨p,rfl⟩ := wordClass_surjective C image K L recognises I
    obtain ⟨q,rfl⟩ := wordClass_surjective C image K L recognises J
    obtain ⟨r,rfl⟩ := wordClass_surjective C image K L recognises H
    simp only [canonicalComp_word,Word.append_assoc]

end CounterFreeHDA.Cubical.Effective
