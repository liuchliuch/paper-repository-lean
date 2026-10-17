import CounterFreeHDA.EffectiveContexts

namespace CounterFreeHDA.Cubical.Effective
universe u v
variable {Lab : Type u} {k : ℕ} [Fintype Lab] [DecidableEq Lab]
variable (C : FinCat.{u,v} (Cube Lab k)) (image : ∀ {U V}, Step U V → C.Hom U V)
    (K : ∀ {U V}, Finset (C.Hom U V))

abbrev Signature (U V : Cube Lab k) := ∀ (S T : Cube Lab k), C.Hom S U → C.Hom V T → Bool

def signature {U V : Cube Lab k} (p : C.Hom U V) : Signature C U V := fun S T a b =>
  decide ((⟨U,a⟩ : ImageState C S) ∈ imageEnum C image S ∧
    (⟨T,b⟩ : ImageState C V) ∈ imageEnum C image V ∧ C.comp (C.comp a p) b ∈ K (U := S) (V := T))

theorem signature_eq_iff {U V : Cube Lab k} (p q : C.Hom U V) :
    signature C image K p = signature C image K q ↔
      ContextBelow C image K p q ∧ ContextBelow C image K q p := by
  constructor
  · intro H
    have he : ∀ S T a b,
        ((⟨U,a⟩ : ImageState C S) ∈ imageEnum C image S ∧
          (⟨T,b⟩ : ImageState C V) ∈ imageEnum C image V ∧ C.comp (C.comp a p) b ∈ K) ↔
        ((⟨U,a⟩ : ImageState C S) ∈ imageEnum C image S ∧
          (⟨T,b⟩ : ImageState C V) ∈ imageEnum C image V ∧ C.comp (C.comp a q) b ∈ K) := by
      intro S T a b
      exact decide_eq_decide.mp (congrFun (congrFun (congrFun (congrFun H S) T) a) b)
    exact ⟨fun S T a b ha hb hq => ((he S T a b).mpr ⟨ha,hb,hq⟩).2.2,
      fun S T a b ha hb hp => ((he S T a b).mp ⟨ha,hb,hp⟩).2.2⟩
  · rintro ⟨hp,hq⟩
    funext S T a b
    apply decide_eq_decide.mpr
    exact ⟨fun ⟨ha,hb,h⟩ => ⟨ha,hb,hq S T a b ha hb h⟩,
      fun ⟨ha,hb,h⟩ => ⟨ha,hb,hp S T a b ha hb h⟩⟩

def generatedEnum (U V : Cube Lab k) : Finset (C.Hom U V) :=
  Finset.univ.filter (fun p => (⟨V,p⟩ : ImageState C U) ∈ imageEnum C image U)

def classOf {U V : Cube Lab k} (p : C.Hom U V) : Finset (C.Hom U V) :=
  (generatedEnum C image U V).filter (fun q => signature C image K q = signature C image K p)

def classEnum (U V : Cube Lab k) : Finset (Finset (C.Hom U V)) :=
  (generatedEnum C image U V).image (classOf C image K)

abbrev CanonicalHom (U V : Cube Lab k) := {A : Finset (C.Hom U V) // A ∈ classEnum C image K U V}

theorem classOf_self {U V : Cube Lab k} {p : C.Hom U V} (hp : p ∈ generatedEnum C image U V) :
    p ∈ classOf C image K p := Finset.mem_filter.mpr ⟨hp,rfl⟩

theorem classOf_eq_iff {U V : Cube Lab k} {p q : C.Hom U V}
    (hp : p ∈ generatedEnum C image U V) :
    classOf C image K p = classOf C image K q ↔ signature C image K p = signature C image K q := by
  constructor
  · intro H
    have hm : p ∈ classOf C image K q := H ▸ classOf_self C image K hp
    exact (Finset.mem_filter.mp hm).2
  · intro H
    unfold classOf
    simp only [H]

def wordClass {U V : Cube Lab k} (p : Word U V) : CanonicalHom C image K U V :=
  ⟨classOf C image K (wordImage C image p),Finset.mem_image.mpr
    ⟨wordImage C image p,Finset.mem_filter.mpr ⟨Finset.mem_univ _,imageEnum_complete C image p⟩,rfl⟩⟩

variable (L : ∀ {U V : Cube Lab k}, Word U V → Prop)
    (recognises : ∀ {U V} (p : Word U V), L p ↔ wordImage C image p ∈ K)

include recognises in
theorem wordClass_eq_iff {U V : Cube Lab k} (p q : Word U V) :
    wordClass C image K p = wordClass C image K q ↔
      (Recognition.Syntactic.equiv (STCategory.category Lab k) L).r p q := by
  rw [Subtype.ext_iff]
  change classOf C image K (wordImage C image p) = classOf C image K (wordImage C image q) ↔ _
  rw [classOf_eq_iff C image K (Finset.mem_filter.mpr ⟨Finset.mem_univ _,imageEnum_complete C image p⟩),signature_eq_iff]
  exact and_congr (contextBelow_iff C image K L recognises p q) (contextBelow_iff C image K L recognises q p)

/-- Every ordered syntactic quotient class is represented by a canonical,
computably enumerated finite set of arrows of the supplied multiplication table. -/
def quotientClass {U V : Cube Lab k} :
    Recognition.Syntactic.Arrow (STCategory.category Lab k) L U V → CanonicalHom C image K U V :=
  fun q => Quotient.liftOn q (wordClass C image K) (fun p q h => (wordClass_eq_iff C image K L recognises p q).mpr h)

include recognises in
theorem quotientClass_bijective {U V : Cube Lab k} :
    Function.Bijective (quotientClass C image K L recognises (U := U) (V := V)) := by
  constructor
  · intro p q
    induction p using Quotient.inductionOn with
    | _ p =>
      induction q using Quotient.inductionOn with
      | _ q =>
        intro h
        exact Quotient.sound ((wordClass_eq_iff C image K L recognises p q).mp h)
  · rintro ⟨A,hA⟩
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨p,hp⟩ := (imageEnum_iff C image a).mp (Finset.mem_filter.mp ha).2
    refine ⟨Quotient.mk _ p,Subtype.ext ?_⟩
    change classOf C image K (wordImage C image p) = classOf C image K a
    rw [hp]

end CounterFreeHDA.Cubical.Effective
