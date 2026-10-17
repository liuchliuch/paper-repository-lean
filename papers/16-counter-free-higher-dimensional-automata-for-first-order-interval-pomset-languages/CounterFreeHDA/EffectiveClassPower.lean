import CounterFreeHDA.EffectiveClassOrder

namespace CounterFreeHDA.Cubical.Effective
universe u v
variable {Lab : Type u} {k : ℕ} [Fintype Lab] [DecidableEq Lab]
variable (C : FinCat.{u,v} (Cube Lab k)) (image : ∀ {U V}, Step U V → C.Hom U V)
    (K : ∀ {U V}, Finset (C.Hom U V))
    (L : ∀ {U V : Cube Lab k}, Word U V → Prop)
    (recognises : ∀ {U V} (p : Word U V), L p ↔ wordImage C image p ∈ K)

theorem wordImage_pow {U : Cube Lab k} (p : Word U U) (n : ℕ) :
    wordImage C image (p.pow n) = FinCat.pow (wordImage C image p) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Word.pow,STCategory.fold_append,ih]
    rfl

include recognises in
theorem canonical_pow_word {U : Cube Lab k} (p : Word U U) (n : ℕ) :
    FinCat.pow (C := canonicalCategory C image K L recognises) (wordClass C image K p) n =
      wordClass C image K (p.pow n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change canonicalComp C image K L recognises
      (FinCat.pow (C := canonicalCategory C image K L recognises) (wordClass C image K p) n)
      (wordClass C image K p) = _
    rw [ih,canonicalComp_word]
    rfl

include recognises in
theorem canonical_aperiodic {h : ℕ} (hC : C.AperiodicExponent h) :
    (canonicalCategory C image K L recognises).AperiodicExponent h := by
  intro U I
  obtain ⟨p,rfl⟩ := wordClass_surjective C image K L recognises I
  rw [canonical_pow_word,canonical_pow_word]
  apply Subtype.ext
  change classOf C image K (wordImage C image (p.pow h)) = classOf C image K (wordImage C image (p.pow (h+1)))
  rw [wordImage_pow,wordImage_pow,hC]

include recognises in
theorem quotientClass_comp {U V W : Cube Lab k}
    (p : Recognition.Syntactic.Arrow (STCategory.category Lab k) L U V)
    (q : Recognition.Syntactic.Arrow (STCategory.category Lab k) L V W) :
    quotientClass C image K L recognises (Recognition.Syntactic.qcomp (STCategory.category Lab k) L p q) =
      canonicalComp C image K L recognises (quotientClass C image K L recognises p)
        (quotientClass C image K L recognises q) := by
  induction p using Quotient.inductionOn with
  | _ p =>
    induction q using Quotient.inductionOn with
    | _ q => exact (canonicalComp_word C image K L recognises p q).symm

include recognises in
theorem quotientClass_le {U V : Cube Lab k}
    (p q : Recognition.Syntactic.Arrow (STCategory.category Lab k) L U V) :
    canonicalLE C image K (quotientClass C image K L recognises p) (quotientClass C image K L recognises q) ↔
      Recognition.Syntactic.qle (STCategory.category Lab k) L p q := by
  induction p using Quotient.inductionOn with
  | _ p =>
    induction q using Quotient.inductionOn with
    | _ q => exact canonicalLE_word C image K L recognises p q

end CounterFreeHDA.Cubical.Effective
