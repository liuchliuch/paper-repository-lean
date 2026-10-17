import CounterFreeHDA.EffectiveClassPower
import CounterFreeHDA.CoproductCounterFree

namespace CounterFreeHDA.Cubical.FinitePomsetRecognizer
universe u v
open Effective
variable {Lab : Type u} {k h : ℕ} [Fintype Lab] [DecidableEq Lab] {L : Set (IntervalPom Lab)}
    (G : FinitePomsetRecognizer.{u,v} (k := k) L h)
    (image : ∀ {U V}, Step U V → G.D.Hom U V)
    (himage : ∀ {U V} (s : Step U V), image s = G.stepImage s)
    (K : ∀ {U V}, Finset (G.D.Hom U V))
    (hK : ∀ {U V} (a : G.D.Hom U V), a ∈ K ↔ a ∈ G.K)

include himage in
theorem effective_wordImage {U V : Cube Lab k} (p : Word U V) : wordImage G.D image p = wordImage G.D G.stepImage p := by
  induction p with
  | nil U => rfl
  | cons s p ih =>
    change G.D.comp (image s) (wordImage G.D image p) = G.D.comp (G.stepImage s) (wordImage G.D G.stepImage p)
    rw [himage,ih]

include himage hK in
theorem effective_word_recognises {U V : Cube Lab k} (p : Word U V) :
    STCategory.language L p ↔ wordImage G.D image p ∈ K := by
  unfold STCategory.language
  rw [effective_wordImage G image himage,G.word_recognises]
  exact (hK _).symm

variable (downward : ∀ {P Q}, P ⊑ₛ Q → Q ∈ L → P ∈ L)

/-- A genuine ordered recognizer with computable finite canonical hom-sets,
composition, order and acceptance; semantic maps are proved using the original
recognizer and do not occur in the finite table algorithms. -/
noncomputable def effectiveOrdered : OrderedPomsetRecognizer.{u,v} (k := k) L h where
  C := canonicalCategory G.D image K (STCategory.language L) (G.effective_word_recognises image himage K hK)
  order := canonicalOrder G.D image K (STCategory.language L) (G.effective_word_recognises image himage K hK)
  map A := quotientClass G.D image K (STCategory.language L) (G.effective_word_recognises image himage K hK)
    (G.actualMap downward A)
  map_id U := by
    change quotientClass G.D image K (STCategory.language L) (G.effective_word_recognises image himage K hK)
      (G.actualMap downward (BoundedArrow.ident U)) = canonicalId G.D image K U
    rw [G.actualMap_id downward]
    rfl
  map_comp A B := by
    change quotientClass G.D image K (STCategory.language L) (G.effective_word_recognises image himage K hK)
      (G.actualMap downward (A.comp B)) = _
    rw [G.actualMap_comp downward]
    change quotientClass G.D image K (STCategory.language L) (G.effective_word_recognises image himage K hK)
      (Recognition.Syntactic.qcomp (STCategory.category Lab k) (STCategory.language L)
        (G.actualMap downward A) (G.actualMap downward B)) =
      canonicalComp G.D image K (STCategory.language L) (G.effective_word_recognises image himage K hK)
        (quotientClass G.D image K (STCategory.language L) (G.effective_word_recognises image himage K hK) (G.actualMap downward A))
        (quotientClass G.D image K (STCategory.language L) (G.effective_word_recognises image himage K hK) (G.actualMap downward B))
    exact quotientClass_comp G.D image K (STCategory.language L) (G.effective_word_recognises image himage K hK)
      (G.actualMap downward A) (G.actualMap downward B)
  map_iso A B φ := congrArg (quotientClass G.D image K (STCategory.language L)
    (G.effective_word_recognises image himage K hK)) (G.actualMap_iso downward A B φ)
  J := {I | canonicalAccept G.D image K I}
  recognises A := by
    exact (G.actualMap_recognises downward A).trans
      (canonicalAccept_word G.D image K (STCategory.language L) (G.effective_word_recognises image himage K hK) A.representative).symm
  lower U V := canonicalAccept_lower G.D image K (STCategory.language L) (G.effective_word_recognises image himage K hK) U V
  monotone A B hAB := by
    exact (quotientClass_le G.D image K (STCategory.language L) (G.effective_word_recognises image himage K hK) _ _).mpr
      (G.actualMap_monotone downward A B hAB)
  aperiodic := canonical_aperiodic G.D image K (STCategory.language L) (G.effective_word_recognises image himage K hK) G.aperiodic

include himage hK in
theorem effective_step {U V : Cube Lab k} (s : Step U V) :
    (G.effectiveOrdered image himage K hK downward).stepImage s = wordClass G.D image K (.cons s (.nil V)) := by
  apply Subtype.ext
  change classOf G.D image K (wordImage G.D image (BoundedArrow.ofStep s).representative) =
    classOf G.D image K (wordImage G.D image (.cons s (.nil V)))
  rw [G.effective_wordImage image himage,G.representative_image]
  change classOf G.D image K (G.map (BoundedArrow.ofStep s)) = classOf G.D image K (G.D.comp (image s) (G.D.id V))
  rw [G.D.comp_id,himage]
  rfl

end CounterFreeHDA.Cubical.FinitePomsetRecognizer
