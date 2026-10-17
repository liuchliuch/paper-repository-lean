import CounterFreeHDA.BoundedArrow

/-! Lift the finite syntactic ST recognizer to every actual bounded interval
pomset. Independence of the chosen ST word is proved from the original
recognizer's isomorphism and composition laws. -/
namespace CounterFreeHDA.Cubical
universe u v w
variable {Lab : Type u} {k : ℕ}

namespace STCategory

/-- The syntactic quotient identifies any two words with equal original
finite evaluation; this fact makes the actual-pomset lift independent of
all choices of decomposition. -/
theorem map_eq_of_evaluation_eq (D : FinCat.{u,v} (Cube Lab k))
    (image : ∀ {U V}, Step U V → D.Hom U V) (L : Set (IntervalPom Lab))
    (downward : ∀ {P Q}, P ⊑ₛ Q → Q ∈ L → P ∈ L)
    (K : ∀ {U V}, Set (D.Hom U V))
    (recognises : ∀ {U V} (p : Word U V), p.label.pom ∈ L ↔ wordImage D image p ∈ K)
    {h : ℕ} (hD : D.AperiodicExponent h) {U V : Cube Lab k} (p q : Word U V)
    (he : wordImage D image p = wordImage D image q) :
    (orderedRecognizer D image L downward K recognises hD).map p =
      (orderedRecognizer D image L downward K recognises hD).map q := by
  apply Quotient.sound
  exact Recognition.Syntactic.equivalent_of_image_eq (category Lab k) (language L)
    D (functor D image) (fun x => x ∈ K) recognises he

end STCategory

/-- The ordered recognizer on the actual bounded-pomset source. Every law
refers to actual gluing, identities, subsumption and isomorphism. -/
structure OrderedPomsetRecognizer (L : Set (IntervalPom Lab)) (h : ℕ) where
  C : FinCat.{u,v} (Cube Lab k)
  order : C.IsOrdered
  map : ∀ {U V}, BoundedArrow U V → C.Hom U V
  map_id : ∀ U, map (BoundedArrow.ident U) = C.id U
  map_comp : ∀ {U V W} (A : BoundedArrow U V) (B : BoundedArrow V W),
    map (A.comp B) = C.comp (map A) (map B)
  map_iso : ∀ {U V} (A B : BoundedArrow U V), PomsetIso A.pom.val B.pom.val → map A = map B
  J : ∀ {U V}, Set (C.Hom U V)
  recognises : ∀ {U V} (A : BoundedArrow U V), A.pom ∈ L ↔ map A ∈ J
  lower : ∀ U V, IsLowerSet order.homLE (J (U := U) (V := V))
  monotone : ∀ {U V} (A B : BoundedArrow U V), A.pom ⊑ₛ B.pom → order.homLE (map A) (map B)
  aperiodic : C.AperiodicExponent h

namespace FinitePomsetRecognizer
variable {L : Set (IntervalPom Lab)} {h : ℕ}
    (G : FinitePomsetRecognizer.{u,v} (k := k) L h)
    (downward : ∀ {P Q}, P ⊑ₛ Q → Q ∈ L → P ∈ L)

theorem word_recognises {U V : Cube Lab k} (p : Word U V) :
    p.label.pom ∈ L ↔ wordImage G.D G.stepImage p ∈ G.K := by
  rw [G.wordImage_eq]
  exact G.recognises (BoundedArrow.ofWord p)

noncomputable def syntactic :=
  STCategory.orderedRecognizer G.D G.stepImage L downward G.K G.word_recognises G.aperiodic

noncomputable def actualMap {U V : Cube Lab k} (A : BoundedArrow U V) : (G.syntactic downward).C.Hom U V :=
  (G.syntactic downward).map A.representative

theorem syntactic_eq {U V : Cube Lab k} (p q : Word U V)
    (he : wordImage G.D G.stepImage p = wordImage G.D G.stepImage q) :
    (G.syntactic downward).map p = (G.syntactic downward).map q :=
  STCategory.map_eq_of_evaluation_eq G.D G.stepImage L downward G.K G.word_recognises G.aperiodic p q he

theorem actualMap_id (U : Cube Lab k) : G.actualMap downward (BoundedArrow.ident U) = (G.syntactic downward).C.id U := by
  have he : wordImage G.D G.stepImage (BoundedArrow.ident U).representative = wordImage G.D G.stepImage (.nil U) :=
    (G.representative_image _).trans (G.map_id U)
  exact (G.syntactic_eq downward _ _ he).trans ((G.syntactic downward).map_id U)

theorem actualMap_comp {U V W : Cube Lab k} (A : BoundedArrow U V) (B : BoundedArrow V W) :
    G.actualMap downward (A.comp B) = (G.syntactic downward).C.comp (G.actualMap downward A) (G.actualMap downward B) := by
  have he : wordImage G.D G.stepImage (A.comp B).representative =
      wordImage G.D G.stepImage (A.representative.append B.representative) :=
    (G.representative_image _).trans ((G.map_comp A B).trans
      ((congrArg₂ G.D.comp (G.representative_image A) (G.representative_image B)).symm.trans
        (STCategory.fold_append G.D G.stepImage _ _).symm))
  exact (G.syntactic_eq downward _ _ he).trans ((G.syntactic downward).map_comp _ _)

theorem actualMap_iso {U V : Cube Lab k} (A B : BoundedArrow U V) (φ : PomsetIso A.pom.val B.pom.val) :
    G.actualMap downward A = G.actualMap downward B :=
  G.syntactic_eq downward _ _ ((G.representative_image A).trans ((G.map_iso A B φ).trans (G.representative_image B).symm))

theorem actualMap_recognises {U V : Cube Lab k} (A : BoundedArrow U V) :
    A.pom ∈ L ↔ G.actualMap downward A ∈ (G.syntactic downward).J := by
  have he : A.representative.label.pom ∈ L ↔ A.pom ∈ L :=
    (G.recognises (BoundedArrow.ofWord A.representative)).trans
      ((congrArg (fun a => a ∈ G.K) (G.map_iso (BoundedArrow.ofWord A.representative) A A.representativeIso)).to_iff.trans
        (G.recognises A).symm)
  exact he.symm.trans ((G.syntactic downward).recognises A.representative)

theorem actualMap_monotone {U V : Cube Lab k} (A B : BoundedArrow U V) (hab : A.pom ⊑ₛ B.pom) :
    (G.syntactic downward).order.homLE (G.actualMap downward A) (G.actualMap downward B) := by
  apply (G.syntactic downward).monotone
  exact subsumption_trans A.representativeIso.subsumption (subsumption_trans hab B.representativeIso.symm.subsumption)

/-- **Lemma 2.1 for actual bounded interval pomsets.** The finite ordered
recognizer, lower accepting ideal, monotonicity and exponent are all
constructed; no ordered-recognizer output is assumed. -/
noncomputable def ordered : OrderedPomsetRecognizer.{u,u} (k := k) L h where
  C := (G.syntactic downward).C
  order := (G.syntactic downward).order
  map := G.actualMap downward
  map_id := G.actualMap_id downward
  map_comp := G.actualMap_comp downward
  map_iso := G.actualMap_iso downward
  J := (G.syntactic downward).J
  recognises := G.actualMap_recognises downward
  lower := (G.syntactic downward).lower
  monotone := G.actualMap_monotone downward
  aperiodic := (G.syntactic downward).aperiodic

end FinitePomsetRecognizer
end CounterFreeHDA.Cubical
