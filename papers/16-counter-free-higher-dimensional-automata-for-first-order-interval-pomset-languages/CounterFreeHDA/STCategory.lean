import CounterFreeHDA.GluingWidth
import CounterFreeHDA.Recognizer
import CounterFreeHDA.IdealPaths

/-! The concrete elementary ST source category. Its actual pomset semantics
cover every bounded-width interval pomset by AutomaticST. Subsumption is
stable under genuine path contexts, proved using characteristic runs. -/
namespace CounterFreeHDA.Cubical
universe u v
variable {Lab : Type u} {k : ℕ}

namespace Word

@[simp] theorem append_nil {U V : Cube Lab k} (p : Word U V) : p.append (.nil V) = p := by
  induction p with
  | nil U => rfl
  | cons s p ih => exact congrArg (Word.cons s) ih

theorem append_assoc {U V W Z : Cube Lab k} (p : Word U V) (q : Word V W) (r : Word W Z) :
    (p.append q).append r = p.append (q.append r) := by
  induction p with
  | nil U => rfl
  | cons s p ih => exact congrArg (Word.cons s) (ih q)

/-- Subsumption of actual pomset labels is stable under left and right ST
contexts, without assuming an abstract source-category compatibility law. -/
theorem subsumption_context {U V S T : Cube Lab k} {p q : Word U V}
    (h : p.label.pom ⊑ₛ q.label.pom) (a : Word S U) (b : Word V T) :
    ((a.append p).append b).label.pom ⊑ₛ ((a.append q).append b).label.pom := by
  let c := (a.append q).append b
  let X := track (k := k) c.label.pom.val
  have hr : X.Run c c.label.sourceCell c.label.targetCell := c.canonicalRun
  obtain ⟨z,hprefix,hb⟩ := (X.run_append_iff (a.append q) b _ _).mp hr
  obtain ⟨y,ha,hq⟩ := (X.run_append_iff a q _ _).mp hprefix
  have hdp : z ∈ X.dPom y p.label.pom :=
    Refinement.reachability_downward p.label q.label y z h p.label_width ⟨q,hq,⟨PomsetIso.refl _⟩⟩
  have hp : X.Run p y z :=
    (Word.lemma_3_1_b_word p y z).mpr (p.label.map_of_dPom y z hdp)
  have hnew : X.Run ((a.append p).append b) c.label.sourceCell c.label.targetCell :=
    (X.run_append_iff (a.append p) b _ _).mpr
      ⟨z,(X.run_append_iff a p _ _).mpr ⟨y,ha,hp⟩,hb⟩
  exact RunLabeling.subsumption_complete c.label _ hnew

end Word

namespace STCategory

def category (Lab : Type u) (k : ℕ) : Recognition.Cat (Cube Lab k) where
  Hom := Word
  id := Word.nil
  comp := Word.append
  id_comp _ := rfl
  comp_id := Word.append_nil
  assoc := Word.append_assoc

def language (L : Set (IntervalPom Lab)) {U V : Cube Lab k} (p : Word U V) : Prop := p.label.pom ∈ L

def subsumption {U V : Cube Lab k} (p q : Word U V) : Prop := p.label.pom ⊑ₛ q.label.pom

theorem sub_context {U V S T : Cube Lab k} {p q : Word U V} (h : subsumption p q)
    (a : Word S U) (b : Word V T) : subsumption ((a.append p).append b) ((a.append q).append b) :=
  Word.subsumption_context h a b

variable (D : FinCat.{u,v} (Cube Lab k)) (image : ∀ {U V}, Step U V → D.Hom U V)

theorem fold_append {U V W : Cube Lab k} (p : Word U V) (q : Word V W) :
    wordImage D image (p.append q) = D.comp (wordImage D image p) (wordImage D image q) := by
  induction p with
  | nil U => exact (D.id_comp _).symm
  | cons s p ih =>
    change D.comp (image s) (wordImage D image (p.append q)) = _
    rw [ih]
    exact (D.assoc _ _ _).symm

def functor : Recognition.Functor (category Lab k) (Recognition.ofFinite D) where
  obj := id
  map := wordImage D image
  map_id _ := rfl
  map_comp := fold_append D image

/-- **Lemma 2.1 on the concrete ST source.** This instantiates the actual
syntactic quotient using the path-context subsumption theorem above. -/
noncomputable def orderedRecognizer (L : Set (IntervalPom Lab))
    (downward : ∀ {P Q}, P ⊑ₛ Q → Q ∈ L → P ∈ L)
    (K : ∀ {U V}, Set (D.Hom U V))
    (recognises : ∀ {U V} (p : Word U V), p.label.pom ∈ L ↔ wordImage D image p ∈ K)
    {h : ℕ} (hD : D.AperiodicExponent h) :
    Recognition.OrderedRecognizer (category Lab k) (language L) subsumption h :=
  Recognition.lemma_2_1 (category Lab k) (language L) subsumption
    (fun h a b => sub_context h a b) (fun h => downward h) D (functor D image) K recognises hD

end STCategory
end CounterFreeHDA.Cubical
