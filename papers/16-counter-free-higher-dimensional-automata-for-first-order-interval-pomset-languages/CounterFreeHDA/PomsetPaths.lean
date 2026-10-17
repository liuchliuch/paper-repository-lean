import CounterFreeHDA.Track
import CounterFreeHDA.ActualPower

/-! Exact interval-pomset labels of HDA paths. Every elementary step has a
real discrete starter/terminator, and a path label is their actual gluing.
Reachability requires an isomorphism of this label with the specified pomset. -/

namespace CounterFreeHDA.Cubical
universe u v
variable {Lab : Type u} {k : ℕ}

/-- A discrete interval pomset with ordered subinterfaces. -/
def discretePom {n r s : ℕ} (lab : Fin n → Lab)
    (src : Fin r ↪o Fin n) (tgt : Fin s ↪o Fin n) : IntervalPom Lab where
  val := {
    n := n, lab := lab,prec := fun _ _ => False,eord := fun i j => i < j,
    srcLen := r,tgtLen := s,src := src,tgt := tgt,
    src_inj := src.injective,tgt_inj := tgt.injective }
  property := by
    refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · intro e; exact not_false
    · intro e f g h; exact False.elim h
    · intro e; exact lt_irrefl _
    · intro e hp
      have hlt : ∀ {a b : Fin n}, Relation.TransGen (fun i j : Fin n => i < j) a b → a < b := by
        intro a b h
        induction h with
        | single h => exact h
        | tail _ h ih => exact lt_trans ih h
      exact lt_irrefl _ (hlt hp)
    · intro e f hef
      rcases lt_or_gt_of_ne hef with h | h <;>
        simp only [false_or,false_implies,not_false,true_and,implies_true]
      · have ha : ¬ f < e := not_lt_of_gt h
        tauto
      · have ha : ¬ e < f := not_lt_of_gt h
        tauto
    · intro e h f; exact not_false
    · intro e h f; exact not_false
    · intro i j; exact src.strictMono.lt_iff_lt
    · intro i j; exact tgt.strictMono.lt_iff_lt
    · exact ⟨fun _ => (0 : ℝ),fun _ => 1,by intro e f; norm_num⟩

def cubeInterface (U : Cube Lab k) : Interface Lab := ⟨U.dim,U.lab⟩

/-- A typed actual interval pomset; type equations retain every position label. -/
structure Arrow (U V : Cube Lab k) where
  pom : IntervalPom Lab
  source : pom.val.srcType = cubeInterface U
  target : pom.val.tgtType = cubeInterface V

namespace Arrow

def ident (U : Cube Lab k) : Arrow U U where
  pom := identityPom Lab U.dim U.lab
  source := rfl
  target := rfl

noncomputable def comp {U V W : Cube Lab k} (P : Arrow U V) (Q : Arrow V W) : Arrow U W where
  pom := glue P.pom Q.pom (GlueMatch.ofType (P.target.trans Q.source.symm))
  source := (glue_srcType _).trans P.source
  target := (glue_tgtType _).trans Q.target

end Arrow

namespace Face

noncomputable def positionEmbedding {U V : Cube Lab k} (f : Face U V) : Fin U.dim ↪o Fin V.dim :=
  OrderEmbedding.ofStrictMono f.position f.position_strictMono

end Face

namespace Step

noncomputable def label : ∀ {U V : Cube Lab k}, Step U V → Arrow U V
  | _, _, .start f hl hd => {
    pom := discretePom _ f.positionEmbedding (OrderEmbedding.ofStrictMono id (fun _ _ h => h))
    source := by
      refine Sigma.ext (by rfl) ?_
      apply heq_of_eq
      funext i
      exact f.labels (f.position_spec i)
    target := rfl }
  | _, _, .stop f hu hd => {
    pom := discretePom _ (OrderEmbedding.ofStrictMono id (fun _ _ h => h)) f.positionEmbedding
    source := rfl
    target := by
      refine Sigma.ext (by rfl) ?_
      apply heq_of_eq
      funext i
      exact f.labels (f.position_spec i) }

end Step

namespace Word

/-- The full path label, including all orders, interfaces and labels. -/
noncomputable def label : ∀ {U V : Cube Lab k}, Word U V → Arrow U V
  | _, _, .nil U => Arrow.ident U
  | _, _, .cons s p => s.label.comp p.label

end Word

namespace Precubical

/-- Reachability at a genuine interval-pomset label. Interfaces and labels
are forced by isomorphism, rather than checked merely by cardinality. -/
def dPom (X : Precubical.{u,v} Lab k) {U V : Cube Lab k} (x : X.Cell U)
    (P : IntervalPom Lab) : Set (X.Cell V) :=
  {y | ∃ p : Word U V, X.Run p x y ∧ IntervalPomIso p.label.pom P}

/-- The paper's full endpoint-stabilisation notion on genuine pomset powers. -/
def CounterFreePom (X : Precubical.{u,v} Lab k) : Prop :=
  ∃ N : ℕ, 1 ≤ N ∧ ∀ (U : Cube Lab k) (x : X.Cell U)
    (P : EndoPom (cubeInterface U)),
      X.dPom (V := U) x (P.pow N).pom = X.dPom x (P.pow (N+1)).pom

end Precubical

namespace HDA

def LangPom (X : HDA.{u,v} Lab k) : Set (IntervalPom Lab) :=
  {P | ∃ (U V : Cube Lab k) (x : X.Cell U) (y : X.Cell V),
    X.initial x ∧ X.accepting y ∧ y ∈ X.toPrecubical.dPom x P}

end HDA
end CounterFreeHDA.Cubical
