import CounterFreeHDA.AutomaticST
import CounterFreeHDA.IdentityComposition

namespace CounterFreeHDA.Cubical
universe u
variable {Lab : Type u} {k : ℕ}

namespace Word

def length : {U V : Cube Lab k} → Word U V → ℕ
  | _,_,.nil _ => 0
  | _,_,.cons _ p => p.length+1

end Word

theorem stMeasure_comp {U V W : Cube Lab k} (A : Arrow U V) (B : Arrow V W) :
    stMeasure (A.comp B).pom.val = stMeasure A.pom.val + stMeasure B.pom.val := by
  have hc := glue_card A.pom.val B.pom.val (GlueMatch.ofType (A.target.trans B.source.symm))
  have haS := srcLen_le A.pom.val
  have haT := tgtLen_le A.pom.val
  have hbS := srcLen_le B.pom.val
  have hbT := tgtLen_le B.pom.val
  have hm : A.pom.val.tgtLen = B.pom.val.srcLen := (GlueMatch.ofType (A.target.trans B.source.symm)).len_eq
  change (glueData A.pom.val B.pom.val (GlueMatch.ofType (A.target.trans B.source.symm))).n + A.pom.val.tgtLen = A.pom.val.n + B.pom.val.n at hc
  change stMeasure (glueData _ _ _) = _
  unfold stMeasure
  change 2 * (glueData A.pom.val B.pom.val _).n - A.pom.val.srcLen - B.pom.val.tgtLen = _
  omega

theorem stMeasure_step {U V : Cube Lab k} (s : Step U V) : stMeasure s.label.pom.val = 1 := by
  cases s with
  | start f hl hd =>
    change 2*V.dim-U.dim-V.dim = 1
    omega
  | stop f hu hd =>
    change 2*U.dim-U.dim-V.dim = 1
    omega

theorem Word.stMeasure_label {U V : Cube Lab k} (p : Word U V) : stMeasure p.label.pom.val = p.length := by
  induction p with
  | nil U =>
    change 2*U.dim-U.dim-U.dim = 0
    omega
  | cons s p ih =>
    rw [Word.label,stMeasure_comp,stMeasure_step,ih]
    change 1+p.length = p.length+1
    omega

theorem stMeasure_iso {P Q : PomsetData Lab} (φ : PomsetIso P Q) : stMeasure P = stMeasure Q := by
  have he : P.n = Q.n := by simpa only [Fintype.card_fin] using Fintype.card_congr φ.toEquiv
  have hs : P.srcLen = Q.srcLen := by simpa only [Fintype.card_fin] using Fintype.card_congr φ.srcEquiv
  have ht : P.tgtLen = Q.tgtLen := by simpa only [Fintype.card_fin] using Fintype.card_congr φ.tgtEquiv
  simp only [stMeasure,he,hs,ht]

/-- A bounded actual pomset of ST measure one is a single genuine elementary
starter or terminator, up to the full event/order/interface isomorphism. -/
theorem elementary_of_measure_one {U V : Cube Lab k} (A : BoundedArrow U V)
    (hm : stMeasure A.pom.val = 1) : ∃ s : Step U V, Nonempty (PomsetIso s.label.pom.val A.pom.val) := by
  obtain ⟨p,⟨φ⟩⟩ := (st_representation A.pom.val A.pom.property A.width).typed A.toArrow
  have hp : p.length = 1 := (p.stMeasure_label).symm.trans ((stMeasure_iso φ).trans hm)
  cases p with
  | nil U => change 0 = 1 at hp; omega
  | cons s p =>
    cases p with
    | nil V =>
      exact ⟨s,⟨((BoundedArrow.ofStep s).identityRightIso).symm.trans φ⟩⟩
    | cons t p =>
      change (p.length+1)+1 = 1 at hp
      omega

end CounterFreeHDA.Cubical
