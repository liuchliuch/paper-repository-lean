import CounterFreeHDA.ElementaryFactors

/-! Automatic ST decomposition of every bounded-width interval pomset.
No path, factorization or mapping property is a premise. -/
namespace CounterFreeHDA.Cubical
universe u v
variable {Lab : Type u} {k : ℕ}

/-- Every actual interval pomset of width at most k has an elementary ST
representation with the same events, labels, both orders and interfaces. -/
theorem st_representation (P : PomsetData Lab) (hP : IsIntervalPom P) (hw : P.WidthLE k) :
    STRepresented (k := k) P := by
  generalize hn : stMeasure P = n
  induction n using Nat.strong_induction_on generalizing P with
  | h n ih =>
    rcases hP.peel with hfull | hstart | hstop
    · exact STRepresented.full hP hw hfull
    · obtain ⟨e,he⟩ := hstart
      let F := startFactor P hP hw e he
      apply F.represented
      apply ih (stMeasure F.tail.pom.val) (by rw [← hn]; exact F.decreases)
      · exact F.tail.pom.property
      · exact F.width
      · rfl
    · obtain ⟨e,hes,het,hc⟩ := hstop
      obtain ⟨i,rfl⟩ := hes
      let F := stopFactor P hP hw i het hc
      apply F.represented
      apply ih (stMeasure F.tail.pom.val) (by rw [← hn]; exact F.decreases)
      · exact F.tail.pom.property
      · exact F.width
      · rfl

namespace Arrow
variable {U V : Cube Lab k} {Y : Precubical.{u,v} Lab k}

/-- **Lemma 3.1(b).** Full characteristic-HDA mapping property for every
actual bounded-width interval pomset, with automatic ST representation. -/
theorem lemma_3_1_b (A : Arrow U V) (hw : A.pom.val.WidthLE k)
    (x : Y.Cell U) (y : Y.Cell V) :
    y ∈ Y.dPom x A.pom ↔ ∃ a : Map (track A.pom.val) Y,
      a.app A.sourceCell = x ∧ a.app A.targetCell = y := by
  obtain ⟨p,hp⟩ := (st_representation A.pom.val A.pom.property hw).typed A
  exact A.mapping_iff_of_representation p hp x y

/-- The actual pomset labels a complete path in its own characteristic HDA. -/
theorem complete_path (A : Arrow U V) (hw : A.pom.val.WidthLE k) :
    A.targetCell ∈ (track A.pom.val).dPom A.sourceCell A.pom := by
  apply (A.lemma_3_1_b hw _ _).mpr
  exact ⟨{app := fun c => c,natural := fun _ _ => rfl},rfl,rfl⟩

end Arrow
end CounterFreeHDA.Cubical
