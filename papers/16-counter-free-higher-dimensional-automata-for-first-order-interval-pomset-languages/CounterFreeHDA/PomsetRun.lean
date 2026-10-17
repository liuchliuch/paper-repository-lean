import CounterFreeHDA.Reachability

namespace CounterFreeHDA.Cubical.Precubical
universe u v
variable {Lab : Type u} {k : ℕ} (X : Precubical.{u,v} Lab k) {U V : Cube Lab k}

/-- Any fixed actual ST decomposition gives the entire pomset endpoint relation. -/
theorem dPom_word (p : Word U V) (x : X.Cell U) (y : X.Cell V) :
    y ∈ X.dPom x p.label.pom ↔ X.Run p x y := by
  constructor
  · rintro ⟨q,hq,hiso⟩
    exact (Word.run_iff_of_label_iso q p hiso x y).mp hq
  · intro hp
    exact ⟨p,hp,⟨PomsetIso.refl _⟩⟩

end CounterFreeHDA.Cubical.Precubical
