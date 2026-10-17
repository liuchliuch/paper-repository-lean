import CounterFreeHDA.InterfaceIso

namespace CounterFreeHDA.PomsetData
universe u
variable {Lab : Type u} {P Q : PomsetData Lab} {k : ℕ}

/-- Width is preserved by induced event embeddings. -/
theorem WidthLE.ofEmbedding (hw : P.WidthLE k) (f : Fin Q.n ↪ Fin P.n)
    (hp : ∀ e g, P.prec (f e) (f g) → Q.prec e g) : Q.WidthLE k := by
  classical
  intro A hA
  have hc : (A.image f).card = A.card := Finset.card_image_of_injective A f.injective
  rw [← hc]
  apply hw
  intro e he g hg
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp he
  obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hg
  exact fun h => hA a ha b hb (hp a b h)

theorem WidthLE.source_bound (hw : P.WidthLE k) (hP : IsIntervalPom P) : P.srcLen ≤ k := by
  rw [← Reinterface.sourceSet_card P]
  exact hw _ (Reinterface.source_antichain P hP)

theorem WidthLE.target_bound (hw : P.WidthLE k) (hP : IsIntervalPom P) : P.tgtLen ≤ k := by
  rw [← Reinterface.targetSet_card P]
  exact hw _ (Reinterface.target_antichain P hP)

end CounterFreeHDA.PomsetData
