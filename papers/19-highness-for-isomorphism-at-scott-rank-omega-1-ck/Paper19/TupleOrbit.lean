import Paper19.Projection

namespace Paper19
open scoped symmDiff

/-- The validity field expresses membership of each translation in its actual
Boolean group, independently of the coherence and named-root equations. -/
def ValidAut (T : Tree) := {c : CoherentAut T // ∀ n, GMem T n (c.h n)}
def ValidIso (T : Tree) := {c : CoherentIso T // ∀ n, GMem T n (c.h n)}

/-- One common automorphism acts on every coordinate of the tuple. -/
def TupleOrbit (T : Tree) {m : ℕ} (a b : Fin m → ℕ × Finset Node) : Prop :=
  ∃ c : ValidAut T, ∀ i, (b i).1 = (a i).1 ∧
    (b i).2 = (a i).2 ∆ c.val.h (a i).1

/-- Semantic content of the entire formula (8), including its zero-root
condition. N is any common upper bound on the tuple levels. -/
def TupleFormula (T : Tree) {m : ℕ} (N : ℕ) (a b : Fin m → ℕ × Finset Node) : Prop :=
  ∃ z : Finset Node, LiftSeq T N z ∧ projectTo T N z 0 = ∅ ∧
    ∀ i, (b i).1 = (a i).1 ∧ (b i).2 = (a i).2 ∆ projectTo T N z (a i).1

theorem tuple_orbit_formula {T : Tree} {m N : ℕ} (a b : Fin m → ℕ × Finset Node)
    (hN : ∀ i, (a i).1 ≤ N) : TupleOrbit T a b ↔ TupleFormula T N a b := by
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c.val.h N, ⟨fun k => c.val.h (N + k), rfl,
      fun k => c.val.coherence (N + k), fun k => c.property (N + k)⟩, ?_, ?_⟩
    · rw [coherent_projectTo c.val (Nat.zero_le N), c.val.root]
    · intro i
      rw [coherent_projectTo c.val (hN i)]
      exact hc i
  · rintro ⟨z, hlift, hroot, hb⟩
    obtain ⟨c, hc, hG⟩ := extend_lift hlift hroot
    refine ⟨⟨c, hG⟩, ?_⟩
    intro i
    have hproj : projectTo T N z (a i).1 = c.h (a i).1 := by
      rw [← hc, coherent_projectTo c (hN i)]
    simpa [hproj] using hb i

/-- Lemma 5 with actual group membership retained in its codomain. -/
def validIsoOfPath {T : Tree} {f : Stream} (hf : (STree T).IsPath f) : ValidIso T :=
  ⟨{ h := fun n => {streamPrefix f n}
     coherence := fun n => by
       rw [proj_singleton (streamPrefix_length f (n + 1)), streamPrefix_take f n (n + 1) (by omega)]
     root := by simp [streamPrefix] },
   fun n => GMem_singleton ⟨hf n, streamPrefix_length f n⟩⟩

end Paper19
