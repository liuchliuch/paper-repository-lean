import Paper19.EffectiveCoding

namespace Paper19

/-- Total functions with decidable computable graphs are computable. The
proof explicitly enumerates the standard output codes and searches the graph. -/
theorem computable_of_graph {α β : Type} [Primcodable α] [Denumerable β]
    (f : α → β) (hgraph : ComputablePred (fun p : α × β => f p.1 = p.2)) : Computable f := by
  classical
  let search : α → ℕ → Option β := fun a n =>
    if f a = Denumerable.ofNat β n then some (Denumerable.ofNat β n) else none
  have hv : Computable (fun p : α × ℕ => Denumerable.ofNat β p.2) :=
    (Primrec.ofNat β).to_comp.comp Computable.snd
  have hp := hgraph.comp' (Computable.fst.pair hv)
  have hs : Computable₂ search := by
    simpa [search, Bool.cond_decide] using Computable.cond hp.decide
      (Primrec.option_some.to_comp.comp hv) (Computable.const none)
  apply (Partrec.rfindOpt hs).of_eq
  intro a
  have hmem : ∀ b, b ∈ Nat.rfindOpt (search a) → b = f a := by
    intro b hb
    obtain ⟨n, hn⟩ := Nat.rfindOpt_spec hb
    by_cases he : f a = Denumerable.ofNat β n
    · have hb' : Denumerable.ofNat β n = b := by simpa [search, he] using hn
      exact hb'.symm.trans he.symm
    · simp [search, he] at hn
  have hd : (Nat.rfindOpt (search a)).Dom := Nat.rfindOpt_dom.mpr
    ⟨Encodable.encode (f a), f a, by simp [search]⟩
  apply Part.ext
  intro b
  constructor
  · intro hb
    simpa using hmem b hb
  · intro hb
    have he : b = f a := by simpa using hb
    subst b
    have hm := Part.get_mem hd
    rwa [hmem _ hm] at hm

end Paper19
