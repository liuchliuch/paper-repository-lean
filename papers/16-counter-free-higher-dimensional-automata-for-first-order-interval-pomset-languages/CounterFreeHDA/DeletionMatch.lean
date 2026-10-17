import CounterFreeHDA.Deletion

namespace CounterFreeHDA
universe u

/-- An increasing equivalence of finite ordered positions preserves indices. -/
theorem increasingEquiv_val {r s : ℕ} (e : Fin r ≃ Fin s) (hm : StrictMono e) (i : Fin r) :
    (e i).val = i.val := by
  have hn : r = s := by simpa only [Fintype.card_fin] using Fintype.card_congr e
  let f : Fin r → Fin r := fun i => Fin.cast hn.symm (e i)
  have hf : StrictMono f := fun _ _ h => hm h
  exact congrArg Fin.val (le_antisymm (hf.le_id i) (hf.id_le i))

namespace Deletion
variable {Lab : Type u} {A B : PomsetData Lab}
variable (m : GlueMatch A B) (keepA : Fin A.n → Prop) (keepB : Fin B.n → Prop)
    [DecidablePred keepA] [DecidablePred keepB]

/-- A reduced interface match retains the exact original interface positions,
so repeated labels cannot introduce an arbitrary seam permutation. -/
structure Match where
  toGlueMatch : GlueMatch (data A keepA) (data B keepB)
  positions : ∀ i : Fin (target A keepA).card,
    Fin.cast m.len_eq ((target A keepA).orderEmbOfFin rfl i) =
      (source B keepB).orderEmbOfFin rfl (Fin.cast toGlueMatch.len_eq i)

private theorem enum_witness {r : ℕ} (S : Finset (Fin r)) (i : Fin r) (hi : i ∈ S) :
    ∃ j : Fin S.card, S.orderEmbOfFin rfl j = i := by
  let j := (S.orderIsoOfFin rfl).symm ⟨i,hi⟩
  exact ⟨j,congrArg Subtype.val ((S.orderIsoOfFin rfl).apply_symm_apply ⟨i,hi⟩)⟩

/-- Delete the same actual events from both copies of the gluing interface. -/
noncomputable def matching
    (hk : ∀ i, keepA (A.tgt i) ↔ keepB (B.src (Fin.cast m.len_eq i))) : Match m keepA keepB := by
  let T := target A keepA
  let S := source B keepB
  let a : Fin T.card → Fin B.srcLen := fun i => Fin.cast m.len_eq (T.orderEmbOfFin rfl i)
  let b : Fin S.card → Fin B.srcLen := S.orderEmbOfFin rfl
  have ha : StrictMono a := fun _ _ h => (T.orderEmbOfFin rfl).strictMono h
  have hb : StrictMono b := (S.orderEmbOfFin rfl).strictMono
  have hr : Set.range a = Set.range b := by
    ext j
    constructor
    · rintro ⟨i,rfl⟩
      have hA := target_kept A keepA (T.orderEmbOfFin_mem rfl i)
      have hB := (hk (T.orderEmbOfFin rfl i)).mp hA
      exact enum_witness S _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hB⟩)
    · rintro ⟨i,rfl⟩
      let j := Fin.cast m.len_eq.symm (b i)
      have hB := source_kept B keepB (S.orderEmbOfFin_mem rfl i)
      have hA : keepA (A.tgt j) := (hk j).mpr (by simpa only [j,Fin.cast_cast,Fin.cast_refl,id_eq] using hB)
      obtain ⟨l,hl⟩ := enum_witness T j (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hA⟩)
      refine ⟨l,?_⟩
      exact (congrArg (Fin.cast m.len_eq) hl).trans (Fin.ext rfl)
  let E := enumerationEquiv a b ha.injective hb.injective hr
  have he : ∀ i, b (E i) = a i := enumerationEquiv_event _ _ _ _ _
  have hm : StrictMono E := by
    intro i j hij
    apply hb.lt_iff_lt.mp
    exact (congrArg₂ (fun i j : Fin B.srcLen => i < j) (he i) (he j)).mpr (ha hij)
  have hn : T.card = S.card := by simpa only [Fintype.card_fin] using Fintype.card_congr E
  have hpos : ∀ i, a i = b (Fin.cast hn i) := by
    intro i
    exact (he i).symm.trans (congrArg b (Fin.ext (increasingEquiv_val E hm i)))
  let matchAB : GlueMatch (data A keepA) (data B keepB) := {
    len_eq := hn
    lab_eq i := by
      have hleft : (data A keepA).lab ((data A keepA).tgt i) = A.lab (A.tgt (T.orderEmbOfFin rfl i)) :=
        congrArg A.lab (inclusion_target A keepA i)
      have hright : (data B keepB).lab ((data B keepB).src (Fin.cast hn i)) = B.lab (B.src (b (Fin.cast hn i))) :=
        congrArg B.lab (inclusion_source B keepB (Fin.cast hn i))
      exact hleft.trans ((m.lab_eq _).trans ((congrArg (B.lab ∘ B.src) (hpos i)).trans hright.symm)) }
  exact ⟨matchAB,hpos⟩

end Deletion
end CounterFreeHDA
