import CounterFreeHDA.Antichain

/-! A constructive finite peeling criterion for interval orders. The end-time
minimum supplies a legal termination whenever no new minimal event can start. -/
namespace CounterFreeHDA
universe u
variable {Lab : Type u} {P : PomsetData Lab}

namespace PomsetData

def Minimal (P : PomsetData Lab) (e : Fin P.n) : Prop := ∀ f, ¬ P.prec f e

def Startable (P : PomsetData Lab) (e : Fin P.n) : Prop := ¬ P.inSrc e ∧ P.Minimal e

def Stoppable (P : PomsetData Lab) (e : Fin P.n) : Prop :=
  P.inSrc e ∧ ¬ P.inTgt e ∧ ∀ f, ¬ P.inSrc f → P.prec e f

end PomsetData

namespace IsIntervalPom

/-- The interval condition gives a genuine next ST step, or the identity case.
The last condition is precisely the new cross precedence introduced by gluing
an elementary terminator to the residual pomset. -/
theorem peel (hP : IsIntervalPom P) :
    (∀ e, P.inSrc e ∧ P.inTgt e) ∨
    (∃ e, P.Startable e) ∨ (∃ e, P.Stoppable e) := by
  classical
  by_cases hstart : ∃ e, P.Startable e
  · exact Or.inr (Or.inl hstart)
  have hminimal : ∀ e, P.Minimal e → P.inSrc e := by
    intro e he
    by_contra hn
    exact hstart ⟨e,hn,he⟩
  by_cases hout : ∃ f, ¬ P.inSrc f
  · obtain ⟨f,hf⟩ := hout
    obtain ⟨s,t,hr⟩ := hP.interval_rep
    obtain ⟨e,_,he⟩ := Finset.exists_min_image (Finset.univ : Finset (Fin P.n)) t ⟨f,Finset.mem_univ f⟩
    have hse : s e ≤ t e := le_of_not_gt (fun h => hP.prec_irrefl e ((hr e e).mpr h))
    have hem : P.Minimal e := by
      intro g hg
      have hge : t g < s e := (hr g e).mp hg
      have heg := he g (Finset.mem_univ g)
      linarith
    have hes := hminimal e hem
    have hcross : ∀ g, ¬ P.inSrc g → P.prec e g := by
      intro g hgs
      have hnm : ¬ P.Minimal g := fun hm => hgs (hminimal g hm)
      change ¬ (∀ a, ¬ P.prec a g) at hnm
      push_neg at hnm
      obtain ⟨a,ha⟩ := hnm
      apply (hr e g).mpr
      exact lt_of_le_of_lt (he a (Finset.mem_univ a)) ((hr a g).mp ha)
    have het : ¬ P.inTgt e := fun ht => hP.tgt_maximal e ht f (hcross f hf)
    exact Or.inr (Or.inr ⟨e,hes,het,hcross⟩)
  · have hall : ∀ e, P.inSrc e := by simpa only [not_exists,not_not] using hout
    by_cases ht : ∀ e, P.inTgt e
    · exact Or.inl (fun e => ⟨hall e,ht e⟩)
    · push_neg at ht
      obtain ⟨e,he⟩ := ht
      exact Or.inr (Or.inr ⟨e,hall e,he,fun f hf => False.elim (hf (hall f))⟩)

end IsIntervalPom
end CounterFreeHDA
