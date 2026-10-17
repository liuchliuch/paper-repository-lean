import CounterFreeHDA.DeletionMatch
import CounterFreeHDA.Shared

namespace CounterFreeHDA.Deletion
universe u
variable {Lab : Type u} {A P : PomsetData Lab}
    (keepA : Fin A.n → Prop) (keepP : Fin P.n → Prop)
    [DecidablePred keepA] [DecidablePred keepP]

/-- Lift an actual event embedding through induced deletion. -/
noncomputable def lift (f : Fin A.n ↪ Fin P.n) (hk : ∀ e, keepA e → keepP (f e)) :
    Fin (data A keepA).n ↪ Fin (data P keepP).n where
  toFun a := retain P keepP (f (inclusion A keepA a)) (hk _ (inclusion_kept A keepA a))
  inj' := by
    intro a b hab
    apply (inclusion A keepA).injective
    apply f.injective
    have h := congrArg (inclusion P keepP) hab
    exact (inclusion_retain P keepP _ _).symm.trans (h.trans (inclusion_retain P keepP _ _))

@[simp] theorem inclusion_lift (f : Fin A.n ↪ Fin P.n) (hk : ∀ e, keepA e → keepP (f e))
    (a : Fin (data A keepA).n) :
    inclusion P keepP (lift keepA keepP f hk a) = f (inclusion A keepA a) := inclusion_retain P keepP _ _

end CounterFreeHDA.Deletion

namespace CounterFreeHDA
universe u
variable {Lab : Type u} {A B : PomsetData Lab}

theorem orderedSubset_enum_eq {r : ℕ} {S T : Finset (Fin r)} (h : S = T)
    (i : Fin S.card) (j : Fin T.card) (hij : i.val = j.val) :
    S.orderEmbOfFin rfl i = T.orderEmbOfFin rfl j := by
  subst T
  exact Finset.orderEmbOfFin_eq_orderEmbOfFin_iff.mpr hij

namespace Cubical.TrackGlue

theorem event_cover (m : GlueMatch A B) (e : Fin (glueData A B m).n) :
    (∃ a, leftEvent m a = e) ∨ (∃ b, rightEvent m b = e) := by
  classical
  cases hh : (index m).symm e with
  | left a =>
    refine Or.inl ⟨a.val,?_⟩
    exact (leftEvent_left m a).trans ((congrArg (index m) hh).symm.trans ((index m).apply_symm_apply e))
  | right b =>
    refine Or.inr ⟨b.val,?_⟩
    exact (rightEvent_right m b).trans ((congrArg (index m) hh).symm.trans ((index m).apply_symm_apply e))
  | mid i =>
    refine Or.inl ⟨A.tgt i,?_⟩
    exact (leftEvent_tgt m i).trans ((congrArg (index m) hh).symm.trans ((index m).apply_symm_apply e))

theorem leftEvent_eord (m : GlueMatch A B) (hA : IsIntervalPom A) (e f : Fin A.n) :
    (glueData A B m).eord (leftEvent m e) (leftEvent m f) ↔ A.eord e f := by
  change glueEord m.len_eq ((index m).symm (index m _)) ((index m).symm (index m _)) ↔ _
  rw [Equiv.symm_apply_apply,Equiv.symm_apply_apply]
  exact glueEord_left m hA e f

end Cubical.TrackGlue
end CounterFreeHDA
