import CounterFreeHDA.CharacteristicLanguage
import CounterFreeHDA.Induced

namespace CounterFreeHDA.Induced
universe u
variable {Lab : Type u} (P : PomsetData Lab) (keep : Fin P.n → Prop) [DecidablePred keep]
    (S : Finset (Fin P.srcLen)) (T : Finset (Fin P.tgtLen))
    (hS : ∀ i ∈ S, keep (P.src i)) (hT : ∀ i ∈ T, keep (P.tgt i))

@[simp] theorem include_lab (e : Fin (data P keep S T hS hT).n) :
    P.lab (includeEvent P keep S T hS hT e) = (data P keep S T hS hT).lab e := rfl

@[simp] theorem include_prec (e f : Fin (data P keep S T hS hT).n) :
    P.prec (includeEvent P keep S T hS hT e) (includeEvent P keep S T hS hT f) ↔
      (data P keep S T hS hT).prec e f := Iff.rfl

@[simp] theorem include_eord (e f : Fin (data P keep S T hS hT).n) :
    P.eord (includeEvent P keep S T hS hT e) (includeEvent P keep S T hS hT f) ↔
      (data P keep S T hS hT).eord e f := Iff.rfl

theorem include_kept (e : Fin (data P keep S T hS hT).n) :
    keep (includeEvent P keep S T hS hT e) := ((index P keep).symm e).property

@[simp] theorem include_source (i : Fin S.card) :
    includeEvent P keep S T hS hT ((data P keep S T hS hT).src i) =
      P.src (S.orderEmbOfFin rfl i) :=
  congrArg Subtype.val ((index P keep).symm_apply_apply _)

@[simp] theorem include_target (i : Fin T.card) :
    includeEvent P keep S T hS hT ((data P keep S T hS hT).tgt i) =
      P.tgt (T.orderEmbOfFin rfl i) :=
  congrArg Subtype.val ((index P keep).symm_apply_apply _)

end CounterFreeHDA.Induced
