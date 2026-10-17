import Paper15.CertificateData.Positions
namespace Paper15.OrbitCheck

lemma positionMaps_correct {g : Nat} (hg : g<1296) (p : Fin 27) :
    (positionMaps.get g).at p=(position g p).val := by
  have h := List.all_eq_true.mp positionMaps_checked g (List.mem_range.mpr hg)
  exact beq_iff_eq.mp (List.all_eq_true.mp h p (by simp [slots]))

/-- Geometric maps are checked once for the whole finite group. Individual
transitions then require only direct bit tests and exact equality. -/
noncomputable def fastTransition (r bit s code : Nat) : Bool :=
  decide (code/2<1296) && decide (bit<27) && slots.all (fun p =>
    (if code%2=1 then !(s.testBit ((positionMaps.get (code/2)).at p))
      else s.testBit ((positionMaps.get (code/2)).at p)) ==
    (if p.val=bit then !(r.testBit p.val) else r.testBit p.val))

lemma fastTransition_sound {r bit s code : Nat} (h : fastTransition r bit s code=true) :
    transition r bit s code=true := by
  obtain ⟨⟨hg,hb⟩,hall⟩ := (Bool.and_eq_true_iff.mp h).imp (fun x => Bool.and_eq_true_iff.mp x) id
  have hgroup : code/2<1296 := of_decide_eq_true hg
  apply Bool.and_eq_true_iff.mpr
  refine ⟨hb,List.all_eq_true.mpr (fun p hp => ?_)⟩
  have hq := List.all_eq_true.mp hall p hp
  simpa only [act_slot,decode_slot,positionMaps_correct hgroup] using hq

noncomputable def fastRowValid (r : Nat) (row : Row) : Bool :=
  slots.all (fun p => fastTransition r p.val (representatives.at (row.at p).target) (row.at p).code)

lemma fastRowValid_sound {r : Nat} {row : Row} (h : fastRowValid r row=true) : rowValid r row=true := by
  apply List.all_eq_true.mpr
  intro p hp
  exact fastTransition_sound (List.all_eq_true.mp h p hp)
end Paper15.OrbitCheck
