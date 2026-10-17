import Paper15.OrbitCoverage
import Paper15.OrbitRows

noncomputable section
namespace Paper15.OrbitCheck
open Paper15 Exact

def Tables.toDet (T : Tables) : DetTriangle :=
  ⟨⟨fun y z => signOfBit (T.A y z),fun _ _ => legalSign_signOfBit _⟩,
   ⟨fun z x => signOfBit (T.B z x),fun _ _ => legalSign_signOfBit _⟩,
   ⟨fun x y => signOfBit (T.C x y),fun _ _ => legalSign_signOfBit _⟩⟩

lemma decode_toDet (r : Nat) : (decode r).toDet=DetTriangle.ofPattern r := rfl
lemma Tables.toDet_slot (T : Tables) (p : Fin 27) :
    T.toDet.signAtPos p.val=signOfBit (T.slot p) := by
  fin_cases p <;> simp [Tables.toDet,Tables.slot,DetTriangle.signAtPos]
lemma Tables.toDet_bits (T : Tables) (p : Fin 27) : T.toDet.bits p=T.slot p := by
  apply signOfBit_injective
  rw [DetTriangle.signOfBit_bits,Tables.toDet_slot]

lemma relabel_toDet (a b c : Equiv.Perm (Fin 3)) (T : Tables) :
    (relabel a b c T).toDet=valueReindex a b c T.toDet := rfl
lemma party_toDet (n : Nat) (T : Tables) :
    (party n T).toDet=applyPerm (perm3 n) T.toDet := by
  have hn : n%6<6 := Nat.mod_lt _ (by decide)
  generalize he : n%6=k at *
  interval_cases k <;> apply DetTriangle.ext <;> apply RespTable.ext <;> intro i j <;>
    simp [party,perm3,he,Tables.toDet,applyPerm,swapXY,swapYZ,swapXZ,cycleXYZ,cycleXZY,RespTable.swap,Equiv.swap_apply_def]
lemma flip_toDet (T : Tables) : T.flip.toDet=flipAll T.toDet := by
  apply DetTriangle.ext <;> apply RespTable.ext <;> intro i j <;>
    simp [Tables.flip,Tables.toDet,flipAll,RespTable.flip] <;>
    cases T.A i j <;> cases T.B i j <;> cases T.C i j <;> norm_num [signOfBit]

def codeSymmetry (code : Nat) : Symmetry where
  σX:=perm3 (code/2/216)
  σY:=perm3 (code/2/36%6)
  σZ:=perm3 (code/2/6%6)
  srcPerm:=perm3 (code/2%6)
  flip:=decide (code%2=1)

lemma act_toDet (code : Nat) (T : Tables) :
    (act code T).toDet=(codeSymmetry code).apply T.toDet := by
  unfold act
  split_ifs with h
  · rw [flip_toDet,party_toDet,relabel_toDet]
    simp [codeSymmetry,Symmetry.apply,h,perm3,Nat.mod_mod]
  · rw [party_toDet,relabel_toDet]
    simp [codeSymmetry,Symmetry.apply,h,perm3,Nat.mod_mod]

lemma transition_sound (r s code : Nat) (p : Fin 27)
    (h : transition r p.val s code=true) :
    (codeSymmetry code).apply (DetTriangle.ofPattern s)=flipAt (DetTriangle.ofPattern r) p := by
  have hall := (Bool.and_eq_true_iff.mp h).2
  have heq (q : Fin 27) : (act code (decode s)).slot q =
      (if q.val=p.val then !((decode r).slot q) else (decode r).slot q) := by
    have hq := List.all_eq_true.mp hall q (by simp [slots])
    exact beq_iff_eq.mp hq
  apply DetTriangle.signAtPos_injective
  intro q
  rw [← DetTriangle.signOfBit_bits,← DetTriangle.signOfBit_bits,flipAt_bits]
  congr 1
  rw [← decode_toDet s,← act_toDet,Tables.toDet_bits,heq]
  rw [← decode_toDet r,Tables.toDet_bits]
  by_cases hq : q=p
  · subst q; simp [Tables.toDet_bits]
  · have hv : q.val≠p.val := fun h => hq (Fin.ext h)
    simp [hv,Function.update_of_ne hq,Tables.toDet_bits]

lemma rowValid_sound {r : Nat} {row : Row} (h : rowValid r row=true) (p : Fin 27) :
    ∃s,representatives.mem s ∧ ∃g : Symmetry,g.apply (DetTriangle.ofPattern s)=flipAt (DetTriangle.ofPattern r) p := by
  let c:=row.at p
  refine ⟨representatives.at c.target,representatives.at_mem _,codeSymmetry c.code,?_⟩
  exact transition_sound r _ _ p (List.all_eq_true.mp h p (by simp [slots]))

end Paper15.OrbitCheck
