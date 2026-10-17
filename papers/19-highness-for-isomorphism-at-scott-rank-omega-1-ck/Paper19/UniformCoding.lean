import Paper19.UniformOracle
import Paper19.OracleCoding

namespace Paper19
open UniformOracleComputable

theorem prefix_uniform : UniformOracleComputable (fun o n => List.ofFn (fun i : Fin n => o i)) := by
  have hc : UniformOracleComputable (fun _ (p : Node × ℕ) => p.1 ++ [p.2]) :=
    base Computable.list_concat
  have hs : UniformOracleComputable (fun o (p : ℕ × (ℕ × Node)) => p.2.2 ++ [o p.2.1]) :=
    hc.comp ((snd.comp snd).pair (query.comp (fst.comp snd)))
  have hh := UniformOracleComputable.nat_rec
    (id : UniformOracleComputable (fun _ => @id ℕ)) (const ([] : Node)) hs
  apply hh.of_eq
  intro o n
  induction n with
  | zero => rfl
  | succ n ih =>
    change (Nat.rec (motive := fun _ => Node) [] (fun i b => b ++ [o i]) n) ++ [o n] = _
    change Nat.rec (motive := fun _ => Node) [] (fun i b => b ++ [o i]) n = _ at ih
    rw [ih]
    simpa using (List.ofFn_succ' (fun i : Fin (n + 1) => o i)).symm

theorem bounds_uniform : UniformOracleComputable (fun o => decodeBoundOf o) := by
  have h := (base boundOnList_primrec.to_comp : UniformOracleComputable (fun _ => boundOnList)).comp
    ((prefix_uniform.comp (base Computable.succ)).pair id)
  apply h.of_eq
  intro o j
  change boundOnList (List.ofFn (fun i : Fin (j + 1) => o i), j) = _
  exact boundOnList_prefix o (by omega)

theorem binary_uniform : UniformOracleComputable (fun o => binaryOf o) := by
  have h := (base binaryTest_computable : UniformOracleComputable (fun _ => binaryTest)).comp
    ((prefix_uniform.comp (base Computable.succ)).pair id)
  apply h.of_eq
  intro o k
  change binaryTest (List.ofFn (fun i : Fin (k + 1) => o i), k) = binaryOf o k
  apply Bool.eq_iff_iff.mpr
  simp only [binaryTest, binaryOf, decide_eq_true_eq]
  constructor
  · rintro ⟨j, hj, he⟩
    exact ⟨j, by omega, by rwa [boundOnList_prefix o hj] at he⟩
  · rintro ⟨j, hj, he⟩
    exact ⟨j, by omega, by rw [boundOnList_prefix o (show j < k + 1 by omega)]; exact he⟩

/-- One oracle program, independent of both o and the tree T. -/
theorem pathCode_uniform :
    UniformOracleComputable (fun o => pairStream (binaryOf o) (decodeBoundOf o)) := by
  have hb : Primrec (fun p : ℕ × Bool => 2 * p.1 + if p.2 then 1 else 0) :=
    Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.fst)
      ((Primrec.dom_bool (fun b => if b then 1 else 0)).comp Primrec.snd)
  exact (base hb.to_comp).comp (bounds_uniform.pair binary_uniform)

/-- One inverse oracle program, also independent of T. -/
theorem pathDecode_uniform :
    UniformOracleComputable (fun o => pathOfQT (streamBits o) (streamBounds o)) := by
  have hb : UniformOracleComputable (fun o => streamBounds o) :=
    (base ((Primrec.nat_div.comp Primrec.id (Primrec.const 2)).to_comp)).comp query
  have hp := prefix_uniform.comp hb
  have hc : Primrec (fun p : Node × ℕ => (completedBlocks (bitMap p.1)).getD p.2 0) :=
    (Primrec.list_getD 0).comp
      (Effective.blocks_primrec.comp (bitMap_primrec.comp Primrec.fst)) Primrec.snd
  apply ((base hc.to_comp).comp (hp.pair id)).of_eq
  intro o i
  simp [pathOfQT, bitMap, List.map_ofFn, streamBits, Function.comp_def]

end Paper19
