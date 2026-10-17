import Paper19.Oracle

namespace Paper19
open OracleComputable

/-- A finite initial segment is computable relative to its stream oracle. -/
theorem oraclePrefix_computable (o : Stream) :
    OracleComputable o (fun n => List.ofFn (fun i : Fin n => o i)) := by
  have hc : OracleComputable o (fun p : Node × ℕ => p.1 ++ [p.2]) :=
    of_computable Computable.list_concat
  have hs : OracleComputable o (fun p : ℕ × (ℕ × Node) => p.2.2 ++ [o p.2.1]) :=
    hc.comp ((snd.comp snd).pair (oracle.comp (fst.comp snd)))
  have hh := OracleComputable.nat_rec (id : OracleComputable o (@id ℕ)) (const ([] : Node)) hs
  apply hh.of_eq
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    change (Nat.rec (motive := fun _ => Node) [] (fun i b => b ++ [o i]) n) ++ [o n] = _
    change Nat.rec (motive := fun _ => Node) [] (fun i b => b ++ [o i]) n = _ at ih
    rw [ih]
    simpa using (List.ofFn_succ' (fun i : Fin (n + 1) => o i)).symm

def boundOnList (p : Node × ℕ) : ℕ :=
  ∑ j ∈ Finset.range (p.2 + 1), (p.1.getD j 0 + 1)

theorem boundOnList_primrec : Primrec boundOnList := by
  have hs : Primrec₂ (fun l : Node => fun p : ℕ × ℕ => p.2 + (l.getD p.1 0 + 1)) :=
    Primrec.to₂ (Primrec.nat_add.comp (Primrec.snd.comp Primrec.snd)
      (Primrec.succ.comp ((Primrec.list_getD 0).comp Primrec.fst (Primrec.fst.comp Primrec.snd))))
  have hr := (Primrec.nat_rec (Primrec.const 0 : Primrec (fun _ : Node => (0 : ℕ))) hs).comp
    Primrec.fst (Primrec.succ.comp Primrec.snd)
  apply hr.of_eq
  intro p
  have he (k : ℕ) : Nat.rec (motive := fun _ => ℕ) 0
      (fun j s => s + (p.1.getD j 0 + 1)) k = ∑ j ∈ Finset.range k, (p.1.getD j 0 + 1) := by
    induction k with
    | zero => simp
    | succ k ih =>
      simpa only [Finset.sum_range_succ] using congrArg (fun s => s + (p.1.getD k 0 + 1)) ih
  exact he (p.2 + 1)

theorem ofFn_getD_oracle (o : Stream) {n j : ℕ} (hj : j < n) :
    (List.ofFn (fun i : Fin n => o i)).getD j 0 = o j := by
  rw [List.getD_eq_getElem _ 0 (by simpa using hj), List.getElem_ofFn]

theorem boundOnList_prefix (o : Stream) {n j : ℕ} (hj : j < n) :
    boundOnList (List.ofFn (fun i : Fin n => o i), j) = decodeBoundOf o j := by
  change (∑ k ∈ Finset.range (j + 1), _) = _
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k < j + 1 := Finset.mem_range.mp hk
  rw [ofFn_getD_oracle o (by omega)]

theorem decodeBound_oracle (o : Stream) : OracleComputable o (decodeBoundOf o) := by
  have h := (of_computable boundOnList_primrec.to_comp : OracleComputable o boundOnList).comp
    (((oraclePrefix_computable o).comp (of_computable Computable.succ)).pair id)
  apply h.of_eq
  intro j
  change boundOnList (List.ofFn (fun i : Fin (j + 1) => o i), j) = _
  exact boundOnList_prefix o (by omega)

def binaryTest (p : Node × ℕ) : Bool :=
  decide (∃ j < p.2 + 1, p.2 + 1 = boundOnList (p.1, j))

theorem binaryTest_computable : Computable binaryTest := by
  have hr : PrimrecPred (fun p : (Node × ℕ) × ℕ =>
      p.1.2 + 1 = boundOnList (p.1.1, p.2)) :=
    Primrec.eq.comp (Primrec.succ.comp (Primrec.snd.comp Primrec.fst))
      (boundOnList_primrec.comp ((Primrec.fst.comp Primrec.fst).pair Primrec.snd))
  have ha := hr.computablePred.not.boundedAll (Computable.succ.comp Computable.snd)
  have he : ComputablePred (fun p : Node × ℕ => ∃ j < p.2 + 1,
      p.2 + 1 = boundOnList (p.1, j)) := ha.not.of_eq (by simp)
  exact he.decide

theorem binary_oracle (o : Stream) : OracleComputable o (binaryOf o) := by
  have h := (of_computable binaryTest_computable : OracleComputable o binaryTest).comp
    (((oraclePrefix_computable o).comp (of_computable Computable.succ)).pair id)
  apply h.of_eq
  intro k
  change binaryTest (List.ofFn (fun i : Fin (k + 1) => o i), k) = binaryOf o k
  apply Bool.eq_iff_iff.mpr
  simp only [binaryTest, binaryOf, decide_eq_true_eq]
  constructor
  · rintro ⟨j, hj, he⟩
    exact ⟨j, by omega, by rwa [boundOnList_prefix o hj] at he⟩
  · rintro ⟨j, hj, he⟩
    exact ⟨j, by omega, by rw [boundOnList_prefix o (show j < k + 1 by omega)]; exact he⟩

/-- The forward Lemma 2 conversion is a genuine oracle-computable function. -/
theorem pathCode_oracle (o : Stream) :
    OracleComputable o (pairStream (binaryOf o) (decodeBoundOf o)) := by
  have hb : Primrec (fun p : ℕ × Bool => 2 * p.1 + if p.2 then 1 else 0) :=
    Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.fst)
      ((Primrec.dom_bool (fun b => if b then 1 else 0)).comp Primrec.snd)
  exact (of_computable hb.to_comp).comp ((decodeBound_oracle o).pair (binary_oracle o))

def bitMap (l : Node) : Bin := l.map (fun n => decide (n % 2 = 1))

theorem bitMap_primrec : Primrec bitMap :=
  Primrec.list_map Primrec.id (Primrec.to₂ ((Primrec.eq.comp
    (Primrec.nat_mod.comp Primrec.snd (Primrec.const 2)) (Primrec.const 1)).decide))

/-- The backward Lemma 2 conversion is oracle-computable on every input,
including streams that are not paths. Correctness needs the path hypothesis. -/
theorem pathDecode_oracle (o : Stream) :
    OracleComputable o (pathOfQT (streamBits o) (streamBounds o)) := by
  have hb : OracleComputable o (streamBounds o) :=
    (of_computable ((Primrec.nat_div.comp Primrec.id (Primrec.const 2)).to_comp)).comp oracle
  have hp := (oraclePrefix_computable o).comp hb
  have hcalc : Primrec (fun p : Node × ℕ => (completedBlocks (bitMap p.1)).getD p.2 0) :=
    (Primrec.list_getD 0).comp
      (Effective.blocks_primrec.comp (bitMap_primrec.comp Primrec.fst)) Primrec.snd
  apply ((of_computable hcalc.to_comp).comp (hp.pair id)).of_eq
  intro i
  simp [pathOfQT, bitMap, List.map_ofFn, streamBits, Function.comp_def]

end Paper19
