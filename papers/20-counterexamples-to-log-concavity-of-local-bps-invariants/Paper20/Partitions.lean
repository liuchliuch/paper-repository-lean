import Paper20.Hilbert

/-! Correctness of the Appendix A partition recursion: it enumerates exactly
all positive weakly decreasing lists with the specified sum and cap. -/
namespace Paper20

/-- Mathematical specification independent of the enumeration algorithm. -/
def ValidPartition (cap n : ℕ) (ps : List ℕ) : Prop :=
  ps.sum = n ∧ ps.Pairwise (· ≥ ·) ∧ ∀ a ∈ ps, 0 < a ∧ a ≤ cap

lemma validPartition_nil (cap n : ℕ) : ValidPartition cap n [] ↔ n = 0 := by
  simp [ValidPartition, eq_comm]

lemma validPartition_cons (cap n a : ℕ) (ps : List ℕ) :
    ValidPartition cap n (a :: ps) ↔
      0 < a ∧ a ≤ cap ∧ a ≤ n ∧ ValidPartition a (n-a) ps := by
  constructor
  · rintro ⟨hs, hp, hb⟩
    have ha := hb a (by simp)
    have hpair := List.pairwise_cons.mp hp
    refine ⟨ha.1, ha.2, ?_, ?_, hpair.2, ?_⟩
    · simp only [List.sum_cons] at hs; omega
    · simp only [List.sum_cons] at hs; omega
    · intro x hx
      exact ⟨(hb x (by simp [hx])).1, hpair.1 x hx⟩
  · rintro ⟨ha, hac, han, hs, hp, hb⟩
    refine ⟨?_, List.pairwise_cons.mpr ⟨fun x hx => (hb x hx).2, hp⟩, ?_⟩
    · simp only [List.sum_cons]; omega
    · intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact ⟨ha, hac⟩
      · exact ⟨(hb x hx).1, le_trans (hb x hx).2 hac⟩

lemma validPartition_zero (cap : ℕ) (ps : List ℕ) :
    ValidPartition cap 0 ps ↔ ps = [] := by
  cases ps with
  | nil => simp [ValidPartition]
  | cons a ps =>
    rw [validPartition_cons]
    simp only [reduceCtorEq, iff_false]
    omega

/-- Soundness and completeness; the fuel bound is a genuine proved invariant. -/
theorem mem_partitionsCappedAux (fuel cap n : ℕ) (hf : n < fuel) (ps : List ℕ) :
    ps ∈ partitionsCappedAux fuel cap n ↔ ValidPartition cap n ps := by
  induction fuel generalizing cap n ps with
  | zero => omega
  | succ fuel ih =>
    by_cases hn : n = 0
    · subst hn
      simp [partitionsCappedAux, validPartition_zero]
    · rw [partitionsCappedAux, if_neg hn]
      simp only [List.mem_flatMap, List.mem_reverse, List.mem_range', List.mem_map]
      constructor
      · rintro ⟨a, ha, tail, ht, rfl⟩
        rw [validPartition_cons]
        have hac : a ≤ cap := by omega
        have han : a ≤ n := by omega
        refine ⟨by omega, hac, han, (ih a (n-a) (by omega) tail).mp ht⟩
      · intro hp
        cases ps with
        | nil => have := (validPartition_nil cap n).mp hp; contradiction
        | cons a tail =>
          obtain ⟨ha, hac, han, ht⟩ := (validPartition_cons cap n a tail).mp hp
          refine ⟨a, ?_, tail, (ih a (n-a) (by omega) tail).mpr ht, rfl⟩
          have ham : a ≤ min n cap := le_min han hac
          exact ⟨a-1, by omega, by omega⟩

/-- No partition is visited twice. -/
theorem nodup_partitionsCappedAux (fuel cap n : ℕ) :
    (partitionsCappedAux fuel cap n).Nodup := by
  induction fuel generalizing cap n with
  | zero => simp [partitionsCappedAux]
  | succ fuel ih =>
    by_cases hn : n = 0
    · simp [partitionsCappedAux, hn]
    · rw [partitionsCappedAux, if_neg hn, List.nodup_flatMap]
      constructor
      · intro a ha
        exact (ih a (n-a)).map (by intro x y he; exact List.cons.inj he |>.2)
      · have hl : ((List.range' 1 (min n cap)).reverse).Nodup := List.nodup_reverse.mpr (List.nodup_range' (s := 1) (n := min n cap))
        apply List.Pairwise.imp _ hl
        intro a b hab ps hpa hpb
        obtain ⟨as, has, rfl⟩ := List.mem_map.mp hpa
        obtain ⟨bs, hbs, he⟩ := List.mem_map.mp hpb
        exact hab (List.cons.inj he).1.symm

/-- The final enumeration contains every partition exactly once. -/
theorem nodup_partitionsOf (n : ℕ) : (partitionsOf n).Nodup :=
  nodup_partitionsCappedAux (n+1) n n

/-- The executable partition list ranges over precisely the partitions of `n`. -/
theorem mem_partitionsOf (n : ℕ) (ps : List ℕ) :
    ps ∈ partitionsOf n ↔ ValidPartition n n ps :=
  mem_partitionsCappedAux (n+1) n n (by omega) ps

/-- Every enumerated hook list has exactly `n` entries. -/
theorem hooksOf_length_of_mem_partitionsOf {n : ℕ} {ps : List ℕ}
    (hp : ps ∈ partitionsOf n) : (hooksOf ps).length = n :=
  hooksOf_length_eq n ((mem_partitionsOf n ps).mp hp).1

/-- The abstract partition datatype and the executable enumeration agree. -/
theorem Part.mem_partitionsOf {n : ℕ} (p : Part n) : p.parts ∈ partitionsOf n := by
  rw [Paper20.mem_partitionsOf]
  refine ⟨p.sum_eq, p.sorted, ?_⟩
  intro a ha
  refine ⟨p.pos a ha, ?_⟩
  have := List.single_le_sum (fun b hb => Nat.zero_le b) a ha
  rw [p.sum_eq] at this
  exact this

end Paper20
