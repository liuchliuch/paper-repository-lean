import Paper02.SparseRecovery

/-! Compact, bounded integer sparse candidates for an operational exhaustive
 decoder. Codes have K coordinate/value slots, rather than d integer registers. -/

noncomputable section
namespace Paper02.CompactCandidates
open Finset

abbrev CompactCode (d U K : ℕ) := Fin K → Option (Fin d × Fin (2 * U + 1))

def integerValue {U : ℕ} (a : Fin (2 * U + 1)) : ℤ := (a.val : ℤ) - U

def encodeValue {U : ℕ} (a : ℤ) (ha : -(U : ℤ) ≤ a ∧ a ≤ U) : Fin (2 * U + 1) :=
  ⟨(a + U).toNat, by omega⟩

lemma integerValue_encodeValue {U : ℕ} (a : ℤ) (ha : -(U : ℤ) ≤ a ∧ a ≤ U) :
    integerValue (encodeValue a ha) = a := by
  simp only [integerValue, encodeValue]
  omega

def slotValue {d U : ℕ} (entry : Option (Fin d × Fin (2 * U + 1))) (i : Fin d) : ℤ :=
  match entry with
  | none => 0
  | some (j, a) => if j = i then integerValue a else 0

def candidateValue {d U K : ℕ} (code : CompactCode d U K) (i : Fin d) : ℤ :=
  ∑ j, slotValue (code j) i

def encode {d U K : ℕ} (v : Fin d → ℤ)
    (hv : ∀ i, -(U : ℤ) ≤ v i ∧ v i ≤ U) : CompactCode d U K :=
  fun j => if h : j.val < (SparseRecovery.integerSupport v).card then
    let i := (SparseRecovery.integerSupport v).equivFin.symm ⟨j.val, h⟩
    some (i.val, encodeValue (v i.val) (hv i.val)) else none

lemma mem_integerSupport {d : ℕ} (v : Fin d → ℤ) (i : Fin d) :
    i ∈ SparseRecovery.integerSupport v ↔ v i ≠ 0 := by
  classical
  simp [SparseRecovery.integerSupport]

lemma encode_coordinate_injective {d U K : ℕ} (v : Fin d → ℤ)
    (hv : ∀ i, -(U : ℤ) ≤ v i ∧ v i ≤ U)
    {j k : Fin K} {a b : Fin d × Fin (2 * U + 1)}
    (hj : encode v hv j = some a) (hk : encode v hv k = some b)
    (hi : a.1 = b.1) : j = k := by
  classical
  by_cases hj' : j.val < (SparseRecovery.integerSupport v).card
  · by_cases hk' : k.val < (SparseRecovery.integerSupport v).card
    · simp only [encode, dif_pos hj', dif_pos hk', Option.some.injEq] at hj hk
      have he : (SparseRecovery.integerSupport v).equivFin.symm ⟨j.val, hj'⟩ =
          (SparseRecovery.integerSupport v).equivFin.symm ⟨k.val, hk'⟩ := by
        apply Subtype.ext
        exact (congrArg Prod.fst hj).trans (hi.trans (congrArg Prod.fst hk).symm)
      have hh := (SparseRecovery.integerSupport v).equivFin.symm.injective he
      exact Fin.ext (congrArg (fun z : Fin (SparseRecovery.integerSupport v).card => z.val) hh)
    · simp [encode, hk'] at hk
  · simp [encode, hj'] at hj

/-- Every bounded K-sparse integer vector is represented by K bounded slots.
The encoded coordinate slots are distinct, so no unbounded partial sums are
needed when reading a candidate coordinate. -/
theorem candidateValue_encode {d U K : ℕ} (v : Fin d → ℤ)
    (hv : ∀ i, -(U : ℤ) ≤ v i ∧ v i ≤ U)
    (hs : (SparseRecovery.integerSupport v).card ≤ K) :
    candidateValue (encode (K := K) v hv) = v := by
  classical
  let s := SparseRecovery.integerSupport v
  let e := s.equivFin
  funext i
  by_cases hi : i ∈ s
  · let j0 : Fin K := ⟨(e ⟨i, hi⟩).val, lt_of_lt_of_le (e ⟨i, hi⟩).isLt hs⟩
    have hj0 : j0.val < s.card := (e ⟨i, hi⟩).isLt
    have he0 : e.symm ⟨j0.val, hj0⟩ = ⟨i, hi⟩ := e.symm_apply_apply ⟨i, hi⟩
    unfold candidateValue
    rw [Finset.sum_eq_single j0]
    · simp only [encode, show j0.val < (SparseRecovery.integerSupport v).card from hj0,
        ↓reduceDIte]
      change slotValue (some ((e.symm ⟨j0.val, hj0⟩).val,
        encodeValue (v (e.symm ⟨j0.val, hj0⟩).val) _)) i = _
      simp only [slotValue, integerValue_encodeValue]
      have heval := congrArg Subtype.val he0
      rw [heval]
      simp
    · intro j _ hne
      unfold encode
      split_ifs with hj
      · have hji : ((s.equivFin.symm ⟨j.val, hj⟩).val : Fin d) ≠ i := by
          intro h
          have heq : e.symm ⟨j.val, hj⟩ = ⟨i, hi⟩ := Subtype.ext h
          have hh : (⟨j.val, hj⟩ : Fin s.card) = e ⟨i, hi⟩ := by
            rw [← heq, e.apply_symm_apply]
          apply hne
          exact Fin.ext (congrArg (fun z : Fin s.card => z.val) hh)
        change (if (s.equivFin.symm ⟨j.val, hj⟩).val = i then _ else 0) = 0
        rw [if_neg hji]
      · rfl
    · simp
  · have hvi : v i = 0 := by
      by_contra h
      exact hi ((mem_integerSupport v i).mpr h)
    rw [hvi]
    apply Finset.sum_eq_zero
    intro j _
    unfold encode
    split_ifs with hj
    · have hji : ((s.equivFin.symm ⟨j.val, hj⟩).val : Fin d) ≠ i := by
        intro h
        exact hi (h ▸ (s.equivFin.symm ⟨j.val, hj⟩).property)
      change (if (s.equivFin.symm ⟨j.val, hj⟩).val = i then _ else 0) = 0
      rw [if_neg hji]
    · rfl

lemma slotValue_ne_zero {d U : ℕ}
    (entry : Option (Fin d × Fin (2 * U + 1))) (i : Fin d)
    (h : slotValue entry i ≠ 0) : ∃ a, entry = some (i, a) := by
  cases entry with
  | none => simp [slotValue] at h
  | some entry =>
    rcases entry with ⟨j, a⟩
    by_cases hij : j = i
    · subst j; exact ⟨a, rfl⟩
    · simp [slotValue, hij] at h

lemma integerValue_bounds {U : ℕ} (a : Fin (2 * U + 1)) :
    -(U : ℤ) ≤ integerValue a ∧ integerValue a ≤ U := by
  have ha := a.isLt
  unfold integerValue
  omega

theorem candidateValue_bounded {d U K : ℕ} (code : CompactCode d U K)
    (hinj : ∀ (j k : Fin K) (a b : Fin d × Fin (2 * U + 1)),
      code j = some a → code k = some b → a.1 = b.1 → j = k)
    (i : Fin d) : -(U : ℤ) ≤ candidateValue code i ∧ candidateValue code i ≤ U := by
  classical
  by_cases hex : ∃ (j : Fin K) (a : Fin (2 * U + 1)), code j = some (i, a)
  · rcases hex with ⟨j, a, hj⟩
    have heq : candidateValue code i = integerValue a := by
      unfold candidateValue
      rw [Finset.sum_eq_single j]
      · simp [hj, slotValue]
      · intro k _ hkj
        by_contra hk
        obtain ⟨b, hb⟩ := slotValue_ne_zero (code k) i hk
        exact hkj (hinj k j (i, b) (i, a) hb hj rfl)
      · simp
    rw [heq]
    exact integerValue_bounds a
  · have heq : candidateValue code i = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      by_contra hj
      obtain ⟨a, ha⟩ := slotValue_ne_zero (code j) i hj
      exact hex ⟨j, a, ha⟩
    rw [heq]
    omega

/-- A code's vector has at most K nonzero coordinates, even for a malformed
code with repeated coordinates. -/
theorem candidateValue_sparse {d U K : ℕ} (code : CompactCode d U K) :
    (SparseRecovery.integerSupport (candidateValue code)).card ≤ K := by
  classical
  let s := SparseRecovery.integerSupport (candidateValue code)
  have hslot (i : s) : ∃ j : Fin K, slotValue (code j) i.val ≠ 0 := by
    have hi : candidateValue code i.val ≠ 0 := (mem_integerSupport _ _).mp i.property
    obtain ⟨j, _, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hi
    exact ⟨j, hj⟩
  let loc : s → Fin K := fun i => Classical.choose (hslot i)
  have hloc (i : s) : slotValue (code (loc i)) i.val ≠ 0 := Classical.choose_spec (hslot i)
  have hinj : Function.Injective loc := by
    intro i j hij
    obtain ⟨a, ha⟩ := slotValue_ne_zero (code (loc i)) i.val (hloc i)
    obtain ⟨b, hb⟩ := slotValue_ne_zero (code (loc j)) j.val (hloc j)
    rw [hij] at ha
    have hpair := Option.some.inj (ha.symm.trans hb)
    exact Subtype.ext (congrArg Prod.fst hpair)
  have hc := Fintype.card_le_of_injective loc hinj
  simpa only [Fintype.card_coe, Fintype.card_fin] using hc

def weightedSlot {d U : ℕ} (w : ℤ → ℝ)
    (entry : Option (Fin d × Fin (2 * U + 1))) (i : Fin d) : ℝ :=
  match entry with
  | none => 0
  | some (j, a) => if j = i then w (integerValue a) else 0

lemma weight_coordinate {d U K : ℕ} (w : ℤ → ℝ) (hw : w 0 = 0)
    (code : CompactCode d U K)
    (hinj : ∀ (j k : Fin K) (a b : Fin d × Fin (2 * U + 1)),
      code j = some a → code k = some b → a.1 = b.1 → j = k) (i : Fin d) :
    w (candidateValue code i) = ∑ j, weightedSlot w (code j) i := by
  classical
  by_cases hex : ∃ (j : Fin K) (a : Fin (2 * U + 1)), code j = some (i, a)
  · rcases hex with ⟨j, a, hj⟩
    have heq : candidateValue code i = integerValue a := by
      unfold candidateValue
      rw [Finset.sum_eq_single j]
      · simp [hj, slotValue]
      · intro k _ hkj
        by_contra hk
        obtain ⟨b, hb⟩ := slotValue_ne_zero (code k) i hk
        exact hkj (hinj k j (i, b) (i, a) hb hj rfl)
      · simp
    rw [heq, Finset.sum_eq_single j]
    · simp [hj, weightedSlot]
    · intro k _ hkj
      cases hk : code k with
      | none => rfl
      | some entry =>
        rcases entry with ⟨l, b⟩
        have hli : l ≠ i := by
          intro he
          exact hkj (hinj k j (l, b) (i, a) hk hj he)
        simp [weightedSlot, hli]
    · simp
  · have heq : candidateValue code i = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      by_contra hj
      obtain ⟨a, ha⟩ := slotValue_ne_zero (code j) i hj
      exact hex ⟨j, a, ha⟩
    rw [heq, hw]
    symm
    apply Finset.sum_eq_zero
    intro j _
    cases hj : code j with
    | none => rfl
    | some entry =>
      rcases entry with ⟨l, a⟩
      have hli : l ≠ i := by
        intro he
        subst l
        exact hex ⟨j, a, hj⟩
      simp [weightedSlot, hli]

/-- Evaluating the recovered moment needs only the K compact slots, never a
dimension-sized reconstructed integer vector. -/
theorem moment_slots {d U K : ℕ} (w : ℤ → ℝ) (hw : w 0 = 0)
    (code : CompactCode d U K)
    (hinj : ∀ (j k : Fin K) (a b : Fin d × Fin (2 * U + 1)),
      code j = some a → code k = some b → a.1 = b.1 → j = k) :
    (∑ i, w (candidateValue code i)) =
      ∑ j, match code j with
        | none => 0
        | some (_, a) => w (integerValue a) := by
  classical
  simp_rw [weight_coordinate w hw code hinj]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  cases hj : code j with
  | none => simp [weightedSlot]
  | some entry =>
    rcases entry with ⟨i, a⟩
    simp [weightedSlot]

end Paper02.CompactCandidates
