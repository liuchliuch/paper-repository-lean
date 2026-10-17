import Paper12.CNOT
import Paper12.OneHotComplete

noncomputable section
namespace Paper12
open Matrix Classical
open scoped Function
variable {X Q : Type*} [Fintype X] [Fintype Q]

def SectorSimulates (k : Basis Q) (A : Op (X ⊕ Q)) (B : Op X) : Prop :=
  ∀ ψ, applyOp A (registerVec ψ (eBasis k)) = registerVec (applyOp B ψ) (eBasis k)

theorem SectorSimulates.one (k : Basis Q) : SectorSimulates (X := X) k 1 1 := by
  intro ψ
  simp only [applyOp_one]

theorem SectorSimulates.mul {k : Basis Q} {A C : Op (X ⊕ Q)} {B D : Op X}
    (h : SectorSimulates k A B) (g : SectorSimulates k C D) :
    SectorSimulates k (A * C) (B * D) := by
  intro ψ
  rw [applyOp_mul, g, h, applyOp_mul]

theorem SectorSimulates.extendLeft (k : Basis Q) (A : Op X) :
    SectorSimulates k (extendLeft A) A := by
  intro ψ
  change applyOp (registerTensor A 1) _ = _
  rw [registerTensor_apply, applyOp_one]

theorem SectorSimulates.prod {ι : Type*} (s : Finset ι)
    (A : ι → Op (X ⊕ Q)) (B : ι → Op X)
    (hA : (s : Set ι).Pairwise (Commute on A))
    (hB : (s : Set ι).Pairwise (Commute on B)) (k : Basis Q)
    (h : ∀ i ∈ s, SectorSimulates k (A i) (B i)) :
    SectorSimulates k (s.noncommProd A hA) (s.noncommProd B hB) := by
  induction s using Finset.induction_on with
  | empty => simpa using SectorSimulates.one (X := X) k
  | @insert i s hi ih =>
    rw [Finset.noncommProd_insert_of_notMem _ _ _ _ hi,
      Finset.noncommProd_insert_of_notMem _ _ _ _ hi]
    exact (h i (Finset.mem_insert_self _ _)).mul
      (ih (fun a ha b hb hn => hA (Finset.mem_insert_of_mem ha) (Finset.mem_insert_of_mem hb) hn)
        (fun a ha b hb hn => hB (Finset.mem_insert_of_mem ha) (Finset.mem_insert_of_mem hb) hn)
        (fun a ha => h a (Finset.mem_insert_of_mem ha)))

def sectorLocal (q : Q) (a : Q × X) : X → QMat :=
  if a.1 = q then atWire a.2 (pmat .X) else 1

theorem sectorLocal_commute (q : Q) (a b : Q × X) :
    Commute (sectorLocal q a) (sectorLocal q b) := by
  unfold sectorLocal
  split_ifs
  · by_cases hh : a.2 = b.2
    · rw [hh]
    · exact atWire_commute hh _ _
  all_goals simp [Commute]

def sectorLocalPairwise (q : Q) (s : Finset (Q × X)) :
    (s : Set (Q × X)).Pairwise (Commute on sectorLocal q) :=
  fun a _ b _ _ => sectorLocal_commute q a b

theorem sectorLocal_prod (q : Q) (s : Finset (Q × X)) :
    s.noncommProd (sectorLocal q) (sectorLocalPairwise q s) =
      fun x => if (q, x) ∈ s then pmat .X else 1 := by
  induction s using Finset.induction_on with
  | empty => funext x; simp
  | @insert a s ha ih =>
    rw [Finset.noncommProd_insert_of_notMem _ _ _ _ ha, ih]
    funext x
    by_cases hq : a.1 = q
    · by_cases hx : x = a.2
      · subst x
        have hm : (q, a.2) ∉ s := by simpa [← hq] using ha
        have he : (q, a.2) = a := Prod.ext hq.symm rfl
        simp [sectorLocal, hq, atWire, hm, he, ha]
      · have hn : (q, x) ≠ a := fun h => hx (congrArg Prod.snd h)
        simp [sectorLocal, hq, atWire, hx, hn]
    · have hn : (q, x) ≠ a := fun h => hq (congrArg Prod.fst h).symm
      simp [sectorLocal, hq, hn]

theorem cnot_sector (q r : Q) (x : X) :
    SectorSimulates (oneHot q) (cnotThreshold r x).unitary
      (tensorOp (sectorLocal q (r, x))) := by
  intro ψ
  funext b
  rw [Threshold.apply_eq]
  have hR : ((cnotThreshold r x).act b ∘ Sum.inr) = b ∘ Sum.inr := by
    funext y
    exact cnot_control r y x b
  by_cases hk : b ∘ Sum.inr = oneHot q
  · have hc : b (Sum.inr r) = if r = q then 1 else 0 := by
      have hh := congrFun hk r
      simpa only [Function.comp_apply, oneHot] using hh
    by_cases hr : r = q
    · subst r
      have hL : ((cnotThreshold q x).act b ∘ Sum.inl) =
          Function.update (b ∘ Sum.inl) x (1 - b (Sum.inl x)) := by
        funext y
        simp only [cnot_act, hc, ite_true, Function.comp_apply]
        by_cases hy : y = x <;> simp [hy]
      have ht : tensorOp (sectorLocal q (q, x)) =
          (Gate.one (⟨x, pmat .X, pmat_unitary .X⟩ : OneQubit X)).unitary := by
        simp only [sectorLocal, ite_true]
        exact tensor_atWire (⟨x, pmat .X, pmat_unitary .X⟩ : OneQubit X)
      rw [ht]
      simp only [registerVec, hR, hL, eBasis, hk, ite_true, mul_one,
        oneQubitX_apply]
      rfl
    · have ht : tensorOp (sectorLocal q (r, x)) = 1 := by
        simp [sectorLocal, hr]
      have hc0 : b (Sum.inr r) ≠ 1 := by rw [hc, if_neg hr]; decide
      simp only [cnot_act, if_neg hc0, ht, applyOp_one]
  · simp only [registerVec, hR, eBasis, if_neg hk, mul_zero]

def incidenceSet (w : Q → PWord X) (s : PSym) : Finset (Q × X) :=
  Finset.univ.filter (fun a => w a.1 a.2 = s)

def cnotEmbedding : (Q × X) ↪ Gate (X ⊕ Q) where
  toFun a := .thr (cnotThreshold a.1 a.2)
  inj' := by
    intro a b h
    have ht := Gate.thr.inj h
    have hx := congrArg Threshold.head ht
    have hq := congrArg Threshold.controls ht
    simp only [cnotThreshold, Sum.inl.injEq] at hx
    simp only [cnotThreshold, Finset.singleton_inj, Sum.inr.injEq] at hq
    exact Prod.ext hq hx

def incidenceLayer (w : Q → PWord X) (s : PSym) : Layer (X ⊕ Q) where
  gates := (incidenceSet w s).map cnotEmbedding
  commute := by
    intro a ha b hb
    obtain ⟨u, _, rfl⟩ := Finset.mem_map.mp ha
    obtain ⟨v, _, rfl⟩ := Finset.mem_map.mp hb
    exact cnot_unitary_commute u.1 v.1 u.2 v.2

def incidenceCircuit (w : Q → PWord X) (s : PSym) : Circuit (X ⊕ Q) :=
  ⟨[incidenceLayer w s]⟩

theorem incidenceCircuit_size (w : Q → PWord X) (s : PSym) :
    (incidenceCircuit w s).size ≤ Fintype.card Q * Fintype.card X := by
  simp only [incidenceCircuit, Circuit.size, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero, incidenceLayer, Finset.card_map]
  exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (by simp)

theorem incidenceCircuit_sector (w : Q → PWord X) (s : PSym) (q : Q) :
    SectorSimulates (oneHot q) (incidenceCircuit w s).unitary
      (tensorOp (fun x => if w q x = s then pmat .X else 1)) := by
  let t := incidenceSet w s
  let A : Q × X → Op (X ⊕ Q) := fun a => (cnotThreshold a.1 a.2).unitary
  let B : Q × X → Op X := fun a => tensorOp (sectorLocal q a)
  have hA : (t : Set (Q × X)).Pairwise (Commute on A) :=
    fun a _ b _ _ => cnot_unitary_commute a.1 b.1 a.2 b.2
  have hB : (t : Set (Q × X)).Pairwise (Commute on B) :=
    fun a _ b _ _ => (sectorLocal_commute q a b).map tensorHom
  have hfull : (incidenceCircuit w s).unitary = t.noncommProd A hA := by
    simp only [incidenceCircuit, Circuit.unitary, List.map_cons, List.map_nil,
      List.foldr_cons, List.foldr_nil, mul_one, Layer.unitary]
    rw [dif_pos (pairwiseCommute_to_set _ (incidenceLayer w s).commute)]
    simp only [incidenceLayer, Finset.noncommProd, Finset.map_val, Multiset.map_map]
    rfl
  have hsmall : t.noncommProd B hB = tensorOp (fun x => if w q x = s then pmat .X else 1) := by
    change t.noncommProd (fun a => tensorHom (sectorLocal q a)) _ = _
    rw [← Finset.map_noncommProd t (sectorLocal q) (sectorLocalPairwise q t) tensorHom,
      sectorLocal_prod]
    simp only [t, incidenceSet, Finset.mem_filter, Finset.mem_univ, true_and]
    rfl
  rw [hfull, ← hsmall]
  exact SectorSimulates.prod t A B hA hB (oneHot q) (fun a _ => cnot_sector q a.1 a.2)
end Paper12
