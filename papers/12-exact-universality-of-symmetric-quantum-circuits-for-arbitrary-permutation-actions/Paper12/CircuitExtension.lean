import Paper12.CircuitAlgebra
import Paper12.Registers

noncomputable section
namespace Paper12
open Matrix Classical
open scoped Function
variable {J K : Type*} [Fintype J] [Fintype K]

def OneQubit.onLeft (g : OneQubit J) : OneQubit (J ⊕ K) :=
  ⟨Sum.inl g.wire, g.u, g.isUnitary⟩

def Threshold.onLeft (g : Threshold J) : Threshold (J ⊕ K) where
  head := Sum.inl g.head
  controls := g.controls.map Function.Embedding.inl
  threshold := g.threshold
  head_not := by simpa using g.head_not

def Gate.onLeft : Gate J → Gate (J ⊕ K)
  | .one g => .one g.onLeft
  | .thr g => .thr g.onLeft

def Gate.onLeftEmbedding : Gate J ↪ Gate (J ⊕ K) where
  toFun := Gate.onLeft
  inj' := by
    intro a b h
    cases a with
    | one a =>
      cases b with
      | thr b => cases h
      | one b =>
        have hh := Gate.one.inj h
        have hw : a.wire = b.wire := Sum.inl.inj (congrArg OneQubit.wire hh)
        have hu : a.u = b.u := congrArg (fun q : OneQubit (J ⊕ K) => q.u) hh
        congr 1
        cases a; cases b; simp_all
    | thr a =>
      cases b with
      | one b => cases h
      | thr b =>
        have hh := Gate.thr.inj h
        have hw : a.head = b.head := Sum.inl.inj (congrArg Threshold.head hh)
        have hc : a.controls = b.controls :=
          Finset.map_injective Function.Embedding.inl (congrArg Threshold.controls hh)
        have ht : a.threshold = b.threshold := congrArg (fun q : Threshold (J ⊕ K) => q.threshold) hh
        congr 1
        cases a; cases b; simp_all

theorem OneQubit.onLeft_unitary (g : OneQubit J) :
    (g.onLeft (K := K)).unitary = extendLeft g.unitary := by
  ext i j
  have hcond : (∀ z : J ⊕ K, z ≠ Sum.inl g.wire → i z = j z) ↔
      (∀ x : J, x ≠ g.wire → i (Sum.inl x) = j (Sum.inl x)) ∧
        i ∘ Sum.inr = j ∘ Sum.inr := by
    constructor
    · intro h
      refine ⟨fun x hx => h (Sum.inl x) (fun he => hx (Sum.inl.inj he)), ?_⟩
      funext x; exact h (Sum.inr x) (by simp)
    · rintro ⟨hL, hR⟩ z hz
      cases z with
      | inl x => exact hL x (fun he => hz (congrArg Sum.inl he))
      | inr x => exact congrFun hR x
  simp only [OneQubit.unitary, OneQubit.onLeft, extendLeft, registerTensor,
    Matrix.of_apply, Matrix.one_apply, Function.comp_apply]
  simp only [hcond]
  by_cases hL : ∀ x : J, x ≠ g.wire → i (Sum.inl x) = j (Sum.inl x)
  · by_cases hR : i ∘ Sum.inr = j ∘ Sum.inr <;> simp [hL, hR]
  · simp [hL]

theorem Threshold.onLeft_act (g : Threshold J) (b : Basis (J ⊕ K)) :
    (g.onLeft (K := K)).act b = Sum.elim (g.act (b ∘ Sum.inl)) (b ∘ Sum.inr) := by
  simp only [Threshold.act, Threshold.onLeft, Finset.sum_map, Function.Embedding.inl_apply,
    Function.comp_apply]
  by_cases ht : g.threshold ≤ ∑ x ∈ g.controls, (b (Sum.inl x) : ℕ)
  · simp only [if_pos ht]
    funext z
    cases z with
    | inl x =>
      by_cases hx : x = g.head
      · subst x; simp [Function.comp_def]
      · simp [Function.comp_def, hx]
    | inr x => simp
  · simp only [if_neg ht]
    funext z; cases z <;> rfl

theorem Threshold.onLeft_unitary (g : Threshold J) :
    (g.onLeft (K := K)).unitary = extendLeft g.unitary := by
  ext i j
  have hc : (g.onLeft (K := K)).act j = i ↔
      g.act (j ∘ Sum.inl) = i ∘ Sum.inl ∧ j ∘ Sum.inr = i ∘ Sum.inr := by
    rw [g.onLeft_act]
    constructor
    · intro h
      constructor
      · funext x; exact congrFun h (Sum.inl x)
      · funext x; exact congrFun h (Sum.inr x)
    · rintro ⟨hL, hR⟩
      funext z
      cases z with
      | inl x => exact congrFun hL x
      | inr x => exact congrFun hR x
  simp only [Threshold.unitary, Matrix.of_apply, extendLeft, registerTensor, Matrix.one_apply]
  simp only [hc]
  by_cases hL : g.act (j ∘ Sum.inl) = i ∘ Sum.inl
  · by_cases hR : j ∘ Sum.inr = i ∘ Sum.inr <;> simp [hL, hR, Ne.symm, eq_comm]
  · simp [hL]

theorem Gate.onLeft_unitary (g : Gate J) :
    (g.onLeft (K := K)).unitary = extendLeft g.unitary := by
  cases g with
  | one g => exact g.onLeft_unitary
  | thr g => exact g.onLeft_unitary

def Layer.onLeft (L : Layer J) : Layer (J ⊕ K) where
  gates := L.gates.map Gate.onLeftEmbedding
  commute := by
    intro a ha b hb
    obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp ha
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hb
    change (Gate.onLeft x).unitary * (Gate.onLeft y).unitary =
      (Gate.onLeft y).unitary * (Gate.onLeft x).unitary
    simp only [Gate.onLeft_unitary]
    exact (show Commute x.unitary y.unitary from L.commute x hx y hy).map
      (extendLeftHom (K := K))

theorem Layer.onLeft_unitary (L : Layer J) :
    (L.onLeft (K := K)).unitary = extendLeft L.unitary := by
  have hL := pairwiseCommute_to_set L.gates L.commute
  have hE := pairwiseCommute_to_set (L.onLeft (K := K)).gates L.onLeft.commute
  rw [Layer.unitary, dif_pos hE, Layer.unitary, dif_pos hL]
  have hx : (L.gates : Set (Gate J)).Pairwise
      (Commute on fun g => (g.onLeft (K := K)).unitary) := by
    intro a ha b hb _
    simp only [Gate.onLeft_unitary]
    exact (show Commute a.unitary b.unitary from L.commute a ha b hb).map
      (extendLeftHom (K := K))
  have hm : (L.onLeft (K := K)).gates.noncommProd Gate.unitary hE =
      L.gates.noncommProd (fun g => (g.onLeft (K := K)).unitary) hx := by
    simp only [Layer.onLeft, Finset.noncommProd, Finset.map_val, Multiset.map_map]
    rfl
  rw [hm, Finset.noncommProd_congr rfl (fun g _ => g.onLeft_unitary) hx]
  exact (Finset.map_noncommProd L.gates Gate.unitary hL (extendLeftHom (K := K))).symm

def Circuit.onLeft (C : Circuit J) : Circuit (J ⊕ K) := ⟨C.layers.map Layer.onLeft⟩

@[simp] theorem Circuit.onLeft_size (C : Circuit J) : (C.onLeft (K := K)).size = C.size := by
  simp [Circuit.onLeft, Circuit.size, Layer.onLeft, List.map_map, Function.comp_def]

theorem Circuit.onLeft_unitary (C : Circuit J) :
    (C.onLeft (K := K)).unitary = extendLeft C.unitary := by
  have h : ∀ ls : List (Layer J),
      (((⟨ls⟩ : Circuit J).onLeft (K := K)).unitary) = extendLeft (⟨ls⟩ : Circuit J).unitary := by
    intro ls
    induction ls with
    | nil => exact (extendLeftHom (K := K)).map_one.symm
    | cons L ls ih =>
      change (L.onLeft (K := K)).unitary * _ = extendLeft (L.unitary * _)
      simp only [Circuit.onLeft, Circuit.unitary] at ih
      rw [Layer.onLeft_unitary, ih]
      exact ((extendLeftHom (K := K)).map_mul _ _).symm
  exact h C.layers
end Paper12
