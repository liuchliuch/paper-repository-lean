import Paper12.CircuitAlgebra

noncomputable section
namespace Paper12
open Matrix Classical
open scoped Function
variable {J K T : Type*} [Fintype J] [Fintype K] [Fintype T]

def basisRewire (e : J ≃ K) : Basis K ≃ Basis J where
  toFun b := b ∘ e
  invFun b := b ∘ e.symm
  left_inv b := by funext x; simp
  right_inv b := by funext x; simp

def rewireOp (e : J ≃ K) (A : Op J) : Op K := fun i j => A (i ∘ e) (j ∘ e)

def rewireHom (e : J ≃ K) : Op J →* Op K where
  toFun := rewireOp e
  map_one' := by
    ext i j
    simp only [rewireOp, Matrix.one_apply]
    have h : i ∘ e = j ∘ e ↔ i = j := (basisRewire e).injective.eq_iff
    simp only [h]
  map_mul' A B := by
    ext i j
    simp only [rewireOp, Matrix.mul_apply]
    exact (Equiv.sum_comp (basisRewire e) (fun b => A (i ∘ e) b * B b (j ∘ e))).symm

theorem OneQubit.rewire_unitary (e : J ≃ K) (g : OneQubit J) :
    (g.map e).unitary = rewireOp e g.unitary := by
  ext i j
  have hc : (∀ y : K, y ≠ e g.wire → i y = j y) ↔
      (∀ x : J, x ≠ g.wire → i (e x) = j (e x)) := by
    constructor
    · intro h x hx; exact h (e x) (fun he => hx (e.injective he))
    · intro h y hy
      obtain ⟨x, rfl⟩ := e.surjective y
      exact h x (fun he => hy (congrArg e he))
  simp only [OneQubit.unitary, OneQubit.map, rewireOp, Matrix.of_apply, Function.comp_apply]
  simp only [hc]

theorem Threshold.rewire_act (e : J ≃ K) (g : Threshold J) (b : Basis K) :
    ((g.map e).act b) ∘ e = g.act (b ∘ e) := by
  simp only [Threshold.act, Threshold.map, Finset.sum_map, Function.comp_apply,
    Equiv.toEmbedding_apply]
  by_cases ht : g.threshold ≤ ∑ x ∈ g.controls, (b (e x) : ℕ)
  · simp only [if_pos ht]
    funext x
    by_cases hx : x = g.head
    · subst x; simp
    · have he : e x ≠ e g.head := fun h => hx (e.injective h)
      simp [Function.comp_def, hx, he]
  · simp [ht]

theorem Threshold.rewire_unitary (e : J ≃ K) (g : Threshold J) :
    (g.map e).unitary = rewireOp e g.unitary := by
  ext i j
  have hc : (g.map e).act j = i ↔ g.act (j ∘ e) = i ∘ e := by
    rw [← g.rewire_act e j]
    exact (basisRewire e).injective.eq_iff.symm
  simp only [Threshold.unitary, rewireOp, Matrix.of_apply]
  simp only [hc]

theorem Gate.rewire_unitary (e : J ≃ K) (g : Gate J) :
    (Gate.map e g).unitary = rewireOp e g.unitary := by
  cases g with
  | one g => exact g.rewire_unitary e
  | thr g => exact g.rewire_unitary e

theorem Gate.map_trans (e : J ≃ K) (f : K ≃ T) (g : Gate J) :
    Gate.map f (Gate.map e g) = Gate.map (e.trans f) g := by
  cases g with
  | one g => rfl
  | thr g =>
    simp only [Gate.map, Threshold.map, Finset.map_map]
    congr 2

def Layer.rewire (e : J ≃ K) (L : Layer J) : Layer K where
  gates := L.gates.map (Gate.mapEmb e)
  commute := by
    intro a ha b hb
    obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp ha
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hb
    change (Gate.map e x).unitary * (Gate.map e y).unitary =
      (Gate.map e y).unitary * (Gate.map e x).unitary
    simp only [Gate.rewire_unitary]
    exact (show Commute x.unitary y.unitary from L.commute x hx y hy).map (rewireHom e)

theorem Layer.rewire_unitary (e : J ≃ K) (L : Layer J) :
    (L.rewire e).unitary = rewireOp e L.unitary := by
  have hL := pairwiseCommute_to_set L.gates L.commute
  have hE := pairwiseCommute_to_set (L.rewire e).gates (L.rewire e).commute
  rw [Layer.unitary, dif_pos hE, Layer.unitary, dif_pos hL]
  have hx : (L.gates : Set (Gate J)).Pairwise
      (Commute on fun g => (Gate.map e g).unitary) := by
    intro a ha b hb _
    simp only [Gate.rewire_unitary]
    exact (show Commute a.unitary b.unitary from L.commute a ha b hb).map (rewireHom e)
  have hm : (L.rewire e).gates.noncommProd Gate.unitary hE =
      L.gates.noncommProd (fun g => (Gate.map e g).unitary) hx := by
    simp only [Layer.rewire, Finset.noncommProd, Finset.map_val, Multiset.map_map]
    rfl
  rw [hm, Finset.noncommProd_congr rfl (fun g _ => Gate.rewire_unitary e g) hx]
  exact (Finset.map_noncommProd L.gates Gate.unitary hL (rewireHom e)).symm

theorem Layer.rewire_trans (e : J ≃ K) (f : K ≃ T) (L : Layer J) :
    (L.rewire e).rewire f = L.rewire (e.trans f) := by
  apply Layer.ext
  simp only [Layer.rewire, Finset.map_map]
  congr 1
  apply Function.Embedding.ext
  intro g
  exact Gate.map_trans e f g

def Circuit.rewire (e : J ≃ K) (C : Circuit J) : Circuit K := ⟨C.layers.map (Layer.rewire e)⟩

@[simp] theorem Circuit.rewire_size (e : J ≃ K) (C : Circuit J) :
    (C.rewire e).size = C.size := by
  simp [Circuit.rewire, Circuit.size, Layer.rewire, List.map_map, Function.comp_def]

theorem Circuit.rewire_unitary (e : J ≃ K) (C : Circuit J) :
    (C.rewire e).unitary = rewireOp e C.unitary := by
  have h : ∀ ls : List (Layer J),
      (Circuit.rewire e (⟨ls⟩ : Circuit J)).unitary = rewireOp e (⟨ls⟩ : Circuit J).unitary := by
    intro ls
    induction ls with
    | nil => exact (rewireHom e).map_one.symm
    | cons L ls ih =>
      change (L.rewire e).unitary * _ = rewireOp e (L.unitary * _)
      simp only [Circuit.rewire, Circuit.unitary] at ih
      rw [Layer.rewire_unitary, ih]
      exact ((rewireHom e).map_mul _ _).symm
  exact h C.layers

theorem Circuit.preserved_rewire (e : J ≃ K) {h : J ≃ J} {f : K ≃ K}
    {C : Circuit J} (hC : C.Preserved h) (he : ∀ x, f (e x) = e (h x)) :
    (C.rewire e).Preserved f := by
  intro L hL
  obtain ⟨M, hM, rfl⟩ := List.mem_map.mp hL
  change (M.rewire e).rewire f = M.rewire e
  rw [Layer.rewire_trans]
  have heq : e.trans f = h.trans e := Equiv.ext he
  rw [heq, ← Layer.rewire_trans]
  change (Layer.map h M).rewire e = M.rewire e
  rw [hC M hM]
end Paper12
