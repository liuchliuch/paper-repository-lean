import Paper15.SymmetryTransport

/-! # Product-cell bisection along every edge

This extends the certificate geometry to the arbitrary source/edge splits
recorded in Appendix A's complete certificate forest.
-/
noncomputable section
namespace Paper15
open Finset BigOperators

@[ext] theorem Simplex2.ext {q r : Simplex2} (h : ∀ i, q i = r i) : q = r := by
  cases q with
  | mk q hq sq =>
    cases r with
    | mk r hr sr =>
      have he : q = r := funext h
      subst r
      rfl

lemma Simplex2.mid_comm (q r : Simplex2) : q.mid r = r.mid q := by
  apply Simplex2.ext
  intro i
  simp [Simplex2.mid, add_comm]

/-- Membership expressed without privileging any vertex ordering. -/
def InCell (q : Fin 3 → Simplex2) (v : Simplex2) : Prop :=
  ∃ α : Fin 3 → ℝ, (∀ i, 0 ≤ α i) ∧ ∑ i, α i = 1 ∧
    ∀ x, v x = ∑ i, α i * q i x

lemma inCell_iff_triangle (q : Fin 3 → Simplex2) (v : Simplex2) :
    InCell q v ↔ inTriangle (q 0) (q 1) (q 2) v := by
  simp only [InCell, inTriangle, Fin.sum_univ_three]

lemma InCell.reindex {q : Fin 3 → Simplex2} {v : Simplex2}
    (h : InCell q v) (σ : Equiv.Perm (Fin 3)) : InCell (fun i => q (σ i)) v := by
  obtain ⟨α, hα0, hα1, hαv⟩ := h
  refine ⟨fun i => α (σ i), fun i => hα0 _, (Equiv.sum_comp σ α).trans hα1, ?_⟩
  intro x
  rw [Equiv.sum_comp σ (fun i => α i * q i x)]
  exact hαv x

lemma inCell_reindex_iff (q : Fin 3 → Simplex2) (v : Simplex2)
    (σ : Equiv.Perm (Fin 3)) : InCell (fun i => q (σ i)) v ↔ InCell q v := by
  constructor
  · intro h
    simpa only [Equiv.apply_symm_apply] using h.reindex σ.symm
  · exact fun h => h.reindex σ

/-- Replace one endpoint of an arbitrary edge by its midpoint. -/
def bisectVertices (q : Fin 3 → Simplex2) (i j : Fin 3) : Fin 3 → Simplex2 :=
  Function.update q i ((q i).mid (q j))

/-- Every arbitrary-edge bisection covers its parent, including the boundary. -/
theorem inCell_bisect {q : Fin 3 → Simplex2} {v : Simplex2} (h : InCell q v)
    (i j : Fin 3) (hij : i ≠ j) :
    InCell (bisectVertices q i j) v ∨ InCell (bisectVertices q j i) v := by
  have hbij : Function.Bijective (triple i j (-i-j)) := by
    fin_cases i <;> fin_cases j <;> try contradiction
    all_goals decide
  let σ : Equiv.Perm (Fin 3) := Equiv.ofBijective _ hbij
  have h0 : σ 0 = i := rfl
  have h1 : σ 1 = j := rfl
  have h2i : σ 2 ≠ i := by
    rw [← h0]
    exact fun he => (by decide : (2 : Fin 3) ≠ 0) (σ.injective he)
  have h2j : σ 2 ≠ j := by
    rw [← h1]
    exact fun he => (by decide : (2 : Fin 3) ≠ 1) (σ.injective he)
  have hl : (fun k => bisectVertices q i j (σ k)) =
      triple ((q i).mid (q j)) (q j) (q (σ 2)) := by
    funext k
    fin_cases k <;> simp [bisectVertices, Function.update, h0, h1, hij, hij.symm, h2i]
  have hr : (fun k => bisectVertices q j i (σ k)) =
      triple (q i) ((q i).mid (q j)) (q (σ 2)) := by
    funext k
    fin_cases k <;> simp [bisectVertices, Function.update, h0, h1, hij, hij.symm, h2j, Simplex2.mid_comm]
  have hparent : inTriangle (q i) (q j) (q (σ 2)) v := by
    have hh := (inCell_iff_triangle _ _).mp (h.reindex σ)
    simpa only [h0, h1] using hh
  obtain hleft | hright := bisect_covers _ _ _ _ hparent
  · left
    apply (inCell_reindex_iff _ _ σ).mp
    rw [hl]
    exact (inCell_iff_triangle _ _).mpr hleft
  · right
    apply (inCell_reindex_iff _ _ σ).mp
    rw [hr]
    exact (inCell_iff_triangle _ _).mpr hright

abbrev ProductCell := Fin 3 → Fin 3 → Simplex2

def cellChild (c : ProductCell) (axis i j : Fin 3) : ProductCell :=
  Function.update c axis (bisectVertices (c axis) i j)

def InProductCell (c : ProductCell) (q : Fin 3 → Simplex2) : Prop :=
  ∀ a, InCell (c a) (q a)

lemma inProductCell_bisect {c : ProductCell} {q : Fin 3 → Simplex2}
    (h : InProductCell c q) (a i j : Fin 3) (hij : i ≠ j) :
    InProductCell (cellChild c a i j) q ∨ InProductCell (cellChild c a j i) q := by
  obtain hl | hr := inCell_bisect (h a) i j hij
  · left
    intro b
    by_cases hb : b = a
    · subst b; simpa [cellChild] using hl
    · simpa only [cellChild, Function.update_of_ne hb] using h b
  · right
    intro b
    by_cases hb : b = a
    · subst b; simpa [cellChild] using hr
    · simpa only [cellChild, Function.update_of_ne hb] using h b

/-- Certificate geometry used by the actual arbitrary-edge integer checker. -/
inductive FullCertTree (T : DetTriangle) : ProductCell → Type where
  | leaf {c : ProductCell} (lam mu : ℝ)
      (hc : ∀ i j k, certForm T lam mu (c 0 i) (c 1 j) (c 2 k) ≤ 0) :
      FullCertTree T c
  | split {c : ProductCell} (axis i j : Fin 3) (hij : i ≠ j)
      (left : FullCertTree T (cellChild c axis i j))
      (right : FullCertTree T (cellChild c axis j i)) : FullCertTree T c

/-- Soundness includes all nine possible source/edge choices at every node. -/
theorem fullCertTree_sound {T : DetTriangle} {c : ProductCell} (t : FullCertTree T c) :
    ∀ q : Fin 3 → Simplex2, InProductCell c q → GapHoldsAt T (q 0) (q 1) (q 2) := by
  induction t with
  | leaf lam mu hc =>
    intro q hq
    exact gapHoldsAt_of_certForm T lam mu _ _ _ hc _ _ _
      ((inCell_iff_triangle _ _).mp (hq 0))
      ((inCell_iff_triangle _ _).mp (hq 1))
      ((inCell_iff_triangle _ _).mp (hq 2))
  | split a i j hij left right ihl ihr =>
    intro q hq
    obtain hl | hr := inProductCell_bisect hq a i j hij
    · exact ihl q hl
    · exact ihr q hr

def fullSourceCell : ProductCell := fun _ i => Simplex2.dirac i

theorem gapHolds_of_fullCertTree {T : DetTriangle} (t : FullCertTree T fullSourceCell) :
    GapHolds T := by
  intro qx qy qz h1 h3
  apply fullCertTree_sound t (triple qx qy qz) _ h1 h3
  intro a
  exact (inCell_iff_triangle _ _).mpr (mem_std_triangle _)

end Paper15
