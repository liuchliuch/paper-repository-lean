import Paper20.DiagramHooks

namespace Paper20.HookBeta
open Finset
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

/-- The usual strictly decreasing beta numbers of an actual Young diagram. -/
def beta (μ : YoungDiagram) (i : ℕ) : ℕ := μ.rowLen i+μ.colLen 0-1-i

def rowHooks (μ : YoungDiagram) (i : ℕ) : Finset ℕ :=
  (range (μ.rowLen i)).image (fun j => diagramHook μ (i,j))

def rowGaps (μ : YoungDiagram) (i : ℕ) : Finset ℕ :=
  (Ico (i+1) (μ.colLen 0)).image (fun l => beta μ i-beta μ l)

lemma row_positive (μ : YoungDiagram) (i : ℕ) (hi : i < μ.colLen 0) : 0 < μ.rowLen i := by
  exact YoungDiagram.mem_iff_lt_rowLen.mp (YoungDiagram.mem_iff_lt_colLen.mpr hi)

lemma beta_strict (μ : YoungDiagram) (i l : ℕ) (hil : i < l) (hl : l < μ.colLen 0) :
    beta μ l < beta μ i := by
  have hr := μ.rowLen_anti i l hil.le
  have hp := row_positive μ l hl
  dsimp only [beta]
  omega

lemma hook_positive (μ : YoungDiagram) (i j : ℕ) (hj : j < μ.rowLen i) :
    0 < diagramHook μ (i,j) := by
  have hc := YoungDiagram.mem_iff_lt_colLen.mp (YoungDiagram.mem_iff_lt_rowLen.mpr hj)
  dsimp only [diagramHook]
  omega

lemma hook_le_beta (μ : YoungDiagram) (i j : ℕ) (hj : j < μ.rowLen i) :
    diagramHook μ (i,j) ≤ beta μ i := by
  have hc := YoungDiagram.mem_iff_lt_colLen.mp (YoungDiagram.mem_iff_lt_rowLen.mpr hj)
  have hm := μ.colLen_anti 0 j (Nat.zero_le _)
  dsimp only [diagramHook,beta]
  omega

lemma hook_strict (μ : YoungDiagram) (i j k : ℕ) (hjk : j < k) (hk : k < μ.rowLen i) :
    diagramHook μ (i,k) < diagramHook μ (i,j) := by
  have hc := YoungDiagram.mem_iff_lt_colLen.mp (YoungDiagram.mem_iff_lt_rowLen.mpr hk)
  have hm := μ.colLen_anti j k hjk.le
  dsimp only [diagramHook]
  omega

lemma hook_injOn (μ : YoungDiagram) (i : ℕ) :
    Set.InjOn (fun j => diagramHook μ (i,j)) (range (μ.rowLen i)) := by
  intro j hj k hk he
  change diagramHook μ (i,j)=diagramHook μ (i,k) at he
  have hj' := mem_range.mp hj
  have hk' := mem_range.mp hk
  rcases lt_trichotomy j k with h | h | h
  · have := hook_strict μ i j k h hk'; omega
  · exact h
  · have := hook_strict μ i k j h hj'; omega

lemma gap_injOn (μ : YoungDiagram) (i : ℕ) :
    Set.InjOn (fun l => beta μ i-beta μ l) (Ico (i+1) (μ.colLen 0)) := by
  intro l hl t ht he
  change beta μ i-beta μ l=beta μ i-beta μ t at he
  obtain ⟨hil,hlm⟩ := mem_Ico.mp hl
  obtain ⟨hit,htm⟩ := mem_Ico.mp ht
  have hli := beta_strict μ i l (by omega) hlm
  have hti := beta_strict μ i t (by omega) htm
  rcases lt_trichotomy l t with h | h | h
  · have := beta_strict μ l t h htm; omega
  · exact h
  · have := beta_strict μ t l h hlm; omega

/-- A hook in row i can never equal the missing beta difference for a
lower row. The two cases are exactly whether that lower row reaches the
hook's column. -/
lemma hook_ne_gap (μ : YoungDiagram) (i j l : ℕ) (hj : j < μ.rowLen i)
    (hil : i < l) (hl : l < μ.colLen 0) :
    diagramHook μ (i,j) ≠ beta μ i-beta μ l := by
  have hci := YoungDiagram.mem_iff_lt_colLen.mp (YoungDiagram.mem_iff_lt_rowLen.mpr hj)
  have hri := row_positive μ i (by omega)
  have hrl := row_positive μ l hl
  have hrows := μ.rowLen_anti i l hil.le
  have hb := beta_strict μ i l hil hl
  have hm := μ.colLen_anti 0 j (Nat.zero_le _)
  by_cases hcol : j < μ.rowLen l
  · have hcl := YoungDiagram.mem_iff_lt_colLen.mp (YoungDiagram.mem_iff_lt_rowLen.mpr hcol)
    dsimp only [diagramHook,beta] at *
    omega
  · have hcl : μ.colLen j ≤ l := by
      by_contra hn
      exact hcol (YoungDiagram.mem_iff_lt_rowLen.mp
        (YoungDiagram.mem_iff_lt_colLen.mpr (by omega)))
    dsimp only [diagramHook,beta] at *
    omega

lemma row_disjoint (μ : YoungDiagram) (i : ℕ) : Disjoint (rowHooks μ i) (rowGaps μ i) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  obtain ⟨j,hj,rfl⟩ := mem_image.mp hx
  obtain ⟨l,hl,he⟩ := mem_image.mp hy
  exact hook_ne_gap μ i j l (mem_range.mp hj) (by have := (mem_Ico.mp hl).1; omega)
    (mem_Ico.mp hl).2 he.symm

lemma rowHooks_card (μ : YoungDiagram) (i : ℕ) : (rowHooks μ i).card=μ.rowLen i := by
  rw [rowHooks,Finset.card_image_of_injOn (hook_injOn μ i),card_range]

lemma rowGaps_card (μ : YoungDiagram) (i : ℕ) :
    (rowGaps μ i).card=μ.colLen 0-(i+1) := by
  rw [rowGaps,Finset.card_image_of_injOn (gap_injOn μ i),Nat.card_Ico]

/-- The actual row hooks together with precisely the missing beta-number
differences partition the integer interval 1,...,beta_i. This is the exact
combinatorial hook-product foundation for the Vandermonde formula. -/
theorem row_partition (μ : YoungDiagram) (i : ℕ) (hi : i < μ.colLen 0) :
    rowHooks μ i ∪ rowGaps μ i=Icc 1 (beta μ i) := by
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    rcases mem_union.mp hx with hx | hx
    · obtain ⟨j,hj,rfl⟩ := mem_image.mp hx
      exact mem_Icc.mpr ⟨hook_positive μ i j (mem_range.mp hj),
        hook_le_beta μ i j (mem_range.mp hj)⟩
    · obtain ⟨l,hl,rfl⟩ := mem_image.mp hx
      have hb := beta_strict μ i l (by have := (mem_Ico.mp hl).1; omega) (mem_Ico.mp hl).2
      exact mem_Icc.mpr ⟨by omega,Nat.sub_le ..⟩
  · rw [Finset.card_union_of_disjoint (row_disjoint μ i),rowHooks_card,rowGaps_card,Nat.card_Icc]
    have hp := row_positive μ i hi
    dsimp only [beta]
    omega

/-- Row-wise exact hook factorization over the naturals, with no
hook-length divisibility or dimension formula assumed. -/
theorem row_product (μ : YoungDiagram) (i : ℕ) (hi : i < μ.colLen 0) :
    (∏ j ∈ range (μ.rowLen i), diagramHook μ (i,j))*
      (∏ l ∈ Ico (i+1) (μ.colLen 0), (beta μ i-beta μ l))=
        ∏ a ∈ Icc 1 (beta μ i), a := by
  rw [← row_partition μ i hi,Finset.prod_union (row_disjoint μ i)]
  congr 1
  · unfold rowHooks
    rw [Finset.prod_image (hook_injOn μ i)]
  · unfold rowGaps
    rw [Finset.prod_image (gap_injOn μ i)]

end
end Paper20.HookBeta
