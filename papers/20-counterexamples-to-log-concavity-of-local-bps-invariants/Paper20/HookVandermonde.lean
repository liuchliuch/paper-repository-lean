import Paper20.HookBeta

namespace Paper20.HookBeta
open Finset
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

lemma interval_product_factorial (b : ℕ) : (∏ a ∈ Icc 1 b, a)=b.factorial := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [Finset.prod_Icc_succ_top (by omega : 1 ≤ b+1),ih,Nat.factorial_succ]
    exact Nat.mul_comm ..

lemma cells_by_rows (μ : YoungDiagram) :
    μ.cells=(range (μ.colLen 0)).biUnion
      (fun i => (range (μ.rowLen i)).image (fun j => (i,j))) := by
  ext c
  rcases c with ⟨i,j⟩
  constructor
  · intro hc
    have hj : j < μ.rowLen i := YoungDiagram.mem_iff_lt_rowLen.mp hc
    have hi := YoungDiagram.mem_iff_lt_colLen.mp hc
    have hm := μ.colLen_anti 0 j (Nat.zero_le _)
    exact mem_biUnion.mpr ⟨i,mem_range.mpr (by omega),mem_image.mpr ⟨j,mem_range.mpr hj,rfl⟩⟩
  · intro hc
    obtain ⟨i',hi',hc⟩ := mem_biUnion.mp hc
    obtain ⟨j',hj',he⟩ := mem_image.mp hc
    cases he
    exact YoungDiagram.mem_iff_lt_rowLen.mpr (mem_range.mp hj')

lemma row_images_disjoint (μ : YoungDiagram) :
    Set.PairwiseDisjoint (↑(range (μ.colLen 0)) : Set ℕ)
      (fun i => (range (μ.rowLen i)).image (fun j => (i,j))) := by
  intro i hi l hl hil
  apply Finset.disjoint_left.mpr
  intro c hc hd
  obtain ⟨j,hj,he⟩ := mem_image.mp hc
  obtain ⟨k,hk,hf⟩ := mem_image.mp hd
  exact hil ((congrArg Prod.fst he).trans (congrArg Prod.fst hf).symm)

lemma diagram_hook_product (μ : YoungDiagram) :
    (∏ c ∈ μ.cells, diagramHook μ c)=
      ∏ i ∈ range (μ.colLen 0), ∏ j ∈ range (μ.rowLen i), diagramHook μ (i,j) := by
  rw [cells_by_rows,Finset.prod_biUnion (row_images_disjoint μ)]
  apply prod_congr rfl
  intro i hi
  rw [Finset.prod_image]
  intro j hj k hk he
  exact congrArg Prod.snd he

/-- The full exact beta-number Vandermonde factorization of actual
Young-diagram hook lengths, proved by the row complement bijections. -/
theorem diagram_hook_vandermonde (μ : YoungDiagram) :
    (∏ c ∈ μ.cells, diagramHook μ c)*
      (∏ i ∈ range (μ.colLen 0), ∏ l ∈ Ico (i+1) (μ.colLen 0), (beta μ i-beta μ l))=
        ∏ i ∈ range (μ.colLen 0), (beta μ i).factorial := by
  rw [diagram_hook_product,← Finset.prod_mul_distrib]
  apply prod_congr rfl
  intro i hi
  rw [row_product μ i (mem_range.mp hi),interval_product_factorial]

lemma actual_hook_product {n : ℕ} (p : Part n) :
    (hooksOf p.parts).prod=∏ c ∈ p.diagram.cells, diagramHook p.diagram c := by
  rw [Part.hooks_eq_diagram,← List.prod_toFinset _ (boxesOf_nodup p.parts),boxesOf_toFinset]
  rfl

/-- The executable hook list satisfies the genuine hook-product formula
in beta numbers for every positive weakly decreasing partition. -/
theorem actual_hook_vandermonde {n : ℕ} (p : Part n) :
    (hooksOf p.parts).prod*
      (∏ i ∈ range p.parts.length, ∏ l ∈ Ico (i+1) p.parts.length,
        (beta p.diagram i-beta p.diagram l))=
      ∏ i ∈ range p.parts.length, (beta p.diagram i).factorial := by
  have hm : p.diagram.colLen 0=p.parts.length := by
    simpa only [Part.diagram_rowLens] using (YoungDiagram.length_rowLens (μ:=p.diagram)).symm
  simpa only [hm,actual_hook_product] using diagram_hook_vandermonde p.diagram

end
end Paper20.HookBeta
