import Paper20.TableauMurphy
import Paper20.PartitionContent

namespace Paper20.Seminormal
open Paper20.YoungShapes Finset
noncomputable section
set_option maxHeartbeats 5000000
set_option maxRecDepth 10000

/-- The first label in every actual standard filling occupies (0,0). -/
theorem filling_first_cell {n : ℕ} {μ : Shape n} (t : StandardFilling μ) (hn : 0<n) :
    (t.val ⟨0,hn⟩).val=(0,0) := by
  let c := t.val ⟨0,hn⟩
  have hm : (0,0) ∈ μ.val :=
    μ.val.isLowerSet (show (0,0)≤c.val from ⟨Nat.zero_le _,Nat.zero_le _⟩) c.property
  by_contra he
  have hne : (⟨(0,0),hm⟩:Cells μ.val)≠c := by
    intro h
    exact he (congrArg Subtype.val h).symm
  have hlt : (⟨(0,0),hm⟩:Cells μ.val) < c :=
    lt_of_le_of_ne ⟨Nat.zero_le _,Nat.zero_le _⟩ hne
  have hi := t.property hlt
  change t.val.symm ⟨(0,0),hm⟩ < t.val.symm (t.val ⟨0,hn⟩) at hi
  rw [Equiv.symm_apply_apply] at hi
  have hh : (t.val.symm ⟨(0,0),hm⟩).val < 0 := hi
  omega

theorem filling_first_content {n : ℕ} {μ : Shape n} (t : StandardFilling μ) (hn : 0<n) :
    fillingContent t ⟨0,hn⟩=0 := by
  unfold fillingContent
  rw [filling_first_cell t hn]
  norm_num [cellContent]

/-- The sum of all actual tableau-cell contents is the original
partition-program content, independent of the order of its labels. -/
theorem filling_content_sum {n : ℕ} {μ : Shape n} (t : StandardFilling μ) :
    (∑ i : Fin n, fillingContent t i)=Paper20.contentOf μ.val.rowLens := by
  have hcells : YoungDiagram.cellsOfRowLens μ.val.rowLens=μ.val.cells :=
    congrArg YoungDiagram.cells (YoungDiagram.ofRowLens_to_rowLens_eq_self (μ:=μ.val))
  calc
    _ = ∑ c : Cells μ.val, cellContent c.val :=
      Fintype.sum_equiv t.val _ _ (by intro i; rfl)
    _ = ∑ c ∈ μ.val.cells, cellContent c := Finset.sum_coe_sort μ.val.cells cellContent
    _ = _ := by
      rw [Paper20.contentOf_eq_boxes_sum,← List.sum_toFinset _ (Paper20.boxesOf_nodup _),
        Paper20.boxesOf_toFinset,hcells]
      rfl

section Field
variable {F : Type*} [Field F]

lemma murphyDiagonal_first (v : F) {n : ℕ} {μ : Shape n} (hn : 0<n) :
    murphyDiagonal (μ:=μ) v ⟨0,hn⟩=1 := by
  apply LinearMap.ext
  intro f
  funext t
  change eigenvalue v t ⟨0,hn⟩*f t=f t
  simp only [eigenvalue,filling_first_content t hn,mul_zero,zpow_zero,one_mul]

/-- The actual palindromic Murphy word, built recursively out of the
proved adjacent standard-tableau Hecke generators. -/
def murphyOperator (v : F) {n : ℕ} {μ : Shape n} :
    (m : ℕ) → m<n → ((StandardFilling μ → F) →ₗ[F] (StandardFilling μ → F))
  | 0,_ => 1
  | m+1,hm =>
      tableauLinear v ⟨m,by omega⟩ ⟨m+1,hm⟩ rfl*
        murphyOperator v m (by omega)*tableauLinear v ⟨m,by omega⟩ ⟨m+1,hm⟩ rfl

/-- Every genuine Murphy word has exactly the claimed content diagonal
on the actual standard-filling block. -/
theorem murphyOperator_eq_diagonal (v : F) (hv : v≠0)
    (hp : Function.Injective (fun d : ℤ => v^d)) {n : ℕ} {μ : Shape n}
    (m : ℕ) (hm : m<n) : murphyOperator (μ:=μ) v m hm=murphyDiagonal v ⟨m,hm⟩ := by
  induction m with
  | zero => exact (murphyDiagonal_first v hm).symm
  | succ m ih =>
    rw [murphyOperator,ih (by omega)]
    exact tableauLinear_murphy v hv hp ⟨m,by omega⟩ ⟨m+1,hm⟩ rfl

lemma murphyDiagonal_list_apply (v : F) {n : ℕ} {μ : Shape n}
    (indices : List (Fin n)) (f : StandardFilling μ → F) (t : StandardFilling μ) :
    ((indices.map (murphyDiagonal (μ:=μ) v)).prod f) t=
      (indices.map (eigenvalue v t)).prod*f t := by
  induction indices with
  | nil => simp
  | cons i is ih =>
    simp only [List.map_cons,List.prod_cons]
    change eigenvalue v t i*((is.map (murphyDiagonal v)).prod f) t=
      (eigenvalue v t i*(is.map (eigenvalue v t)).prod)*f t
    rw [ih,mul_assoc]

lemma eigenvalue_list_product (v : F) (hv : v≠0) {n : ℕ} {μ : Shape n}
    (t : StandardFilling μ) (indices : List (Fin n)) :
    (indices.map (eigenvalue v t)).prod=v^(2*(indices.map (fillingContent t)).sum) := by
  induction indices with
  | nil => simp
  | cons i is ih =>
    simp only [List.map_cons,List.prod_cons,List.sum_cons,ih,eigenvalue]
    rw [← zpow_add₀ hv]
    congr 1
    ring

/-- The product of the actual palindromic Murphy words in increasing
label order, the source's Murphy factorization of the full twist. -/
def fullTwistTableau (v : F) {n : ℕ} {μ : Shape n} :
    (StandardFilling μ → F) →ₗ[F] (StandardFilling μ → F) :=
  ((List.finRange n).map (fun i => murphyOperator (μ:=μ) v i.val i.isLt)).prod

/-- The actual product of Murphy words acts by the original partition
content scalar q^c=v^(2c) on the entire actual standard-tableau block. -/
theorem fullTwistTableau_scalar (v : F) (hv : v≠0)
    (hp : Function.Injective (fun d : ℤ => v^d)) {n : ℕ} {μ : Shape n} :
    fullTwistTableau (μ:=μ) v=v^(2*Paper20.contentOf μ.val.rowLens) • 1 := by
  apply LinearMap.ext
  intro f
  funext t
  unfold fullTwistTableau
  simp_rw [murphyOperator_eq_diagonal v hv hp]
  rw [murphyDiagonal_list_apply,eigenvalue_list_product v hv,← Fin.sum_univ_def,filling_content_sum]
  rfl

end Field
end
end Paper20.Seminormal
