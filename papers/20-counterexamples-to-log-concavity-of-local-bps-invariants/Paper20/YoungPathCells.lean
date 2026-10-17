import Paper20.YoungPaths

namespace Paper20.YoungShapes
open Finset Paper20.YoungCorners
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

/-- The actual new cell of a proved one-box step. -/
def stepCorner {n : ℕ} {μ : Shape (n+1)}
    (κ : {κ : Shape n // Covers κ.val μ.val}) : {c : ℕ × ℕ // c ∈ removableCells μ.val} :=
  lowerCoverEquiv μ.val ⟨κ.val.val,κ.property⟩

lemma stepCorner_removable {n : ℕ} {μ : Shape (n+1)}
    (κ : {κ : Shape n // Covers κ.val μ.val}) : Removable μ.val (stepCorner κ).val :=
  (mem_removableCells ..).mp (stepCorner κ).property

lemma previous_eq_erase {n : ℕ} {μ : Shape (n+1)}
    (κ : {κ : Shape n // Covers κ.val μ.val}) :
    κ.val.val=erase μ.val (stepCorner κ).val (stepCorner_removable κ) := by
  exact (congrArg Subtype.val ((lowerCoverEquiv μ.val).symm_apply_apply
    ⟨κ.val.val,κ.property⟩)).symm

lemma stepCorner_not_previous {n : ℕ} {μ : Shape (n+1)}
    (κ : {κ : Shape n // Covers κ.val μ.val}) : (stepCorner κ).val ∉ κ.val.val := by
  rw [previous_eq_erase κ,erase_mem]
  simp only [ne_eq,not_true_eq_false,false_and,not_false_eq_true]

lemma step_cells {n : ℕ} {μ : Shape (n+1)}
    (κ : {κ : Shape n // Covers κ.val μ.val}) :
    μ.val.cells=Insert.insert (stepCorner κ).val κ.val.val.cells := by
  have he := congrArg YoungDiagram.cells
    (insert_erase μ.val (stepCorner κ).val (stepCorner_removable κ))
  change Insert.insert (stepCorner κ).val
    (erase μ.val (stepCorner κ).val (stepCorner_removable κ)).cells=μ.val.cells at he
  rw [← previous_eq_erase κ] at he
  exact he.symm

/-- The genuine cells in the order in which an actual saturated path
adds them. No fillings or dimensions are postulated. -/
def cellList : {n : ℕ} → {μ : Shape n} → Path n μ → List (ℕ × ℕ)
  | 0,_,_ => []
  | _+1,_,t => cellList t.2 ++ [(stepCorner t.1).val]

@[simp] theorem cellList_length (n : ℕ) : ∀ (μ : Shape n) (t : Path n μ),
    (cellList t).length=n := by
  induction n with
  | zero => intro μ t; rfl
  | succ n ih =>
    intro μ t
    change (cellList t.2 ++ [(stepCorner t.1).val]).length=n+1
    simp only [List.length_append,List.length_singleton,ih]

/-- Every cell of the final actual Young diagram occurs in its path,
and every cell occurring in the path belongs to that diagram. -/
theorem mem_cellList (n : ℕ) : ∀ (μ : Shape n) (t : Path n μ) (a : ℕ × ℕ),
    a ∈ cellList t ↔ a ∈ μ.val := by
  induction n with
  | zero =>
    intro μ t a
    have he : μ.val.cells=∅ := Finset.card_eq_zero.mp μ.property
    change a ∈ ([]:List (ℕ × ℕ)) ↔ a ∈ μ.val.cells
    rw [he]
    simp
  | succ n ih =>
    intro μ t a
    change a ∈ cellList t.2 ++ [(stepCorner t.1).val] ↔ a ∈ μ.val.cells
    rw [List.mem_append,List.mem_singleton,ih,step_cells t.1,Finset.mem_insert]
    exact or_comm

/-- A path adds every final cell exactly once. -/
theorem cellList_nodup (n : ℕ) : ∀ (μ : Shape n) (t : Path n μ), (cellList t).Nodup := by
  induction n with
  | zero => intro μ t; exact List.nodup_nil
  | succ n ih =>
    intro μ t
    change (cellList t.2 ++ [(stepCorner t.1).val]).Nodup
    apply List.Nodup.append (ih _ t.2) (by simp)
    intro a ha hb
    have he : a=(stepCorner t.1).val := List.mem_singleton.mp hb
    subst a
    exact stepCorner_not_previous t.1 ((mem_cellList n _ t.2 _).mp ha)

/-- The finite set of all cells in an actual path is exactly the final
actual Young diagram, a proved equality of the original concrete cells. -/
theorem cellList_toFinset {n : ℕ} {μ : Shape n} (t : Path n μ) :
    (cellList t).toFinset=μ.val.cells := by
  ext a
  rw [List.mem_toFinset]
  exact mem_cellList n μ t a

/-- The cell order of a genuine path is a linear extension of the cell
partial order: a later added cell can never lie weakly above an earlier one. -/
theorem cellList_order (n : ℕ) : ∀ (μ : Shape n) (t : Path n μ),
    (cellList t).Pairwise (fun a b => ¬b≤a) := by
  induction n with
  | zero => intro μ t; exact List.Pairwise.nil
  | succ n ih =>
    intro μ t
    change (cellList t.2 ++ [(stepCorner t.1).val]).Pairwise _
    rw [List.pairwise_append]
    refine ⟨ih _ t.2,by simp,?_⟩
    intro a ha b hb hba
    have he : b=(stepCorner t.1).val := List.mem_singleton.mp hb
    subst b
    have haold := (mem_cellList n _ t.2 a).mp ha
    have hafinal := t.1.property.1 haold
    have hac := removable_maximal μ.val (stepCorner t.1).val
      (stepCorner_removable t.1) a hafinal hba
    rw [hac] at haold
    exact stepCorner_not_previous t.1 haold

end
end Paper20.YoungShapes
