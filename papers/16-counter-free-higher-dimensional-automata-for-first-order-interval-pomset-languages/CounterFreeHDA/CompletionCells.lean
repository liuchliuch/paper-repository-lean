import CounterFreeHDA.AppendixCells

namespace CounterFreeHDA.Appendix.Completion
open Cubical
abbrev UCube := Cube Unit 2
def profileSize : Fin 3 → ℕ := ![3,4,3]

abbrev VertexFunction (U : UCube) := (Fin U.dim → Bool) → Fin 3
attribute [local instance] Effective.faceFintype Effective.faceDecidableEq

/-- Live deletion profiles have the lower/upper faces displayed in A.2. -/
def completionModel (U : UCube) (i : Fin (profileSize U.1)) (ρ : Fin U.dim → Bool) : Fin 3 :=
  match U.1, i with
  | ⟨0,_⟩,i => i
  | ⟨1,_⟩,i =>
    if i.val = 0 then if ∀ j, ρ j = true then 1 else 0
    else if i.val = 1 then if ∀ j, ρ j = true then 0 else 1
    else if i.val = 2 then if ∀ j, ρ j = true then 2 else 1
    else 2
  | ⟨2,_⟩,i =>
    if i.val = 0 then if (∀ j, ρ j = false) ∨ (∀ j, ρ j = true) then 0 else 1
    else if i.val = 1 then if ∀ j, ρ j = false then 1 else 2
    else 2
  | ⟨n+3,h⟩,_ => False.elim (by omega)

theorem completionModel_injective : ∀ U : UCube, Function.Injective (completionModel U) := by decide

theorem completionModel_face_closed : ∀ (U V : UCube) (f : Cubical.Face U V) (i : Fin (profileSize V.1)),
    ∃ j : Fin (profileSize U.1), completionModel U j = fun ρ => completionModel V i (f.vertices ρ) := by decide

abbrev Cell (U : UCube) := {x : VertexFunction U // x ∈ Set.range (completionModel U)}

instance cellDecidable (U : UCube) : DecidablePred (fun x : VertexFunction U => x ∈ Set.range (completionModel U)) := by
  intro x
  change Decidable (∃ i : Fin (profileSize U.1), completionModel U i = x)
  infer_instance

instance cellFintype (U : UCube) : Fintype (Cell U) := inferInstanceAs (Fintype {x : VertexFunction U // x ∈ Set.range (completionModel U)})

/-- The actual ten-cell live completion HDA, with every mixed face identity. -/
def completionPrecubical : Precubical.{0,0} Unit 2 where
  Cell := Cell
  face f x := ⟨fun ρ => x.val (f.vertices ρ),by
    obtain ⟨i,hi⟩ := x.property
    obtain ⟨j,hj⟩ := completionModel_face_closed _ _ f i
    exact ⟨j,by simpa only [hi] using hj⟩⟩
  face_ident x := by apply Subtype.ext; rfl
  face_comp f g x := by
    apply Subtype.ext
    funext ρ
    exact congrArg x.val (Face.vertices_comp f g ρ).symm

def completionHDA : HDA.{0,0} Unit 2 where
  toPrecubical := completionPrecubical
  initial := fun {U} x => U.dim = 0 ∧ ∀ ρ, x.val ρ = 0
  accepting := fun {U} x => U.dim = 0 ∧ ∀ ρ, x.val ρ ≠ 1

noncomputable def cellEquiv (U : UCube) : Fin (profileSize U.1) ≃ Cell U := Equiv.ofInjective (completionModel U) (completionModel_injective U)

instance completionCellDecidableEq (U : UCube) : DecidableEq (completionHDA.Cell U) :=
  inferInstanceAs (DecidableEq (Cell U))

instance completionFintype : Fintype (Σ U, completionHDA.Cell U) :=
  inferInstanceAs (Fintype (Σ U : UCube, Cell U))

theorem ten_cells : Fintype.card (Σ U, completionHDA.Cell U) = 10 := by decide

end CounterFreeHDA.Appendix.Completion
