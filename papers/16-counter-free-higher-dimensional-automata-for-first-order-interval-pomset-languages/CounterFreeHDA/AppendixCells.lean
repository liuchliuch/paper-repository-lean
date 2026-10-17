import CounterFreeHDA.EffectiveFaces
import CounterFreeHDA.Appendix
import CounterFreeHDA.PomsetPaths

namespace CounterFreeHDA.Cubical.Face
universe u
variable {Lab : Type u} {k : ℕ} {U V W : Cube Lab k}

def vertices (f : Face U V) (ρ : Fin U.dim → Bool) : Fin V.dim → Bool :=
  fun j => Sum.elim ρ id (f.sub j)

@[simp] theorem vertices_ident (ρ : Fin U.dim → Bool) : (Face.ident U).vertices ρ = ρ := rfl

theorem vertices_comp (f : Face U V) (g : Face V W) (ρ : Fin U.dim → Bool) :
    (f.comp g).vertices ρ = g.vertices (f.vertices ρ) := by
  funext j
  cases hg : g.sub j <;> simp only [vertices,Face.comp,hg,Sum.elim_inl,Sum.elim_inr,id_eq]

end CounterFreeHDA.Cubical.Face

namespace CounterFreeHDA.Appendix.Actual
open Cubical
abbrev UCube := Cube Unit 2
abbrev VertexFunction (U : UCube) := (Fin U.dim → Bool) → Fin 2
attribute [local instance] Effective.faceFintype Effective.faceDecidableEq

/-- The three displayed edge functions and square functions, with shared
corners giving exactly the original eight-cell precubical table. -/
def model (U : UCube) (i : Fin (size U.1)) (ρ : Fin U.dim → Bool) : Fin 2 :=
  match U.1, i with
  | ⟨0,_⟩,i => i
  | ⟨1,_⟩,i =>
    if i.val = 0 then if ∀ j, ρ j = true then 1 else 0
    else if i.val = 1 then if ∀ j, ρ j = true then 0 else 1
    else 1
  | ⟨2,_⟩,i =>
    if i.val = 0 then if (∀ j, ρ j = false) ∨ (∀ j, ρ j = true) then 0 else 1
    else if i.val = 1 then 1
    else if ∀ j, ρ j = true then 0 else 1
  | ⟨n+3,h⟩,_ => False.elim (by omega)

theorem model_injective : ∀ U : UCube, Function.Injective (model U) := by decide

theorem model_face_closed : ∀ (U V : UCube) (f : Cubical.Face U V) (i : Fin (size V.1)),
    ∃ j : Fin (size U.1), model U j = fun ρ => model V i (f.vertices ρ) := by decide

abbrev Cell (U : UCube) := {x : VertexFunction U // x ∈ Set.range (model U)}

instance cellDecidable (U : UCube) : DecidablePred (fun x : VertexFunction U => x ∈ Set.range (model U)) := by
  intro x
  change Decidable (∃ i : Fin (size U.1), model U i = x)
  infer_instance

instance cellFintype (U : UCube) : Fintype (Cell U) := inferInstanceAs (Fintype {x : VertexFunction U // x ∈ Set.range (model U)})

/-- The actual finite eight-cell precubical set, with all mixed face identities. -/
def originalPrecubical : Precubical.{0,0} Unit 2 where
  Cell := Cell
  face f x := ⟨fun ρ => x.val (f.vertices ρ),by
    obtain ⟨i,hi⟩ := x.property
    obtain ⟨j,hj⟩ := model_face_closed _ _ f i
    exact ⟨j,by simpa only [hi] using hj⟩⟩
  face_ident x := by apply Subtype.ext; rfl
  face_comp f g x := by
    apply Subtype.ext
    funext ρ
    exact congrArg x.val (Face.vertices_comp f g ρ).symm

def originalHDA : HDA.{0,0} Unit 2 where
  toPrecubical := originalPrecubical
  initial := fun {U} x => U.dim = 0 ∧ ∀ ρ, x.val ρ = 0
  accepting := fun {U} x => U.dim = 0 ∧ ∀ ρ, x.val ρ = 0

noncomputable def cellEquiv (U : UCube) : Fin (size U.1) ≃ Cell U := Equiv.ofInjective (model U) (model_injective U)

instance originalCellDecidableEq (U : UCube) : DecidableEq (originalHDA.Cell U) :=
  inferInstanceAs (DecidableEq (Cell U))

instance originalFintype : Fintype (Σ U, originalHDA.Cell U) :=
  inferInstanceAs (Fintype (Σ U : UCube, Cell U))

theorem eight_cells : Fintype.card (Σ U, originalHDA.Cell U) = 8 := by decide

end CounterFreeHDA.Appendix.Actual
