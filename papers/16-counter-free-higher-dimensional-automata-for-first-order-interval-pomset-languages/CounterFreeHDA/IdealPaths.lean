import CounterFreeHDA.IdealDiagram

/-! Propagation of the recognised arrow along actual ideal-diagram paths.
This is the soundness direction of Proposition 3.4, with no assumed path
criterion or assumed language equality. -/

namespace CounterFreeHDA.Cubical

universe u v

variable {Lab : Type u} {k : ℕ} (C : FinCat.{u,v} (Cube Lab k)) (ord : C.IsOrdered)
variable (image : ∀ {U V}, Step U V → C.Hom U V)

/-- Evaluate an elementary ST-decomposition in the given recognising category. -/
def wordImage : ∀ {U V}, Word (Lab := Lab) (k := k) U V → C.Hom U V
  | _, _, .nil U => C.id U
  | _, _, .cons s p => C.comp (image s) (wordImage p)

namespace IdealDiagram

variable {C ord image}

/-- The lower-set inequalities force the actual arrow image of a path to
propagate from every arrow in its initial top value. -/
theorem run_propagates {S U V : Cube Lab k} {p : Word U V}
    {x : IdealDiagram C ord image S U} {y : IdealDiagram C ord image S V}
    (r : (ideal C ord image S).Run p x y) {a : C.Hom S U} (ha : a ∈ x.top) :
    C.comp a (wordImage C image p) ∈ y.top := by
  induction p with
  | nil U =>
    have hxy := ((ideal C ord image S).run_nil_iff x y).mp r
    subst y
    simpa only [wordImage, C.comp_id] using ha
  | @cons U W V s p ih =>
    cases s with
    | start f hl hd =>
      obtain ⟨z, hxz, hrest⟩ := ((ideal C ord image S).run_start_iff f hl hd p x y).mp r
      subst x
      have htop : a ∈ z.val f := by
        simpa only [ideal, IdealDiagram.top, IdealDiagram.restrict_val, Face.ident_comp] using ha
      have hstep : C.comp a (image (.start f hl hd)) ∈ z.top := by
        apply z.start f hl hd (Face.ident _)
        apply (LowerSetAction.mem_act ord).mpr
        refine ⟨a, ?_, ord.homLE_refl _⟩
        simpa only [Face.comp_ident] using htop
      have h := ih hrest hstep
      simpa only [wordImage, C.assoc] using h
    | stop f hu hd =>
      have hrest := ((ideal C ord image S).run_stop_iff f hu hd p x y).mp r
      have hstep : C.comp a (image (.stop f hu hd)) ∈ (x.restrict f).top := by
        change C.comp a (image (.stop f hu hd)) ∈ x.val ((Face.ident _).comp f)
        rw [Face.ident_comp]
        have hh := x.stop f hu hd (Face.ident _)
        rw [Face.comp_ident] at hh
        apply hh
        exact (LowerSetAction.mem_act ord).mpr ⟨a, ha, ord.homLE_refl _⟩
      have h := ih hrest hstep
      simpa only [wordImage, C.assoc] using h

/-- **Proposition 3.4, soundness.** An actual accepting path of the component
`H_S` has its recognised image in `J`. -/
theorem accepting_run_sound {S V : Cube Lab k} {p : Word S V}
    {x : IdealDiagram C ord image S S} {y : IdealDiagram C ord image S V}
    (r : (ideal C ord image S).Run p x y)
    (hi : C.id S ∈ x.top) (J : Set (C.Hom S V)) (hf : y.top ⊆ J) :
    wordImage C image p ∈ J := by
  have h := run_propagates r hi
  rw [C.id_comp] at h
  exact hf h

end IdealDiagram
end CounterFreeHDA.Cubical
