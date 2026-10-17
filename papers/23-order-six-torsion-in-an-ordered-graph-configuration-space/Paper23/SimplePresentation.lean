import Paper23.Subdivision
import Paper23.GraphStructure

/-! The eight-vertex simple presentation in §1 paragraph 7 has the same
underlying graph and ordered configuration spaces as the original multigraph.
Only original edges one and two are bisected. -/
namespace Paper23.SimplePresentation

open Cubical

noncomputable section

/-- The stated simple presentation, with its actual fifteen-edge incidence list. -/
def simpleGraph : GraphIncidence (Fin 8) (Fin 15) where
  source e := (GraphStructure.simpleEndpoints e).1
  target e := (GraphStructure.simpleEndpoints e).2

/-- This incidence presentation has neither loops nor parallel unordered edges. -/
theorem no_loops : ∀ e, simpleGraph.source e ≠ simpleGraph.target e :=
  GraphStructure.simple_no_loops

theorem no_parallel : ∀ e f,
    (GraphStructure.simpleEndpoints e = GraphStructure.simpleEndpoints f ∨
      GraphStructure.simpleEndpoints e =
        ((GraphStructure.simpleEndpoints f).2, (GraphStructure.simpleEndpoints f).1)) → e = f :=
  GraphStructure.simple_no_parallel

def oldVertex (v : CoreVertex) : Fin 8 := ⟨v.val, by omega⟩

def half : unitInterval := ⟨1 / 2, by constructor <;> norm_num⟩

/-- The two affine half-edge embeddings. -/
def affine (i : Fin 2) (s : unitInterval) : unitInterval :=
  ⟨((s : ℝ) + i.val) / 2, by
    have hi0 : (0 : ℝ) ≤ i.val := Nat.cast_nonneg _
    have hi1 : (i.val : ℝ) ≤ 1 := by exact_mod_cast (show i.val ≤ 1 by omega)
    constructor <;> linarith [s.property.1, s.property.2]⟩

@[simp] theorem affine00 : affine 0 0 = 0 := by ext; norm_num [affine]
@[simp] theorem affine01 : affine 0 1 = half := by ext; norm_num [affine, half]
@[simp] theorem affine10 : affine 1 0 = half := by ext; norm_num [affine, half]
@[simp] theorem affine11 : affine 1 1 = 1 := by ext; norm_num [affine]

theorem continuous_affine (i : Fin 2) : Continuous (affine i) := by
  apply Continuous.subtype_mk
  fun_prop

/-- Original vertices are fixed; the two inserted vertices are edge midpoints. -/
def vertexImage : Fin 8 → coreGraph.Realization := ![
  coreGraph.vertex 0, coreGraph.vertex 1, coreGraph.vertex 2,
  coreGraph.vertex 3, coreGraph.vertex 4, coreGraph.vertex 5,
  coreGraph.edge 1 half, coreGraph.edge 2 half]

@[simp] theorem vertexImage_old (v : CoreVertex) :
    vertexImage (oldVertex v) = coreGraph.vertex v := by fin_cases v <;> rfl

/-- Only the two subdivided a-b edges use half-edge parameters. -/
def edgeImage : Fin 15 → unitInterval → coreGraph.Realization := ![
  coreGraph.edge 0,
  (fun s => coreGraph.edge 1 (affine 0 s)), (fun s => coreGraph.edge 1 (affine 1 s)),
  (fun s => coreGraph.edge 2 (affine 0 s)), (fun s => coreGraph.edge 2 (affine 1 s)),
  coreGraph.edge 3, coreGraph.edge 4, coreGraph.edge 5, coreGraph.edge 6,
  coreGraph.edge 7, coreGraph.edge 8, coreGraph.edge 9, coreGraph.edge 10,
  coreGraph.edge 11, coreGraph.edge 12]

@[simp] theorem edgeImage_zero (e : Fin 15) :
    edgeImage e 0 = vertexImage (simpleGraph.source e) := by
  fin_cases e
  · change coreGraph.edge 0 0 = coreGraph.vertex 0
    exact coreGraph.edge_zero 0
  · change coreGraph.edge 1 (affine 0 0) = coreGraph.vertex 0
    rw [affine00, GraphIncidence.edge_zero]
    rfl
  · change coreGraph.edge 1 (affine 1 0) = coreGraph.edge 1 half
    exact congrArg (coreGraph.edge 1) affine10
  · change coreGraph.edge 2 (affine 0 0) = coreGraph.vertex 0
    rw [affine00, GraphIncidence.edge_zero]
    rfl
  · change coreGraph.edge 2 (affine 1 0) = coreGraph.edge 2 half
    exact congrArg (coreGraph.edge 2) affine10
  · change coreGraph.edge 3 0 = coreGraph.vertex 0
    exact coreGraph.edge_zero 3
  · change coreGraph.edge 4 0 = coreGraph.vertex 0
    exact coreGraph.edge_zero 4
  · change coreGraph.edge 5 0 = coreGraph.vertex 1
    exact coreGraph.edge_zero 5
  · change coreGraph.edge 6 0 = coreGraph.vertex 1
    exact coreGraph.edge_zero 6
  · change coreGraph.edge 7 0 = coreGraph.vertex 2
    exact coreGraph.edge_zero 7
  · change coreGraph.edge 8 0 = coreGraph.vertex 2
    exact coreGraph.edge_zero 8
  · change coreGraph.edge 9 0 = coreGraph.vertex 2
    exact coreGraph.edge_zero 9
  · change coreGraph.edge 10 0 = coreGraph.vertex 3
    exact coreGraph.edge_zero 10
  · change coreGraph.edge 11 0 = coreGraph.vertex 3
    exact coreGraph.edge_zero 11
  · change coreGraph.edge 12 0 = coreGraph.vertex 4
    exact coreGraph.edge_zero 12

@[simp] theorem edgeImage_one (e : Fin 15) :
    edgeImage e 1 = vertexImage (simpleGraph.target e) := by
  fin_cases e
  · change coreGraph.edge 0 1 = coreGraph.vertex 1
    exact coreGraph.edge_one 0
  · change coreGraph.edge 1 (affine 0 1) = coreGraph.edge 1 half
    exact congrArg (coreGraph.edge 1) affine01
  · change coreGraph.edge 1 (affine 1 1) = coreGraph.vertex 1
    rw [affine11, GraphIncidence.edge_one]
    rfl
  · change coreGraph.edge 2 (affine 0 1) = coreGraph.edge 2 half
    exact congrArg (coreGraph.edge 2) affine01
  · change coreGraph.edge 2 (affine 1 1) = coreGraph.vertex 1
    rw [affine11, GraphIncidence.edge_one]
    rfl
  · change coreGraph.edge 3 1 = coreGraph.vertex 2
    exact coreGraph.edge_one 3
  · change coreGraph.edge 4 1 = coreGraph.vertex 3
    exact coreGraph.edge_one 4
  · change coreGraph.edge 5 1 = coreGraph.vertex 4
    exact coreGraph.edge_one 5
  · change coreGraph.edge 6 1 = coreGraph.vertex 5
    exact coreGraph.edge_one 6
  · change coreGraph.edge 7 1 = coreGraph.vertex 3
    exact coreGraph.edge_one 7
  · change coreGraph.edge 8 1 = coreGraph.vertex 4
    exact coreGraph.edge_one 8
  · change coreGraph.edge 9 1 = coreGraph.vertex 5
    exact coreGraph.edge_one 9
  · change coreGraph.edge 10 1 = coreGraph.vertex 4
    exact coreGraph.edge_one 10
  · change coreGraph.edge 11 1 = coreGraph.vertex 5
    exact coreGraph.edge_one 11
  · change coreGraph.edge 12 1 = coreGraph.vertex 5
    exact coreGraph.edge_one 12

theorem continuous_edgeImage (e : Fin 15) : Continuous (edgeImage e) := by
  fin_cases e <;> first
  | exact coreGraph.continuous_edge _
  | exact (coreGraph.continuous_edge _).comp (continuous_affine _)

def forwardRaw : simpleGraph.PreRealization → coreGraph.Realization
  | Sum.inl v => vertexImage v
  | Sum.inr (e, s) => edgeImage e s

theorem forwardRaw_attaching {x y : simpleGraph.PreRealization}
    (h : simpleGraph.Attaching x y) : forwardRaw x = forwardRaw y := by
  rcases h with ⟨e, rfl, rfl⟩ | ⟨e, rfl, rfl⟩ <;> simp [forwardRaw]

theorem forwardRaw_equivalent {x y : simpleGraph.PreRealization}
    (h : simpleGraph.realizationSetoid x y) : forwardRaw x = forwardRaw y := by
  induction h with
  | rel _ _ h => exact forwardRaw_attaching h
  | refl _ => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ hxy hyz => exact hxy.trans hyz

/-- Map the simple presentation to the original quotient graph. -/
def forward : simpleGraph.Realization → coreGraph.Realization :=
  Quotient.lift forwardRaw fun _ _ h => forwardRaw_equivalent h

@[simp] theorem forward_vertex (v : Fin 8) :
    forward (simpleGraph.vertex v) = vertexImage v := rfl
@[simp] theorem forward_edge (e : Fin 15) (s : unitInterval) :
    forward (simpleGraph.edge e s) = edgeImage e s := rfl

theorem continuous_forwardRaw : Continuous forwardRaw := by
  apply continuous_sum_dom.2
  exact ⟨continuous_of_discreteTopology, continuous_prod_of_discrete_left.2 continuous_edgeImage⟩

theorem continuous_forward : Continuous forward :=
  continuous_forwardRaw.quotient_lift _

/-- The inverse affine parameters, continuously clamped outside each half. -/
def rescale (i : Fin 2) (s : unitInterval) : unitInterval :=
  Set.projIcc 0 1 zero_le_one (2 * (s : ℝ) - i.val)

theorem continuous_rescale (i : Fin 2) : Continuous (rescale i) := by
  apply continuous_projIcc.comp
  fun_prop

@[simp] theorem rescale00 : rescale 0 0 = 0 := by ext; norm_num [rescale, Set.coe_projIcc]
@[simp] theorem rescale01 : rescale 0 half = 1 := by ext; norm_num [rescale, half, Set.coe_projIcc]
@[simp] theorem rescale10 : rescale 1 half = 0 := by ext; norm_num [rescale, half, Set.coe_projIcc]
@[simp] theorem rescale11 : rescale 1 1 = 1 := by ext; norm_num [rescale, Set.coe_projIcc]

/-- Follow two consecutive simple edges, each for half of the parameter time. -/
def splitPath (a b : Fin 15) (s : unitInterval) : simpleGraph.Realization :=
  if (s : ℝ) ≤ 1 / 2 then simpleGraph.edge a (rescale 0 s)
  else simpleGraph.edge b (rescale 1 s)

theorem continuous_splitPath (a b : Fin 15)
    (hjoin : simpleGraph.target a = simpleGraph.source b) : Continuous (splitPath a b) := by
  apply ((simpleGraph.continuous_edge a).comp (continuous_rescale 0)).if_le
    ((simpleGraph.continuous_edge b).comp (continuous_rescale 1))
    continuous_subtype_val continuous_const
  intro s hs
  have ht : s = half := Subtype.ext hs
  subst s
  simp [hjoin]

@[simp] theorem splitPath_zero (a b : Fin 15) : splitPath a b 0 = simpleGraph.edge a 0 := by
  norm_num [splitPath]
@[simp] theorem splitPath_one (a b : Fin 15) : splitPath a b 1 = simpleGraph.edge b 1 := by
  norm_num [splitPath]
@[simp] theorem splitPath_half (a b : Fin 15) : splitPath a b half = simpleGraph.edge a 1 := by
  unfold splitPath
  rw [if_pos (by norm_num [half]), rescale01]

/-- Join only original edges one and two; every other edge is kept unchanged. -/
def reverseEdge : CoreEdge → unitInterval → simpleGraph.Realization := ![
  simpleGraph.edge 0, splitPath 1 2, splitPath 3 4,
  simpleGraph.edge 5, simpleGraph.edge 6, simpleGraph.edge 7, simpleGraph.edge 8,
  simpleGraph.edge 9, simpleGraph.edge 10, simpleGraph.edge 11, simpleGraph.edge 12,
  simpleGraph.edge 13, simpleGraph.edge 14]

@[simp] theorem reverseEdge_zero (e : CoreEdge) :
    reverseEdge e 0 = simpleGraph.vertex (oldVertex (coreGraph.source e)) := by
  fin_cases e
  · change simpleGraph.edge 0 0 = simpleGraph.vertex 0
    exact simpleGraph.edge_zero 0
  · change splitPath 1 2 0 = simpleGraph.vertex 0
    rw [splitPath_zero, GraphIncidence.edge_zero]
    rfl
  · change splitPath 3 4 0 = simpleGraph.vertex 0
    rw [splitPath_zero, GraphIncidence.edge_zero]
    rfl
  · change simpleGraph.edge 5 0 = simpleGraph.vertex 0
    exact simpleGraph.edge_zero 5
  · change simpleGraph.edge 6 0 = simpleGraph.vertex 0
    exact simpleGraph.edge_zero 6
  · change simpleGraph.edge 7 0 = simpleGraph.vertex 1
    exact simpleGraph.edge_zero 7
  · change simpleGraph.edge 8 0 = simpleGraph.vertex 1
    exact simpleGraph.edge_zero 8
  · change simpleGraph.edge 9 0 = simpleGraph.vertex 2
    exact simpleGraph.edge_zero 9
  · change simpleGraph.edge 10 0 = simpleGraph.vertex 2
    exact simpleGraph.edge_zero 10
  · change simpleGraph.edge 11 0 = simpleGraph.vertex 2
    exact simpleGraph.edge_zero 11
  · change simpleGraph.edge 12 0 = simpleGraph.vertex 3
    exact simpleGraph.edge_zero 12
  · change simpleGraph.edge 13 0 = simpleGraph.vertex 3
    exact simpleGraph.edge_zero 13
  · change simpleGraph.edge 14 0 = simpleGraph.vertex 4
    exact simpleGraph.edge_zero 14

@[simp] theorem reverseEdge_one (e : CoreEdge) :
    reverseEdge e 1 = simpleGraph.vertex (oldVertex (coreGraph.target e)) := by
  fin_cases e
  · change simpleGraph.edge 0 1 = simpleGraph.vertex 1
    exact simpleGraph.edge_one 0
  · change splitPath 1 2 1 = simpleGraph.vertex 1
    rw [splitPath_one, GraphIncidence.edge_one]
    rfl
  · change splitPath 3 4 1 = simpleGraph.vertex 1
    rw [splitPath_one, GraphIncidence.edge_one]
    rfl
  · change simpleGraph.edge 5 1 = simpleGraph.vertex 2
    exact simpleGraph.edge_one 5
  · change simpleGraph.edge 6 1 = simpleGraph.vertex 3
    exact simpleGraph.edge_one 6
  · change simpleGraph.edge 7 1 = simpleGraph.vertex 4
    exact simpleGraph.edge_one 7
  · change simpleGraph.edge 8 1 = simpleGraph.vertex 5
    exact simpleGraph.edge_one 8
  · change simpleGraph.edge 9 1 = simpleGraph.vertex 3
    exact simpleGraph.edge_one 9
  · change simpleGraph.edge 10 1 = simpleGraph.vertex 4
    exact simpleGraph.edge_one 10
  · change simpleGraph.edge 11 1 = simpleGraph.vertex 5
    exact simpleGraph.edge_one 11
  · change simpleGraph.edge 12 1 = simpleGraph.vertex 4
    exact simpleGraph.edge_one 12
  · change simpleGraph.edge 13 1 = simpleGraph.vertex 5
    exact simpleGraph.edge_one 13
  · change simpleGraph.edge 14 1 = simpleGraph.vertex 5
    exact simpleGraph.edge_one 14

theorem continuous_reverseEdge (e : CoreEdge) : Continuous (reverseEdge e) := by
  fin_cases e <;> first
  | exact simpleGraph.continuous_edge _
  | exact continuous_splitPath _ _ (by decide)

def reverseRaw : coreGraph.PreRealization → simpleGraph.Realization
  | Sum.inl v => simpleGraph.vertex (oldVertex v)
  | Sum.inr (e, s) => reverseEdge e s

theorem reverseRaw_attaching {x y : coreGraph.PreRealization}
    (h : coreGraph.Attaching x y) : reverseRaw x = reverseRaw y := by
  rcases h with ⟨e, rfl, rfl⟩ | ⟨e, rfl, rfl⟩ <;> simp [reverseRaw]

theorem reverseRaw_equivalent {x y : coreGraph.PreRealization}
    (h : coreGraph.realizationSetoid x y) : reverseRaw x = reverseRaw y := by
  induction h with
  | rel _ _ h => exact reverseRaw_attaching h
  | refl _ => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ hxy hyz => exact hxy.trans hyz

/-- The inverse map on the original graph realization. -/
def reverse : coreGraph.Realization → simpleGraph.Realization :=
  Quotient.lift reverseRaw fun _ _ h => reverseRaw_equivalent h

@[simp] theorem reverse_vertex (v : CoreVertex) :
    reverse (coreGraph.vertex v) = simpleGraph.vertex (oldVertex v) := rfl
@[simp] theorem reverse_edge (e : CoreEdge) (s : unitInterval) :
    reverse (coreGraph.edge e s) = reverseEdge e s := rfl

theorem continuous_reverseRaw : Continuous reverseRaw := by
  apply continuous_sum_dom.2
  exact ⟨continuous_of_discreteTopology, continuous_prod_of_discrete_left.2 continuous_reverseEdge⟩

theorem continuous_reverse : Continuous reverse :=
  continuous_reverseRaw.quotient_lift _

@[simp] theorem rescale_affine (i : Fin 2) (s : unitInterval) : rescale i (affine i s) = s := by
  have h : 2 * (affine i s : ℝ) - i.val = (s : ℝ) := by simp only [affine]; ring
  unfold rescale
  rw [h]
  exact Set.projIcc_val zero_le_one s

theorem affine_rescale (i : Fin 2) (s : unitInterval)
    (hlo : (i.val : ℝ) / 2 ≤ s) (hhi : (s : ℝ) ≤ (i.val + 1) / 2) :
    affine i (rescale i s) = s := by
  have hmem : 2 * (s : ℝ) - i.val ∈ Set.Icc (0 : ℝ) 1 := by constructor <;> linarith
  apply Subtype.ext
  change ((Set.projIcc 0 1 zero_le_one (2 * (s : ℝ) - i.val) : ℝ) + i.val) / 2 = s
  rw [Set.projIcc_of_mem zero_le_one hmem]
  ring

theorem splitPath_affine0 (a b : Fin 15) (s : unitInterval) :
    splitPath a b (affine 0 s) = simpleGraph.edge a s := by
  have h : (affine 0 s : ℝ) ≤ 1 / 2 := by
    simp only [affine, Fin.val_zero, Nat.cast_zero, add_zero]
    linarith [s.property.2]
  simp only [splitPath, if_pos h, rescale_affine]

theorem splitPath_affine1 (a b : Fin 15) (hjoin : simpleGraph.target a = simpleGraph.source b)
    (s : unitInterval) : splitPath a b (affine 1 s) = simpleGraph.edge b s := by
  by_cases h : (affine 1 s : ℝ) ≤ 1 / 2
  · have hs : s = 0 := by
      apply Subtype.ext
      change (s : ℝ) = 0
      norm_num [affine] at h
      linarith [s.property.1]
    subst s
    simp only [affine10, splitPath_half, GraphIncidence.edge_one, GraphIncidence.edge_zero, hjoin]
  · simp only [splitPath, if_neg h, rescale_affine]

/-- The forward map sends either of the two joined edges back to its original edge. -/
theorem forward_splitPath (a b : Fin 15) (e : CoreEdge)
    (ha : ∀ s, edgeImage a s = coreGraph.edge e (affine 0 s))
    (hb : ∀ s, edgeImage b s = coreGraph.edge e (affine 1 s)) (s : unitInterval) :
    forward (splitPath a b s) = coreGraph.edge e s := by
  unfold splitPath
  split_ifs with h
  · rw [forward_edge, ha]
    apply congrArg (coreGraph.edge e)
    apply affine_rescale
    · norm_num; exact s.property.1
    · norm_num; exact h
  · rw [forward_edge, hb]
    apply congrArg (coreGraph.edge e)
    apply affine_rescale
    · norm_num; linarith
    · norm_num; exact s.property.2

theorem forward_reverseEdge (e : CoreEdge) (s : unitInterval) :
    forward (reverseEdge e s) = coreGraph.edge e s := by
  fin_cases e <;> first
  | rfl
  | exact forward_splitPath 1 2 1 (fun _ => rfl) (fun _ => rfl) s
  | exact forward_splitPath 3 4 2 (fun _ => rfl) (fun _ => rfl) s

theorem reverse_edgeImage (e : Fin 15) (s : unitInterval) :
    reverse (edgeImage e s) = simpleGraph.edge e s := by
  fin_cases e <;> first
  | rfl
  | exact splitPath_affine0 1 2 s
  | exact splitPath_affine1 1 2 (by decide) s
  | exact splitPath_affine0 3 4 s
  | exact splitPath_affine1 3 4 (by decide) s

theorem reverse_vertexImage (v : Fin 8) : reverse (vertexImage v) = simpleGraph.vertex v := by
  fin_cases v
  · change reverse (coreGraph.vertex 0) = simpleGraph.vertex 0
    rfl
  · change reverse (coreGraph.vertex 1) = simpleGraph.vertex 1
    rfl
  · change reverse (coreGraph.vertex 2) = simpleGraph.vertex 2
    rfl
  · change reverse (coreGraph.vertex 3) = simpleGraph.vertex 3
    rfl
  · change reverse (coreGraph.vertex 4) = simpleGraph.vertex 4
    rfl
  · change reverse (coreGraph.vertex 5) = simpleGraph.vertex 5
    rfl
  · change reverse (coreGraph.edge 1 half) = simpleGraph.vertex 6
    rw [reverse_edge]
    change splitPath 1 2 half = simpleGraph.vertex 6
    rw [splitPath_half, GraphIncidence.edge_one]
    rfl
  · change reverse (coreGraph.edge 2 half) = simpleGraph.vertex 7
    rw [reverse_edge]
    change splitPath 3 4 half = simpleGraph.vertex 7
    rw [splitPath_half, GraphIncidence.edge_one]
    rfl

theorem forward_reverse (x : coreGraph.Realization) : forward (reverse x) = x := by
  refine Quotient.inductionOn x ?_
  rintro (v | ⟨e, s⟩)
  · change forward (reverse (coreGraph.vertex v)) = coreGraph.vertex v
    simp
  · exact forward_reverseEdge e s

theorem reverse_forward (x : simpleGraph.Realization) : reverse (forward x) = x := by
  refine Quotient.inductionOn x ?_
  rintro (v | ⟨e, s⟩)
  · exact reverse_vertexImage v
  · exact reverse_edgeImage e s

/-- The eight-vertex simple presentation realizes precisely the original graph. -/
def realizationHomeomorph : simpleGraph.Realization ≃ₜ coreGraph.Realization where
  toFun := forward
  invFun := reverse
  left_inv := reverse_forward
  right_inv := forward_reverse
  continuous_toFun := continuous_forward
  continuous_invFun := continuous_reverse

/-- The ordered, labelled configuration spaces agree for every particle number. -/
def configurationHomeomorph (n : ℕ) :
    OrderedConfiguration n simpleGraph.Realization ≃ₜ OrderedConfiguration n coreGraph.Realization :=
  OrderedConfiguration.homeomorph realizationHomeomorph

def fourConfigurationHomeomorph :
    OrderedConfiguration 4 simpleGraph.Realization ≃ₜ SourceConfigurationSpace :=
  configurationHomeomorph 4

/-- Integral singular homology is unchanged by this explicit simple presentation. -/
def configurationHomologyIso (q n : ℕ) :
    IntegralHomology q (OrderedConfiguration n simpleGraph.Realization) ≅
      IntegralHomology q (OrderedConfiguration n coreGraph.Realization) :=
  integralHomologyHomeomorph q (configurationHomeomorph n)

/-- The four-particle degree-two homology isomorphism to the original source. -/
def sourceHomologyIso :
    IntegralHomology 2 (OrderedConfiguration 4 simpleGraph.Realization) ≅ SourceHomology :=
  configurationHomologyIso 2 4

/-- The corresponding additive equivalence preserves the exact order of classes. -/
def sourceHomologyEquiv :
    IntegralHomology 2 (OrderedConfiguration 4 simpleGraph.Realization) ≃+ SourceHomology := by
  letI : Module ℤ (IntegralHomology 2 (OrderedConfiguration 4 simpleGraph.Realization)) :=
    (IntegralHomology 2 (OrderedConfiguration 4 simpleGraph.Realization)).isModule
  letI : Module ℤ SourceHomology := SourceHomology.isModule
  exact sourceHomologyIso.toLinearEquiv.toAddEquiv

/-- The simple-presentation consequence reduces exactly to the original paper's
homology conclusion, via the proved graph homeomorphism. -/
theorem orderSix_simplePresentation_iff :
    (∃ z : IntegralHomology 2 (OrderedConfiguration 4 simpleGraph.Realization),
      addOrderOf z = 6) ↔ MainTheoremStatement := by
  change (∃ z : IntegralHomology 2 (OrderedConfiguration 4 simpleGraph.Realization),
    addOrderOf z = 6) ↔ ∃ z : SourceHomology, addOrderOf z = 6
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨sourceHomologyEquiv z, ?_⟩
    rw [sourceHomologyEquiv.addOrderOf_eq]
    exact hz
  · rintro ⟨z, hz⟩
    refine ⟨sourceHomologyEquiv.symm z, ?_⟩
    rw [sourceHomologyEquiv.symm.addOrderOf_eq]
    exact hz

end
end Paper23.SimplePresentation
