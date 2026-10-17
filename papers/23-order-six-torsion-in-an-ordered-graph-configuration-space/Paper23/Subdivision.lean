import Paper23.SourceTopology
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FunProp

/-! Explicit three-segment subdivision maps for the graph in equation (1). -/
namespace Paper23.Subdivision

open Cubical

noncomputable section

/-- The original vertices retained in the subdivision. -/
def oldVertex (v : CoreVertex) : Vertex := ⟨v.val, by omega⟩
/-- The first and second inserted vertex on an original edge. -/
def middleVertex (e : CoreEdge) (i : Fin 2) : Vertex := ⟨6 + 2 * e.val + i.val, by omega⟩
/-- The three oriented subedges on an original edge. -/
def segmentEdge (e : CoreEdge) (i : Fin 3) : Edge := ⟨3 * e.val + i.val, by omega⟩

def edgeCore (e : Edge) : CoreEdge := ⟨e.val / 3, by omega⟩
def edgePart (e : Edge) : Fin 3 := ⟨e.val % 3, Nat.mod_lt _ (by decide)⟩

@[simp] theorem edgeCore_segment : ∀ e i, edgeCore (segmentEdge e i) = e := by decide
@[simp] theorem edgePart_segment : ∀ e i, edgePart (segmentEdge e i) = i := by decide
@[simp] theorem segment_decompose : ∀ e, segmentEdge (edgeCore e) (edgePart e) = e := by decide

@[simp] theorem source_segment0 : ∀ e, subdividedGraph.source (segmentEdge e 0) =
    oldVertex (coreGraph.source e) := by decide
@[simp] theorem target_segment0 : ∀ e, subdividedGraph.target (segmentEdge e 0) =
    middleVertex e 0 := by decide
@[simp] theorem source_segment1 : ∀ e, subdividedGraph.source (segmentEdge e 1) =
    middleVertex e 0 := by decide
@[simp] theorem target_segment1 : ∀ e, subdividedGraph.target (segmentEdge e 1) =
    middleVertex e 1 := by decide
@[simp] theorem source_segment2 : ∀ e, subdividedGraph.source (segmentEdge e 2) =
    middleVertex e 1 := by decide
@[simp] theorem target_segment2 : ∀ e, subdividedGraph.target (segmentEdge e 2) =
    oldVertex (coreGraph.target e) := by decide

/-- The two trisection points. -/
def third1 : unitInterval := ⟨1 / 3, by constructor <;> norm_num⟩
def third2 : unitInterval := ⟨2 / 3, by constructor <;> norm_num⟩

/-- Send the parameter on subedge `i` to `(s+i)/3`. -/
def affine (i : Fin 3) (s : unitInterval) : unitInterval :=
  ⟨((s : ℝ) + i.val) / 3, by
    have hi0 : (0 : ℝ) ≤ i.val := Nat.cast_nonneg _
    have hi2 : (i.val : ℝ) ≤ 2 := by exact_mod_cast (show i.val ≤ 2 by omega)
    constructor <;> linarith [s.property.1, s.property.2]⟩

@[simp] theorem affine00 : affine 0 0 = 0 := by ext; norm_num [affine]
@[simp] theorem affine01 : affine 0 1 = third1 := by ext; norm_num [affine, third1]
@[simp] theorem affine10 : affine 1 0 = third1 := by ext; norm_num [affine, third1]
@[simp] theorem affine11 : affine 1 1 = third2 := by ext; norm_num [affine, third2]
@[simp] theorem affine20 : affine 2 0 = third2 := by ext; norm_num [affine, third2]
@[simp] theorem affine21 : affine 2 1 = 1 := by ext; norm_num [affine]

theorem continuous_affine (i : Fin 3) : Continuous (affine i) := by
  apply Continuous.subtype_mk
  fun_prop

/-- On inserted vertices the forward map uses the appropriate trisection point. -/
def vertexImage (v : Vertex) : coreGraph.Realization :=
  if h : v.val < 6 then coreGraph.vertex ⟨v.val, h⟩ else
    coreGraph.edge ⟨(v.val - 6) / 2, by omega⟩
      (if (v.val - 6) % 2 = 0 then third1 else third2)

@[simp] theorem vertexImage_old (v : CoreVertex) :
    vertexImage (oldVertex v) = coreGraph.vertex v := by fin_cases v <;> rfl
@[simp] theorem vertexImage_middle0 (e : CoreEdge) :
    vertexImage (middleVertex e 0) = coreGraph.edge e third1 := by fin_cases e <;> rfl
@[simp] theorem vertexImage_middle1 (e : CoreEdge) :
    vertexImage (middleVertex e 1) = coreGraph.edge e third2 := by fin_cases e <;> rfl

def edgeImage (e : Edge) (s : unitInterval) : coreGraph.Realization :=
  coreGraph.edge (edgeCore e) (affine (edgePart e) s)

@[simp] theorem edgeImage_segment (e : CoreEdge) (i : Fin 3) (s : unitInterval) :
    edgeImage (segmentEdge e i) s = coreGraph.edge e (affine i s) := by simp [edgeImage]

@[simp] theorem edgeImage_zero (e : Edge) :
    edgeImage e 0 = vertexImage (subdividedGraph.source e) := by
  rw [← segment_decompose e]
  generalize edgeCore e = k
  generalize edgePart e = i
  fin_cases i <;> simp

@[simp] theorem edgeImage_one (e : Edge) :
    edgeImage e 1 = vertexImage (subdividedGraph.target e) := by
  rw [← segment_decompose e]
  generalize edgeCore e = k
  generalize edgePart e = i
  fin_cases i <;> simp

def forwardRaw : subdividedGraph.PreRealization → coreGraph.Realization
  | Sum.inl v => vertexImage v
  | Sum.inr (e, s) => edgeImage e s

theorem forwardRaw_attaching {x y : subdividedGraph.PreRealization}
    (h : subdividedGraph.Attaching x y) : forwardRaw x = forwardRaw y := by
  rcases h with ⟨e, rfl, rfl⟩ | ⟨e, rfl, rfl⟩ <;> simp [forwardRaw]

theorem forwardRaw_equivalent {x y : subdividedGraph.PreRealization}
    (h : subdividedGraph.realizationSetoid x y) : forwardRaw x = forwardRaw y := by
  induction h with
  | rel _ _ h => exact forwardRaw_attaching h
  | refl _ => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ hxy hyz => exact hxy.trans hyz

/-- The forward map on the actual graph quotient. -/
def forward : subdividedGraph.Realization → coreGraph.Realization :=
  Quotient.lift forwardRaw fun _ _ h => forwardRaw_equivalent h

@[simp] theorem forward_vertex (v : Vertex) :
    forward (subdividedGraph.vertex v) = vertexImage v := rfl
@[simp] theorem forward_edge (e : Edge) (s : unitInterval) :
    forward (subdividedGraph.edge e s) = edgeImage e s := rfl

theorem continuous_forwardRaw : Continuous forwardRaw := by
  apply continuous_sum_dom.2
  constructor
  · exact continuous_of_discreteTopology
  · apply continuous_prod_of_discrete_left.2
    intro e
    exact (coreGraph.continuous_edge (edgeCore e)).comp (continuous_affine (edgePart e))

theorem continuous_forward : Continuous forward :=
  continuous_forwardRaw.quotient_lift _

/-- Reparameterize the `i`-th third back to a whole unit interval, constantly
extending outside that third.  Clamping permits the closed pasting argument. -/
def rescale (i : Fin 3) (s : unitInterval) : unitInterval :=
  Set.projIcc 0 1 zero_le_one (3 * (s : ℝ) - i.val)

theorem continuous_rescale (i : Fin 3) : Continuous (rescale i) := by
  apply continuous_projIcc.comp
  fun_prop

@[simp] theorem rescale00 : rescale 0 0 = 0 := by ext; norm_num [rescale, Set.coe_projIcc]
@[simp] theorem rescale01 : rescale 0 third1 = 1 := by ext; norm_num [rescale, third1, Set.coe_projIcc]
@[simp] theorem rescale10 : rescale 1 third1 = 0 := by ext; norm_num [rescale, third1, Set.coe_projIcc]
@[simp] theorem rescale11 : rescale 1 third2 = 1 := by ext; norm_num [rescale, third2, Set.coe_projIcc]
@[simp] theorem rescale20 : rescale 2 third2 = 0 := by ext; norm_num [rescale, third2, Set.coe_projIcc]
@[simp] theorem rescale21 : rescale 2 1 = 1 := by ext; norm_num [rescale, Set.coe_projIcc]

/-- Traverse the three subedges in order, with breakpoints at one and two thirds. -/
def reverseEdge (e : CoreEdge) (s : unitInterval) : subdividedGraph.Realization :=
  if (s : ℝ) ≤ 1 / 3 then subdividedGraph.edge (segmentEdge e 0) (rescale 0 s)
  else if (s : ℝ) ≤ 2 / 3 then subdividedGraph.edge (segmentEdge e 1) (rescale 1 s)
  else subdividedGraph.edge (segmentEdge e 2) (rescale 2 s)

theorem continuous_reverseEdge (e : CoreEdge) : Continuous (reverseEdge e) := by
  have h0 := (subdividedGraph.continuous_edge (segmentEdge e 0)).comp (continuous_rescale 0)
  have h1 := (subdividedGraph.continuous_edge (segmentEdge e 1)).comp (continuous_rescale 1)
  have h2 := (subdividedGraph.continuous_edge (segmentEdge e 2)).comp (continuous_rescale 2)
  have h12 : Continuous (fun s : unitInterval =>
      if (s : ℝ) ≤ 2 / 3 then subdividedGraph.edge (segmentEdge e 1) (rescale 1 s)
      else subdividedGraph.edge (segmentEdge e 2) (rescale 2 s)) := by
    apply h1.if_le h2 continuous_subtype_val continuous_const
    intro s hs
    have ht : s = third2 := Subtype.ext hs
    subst s
    simp
  apply h0.if_le h12 continuous_subtype_val continuous_const
  intro s hs
  have ht : s = third1 := Subtype.ext hs
  subst s
  have hle : (third1 : ℝ) ≤ 2 / 3 := by norm_num [third1]
  simp [hle]

@[simp] theorem reverseEdge_zero (e : CoreEdge) :
    reverseEdge e 0 = subdividedGraph.vertex (oldVertex (coreGraph.source e)) := by
  norm_num [reverseEdge]

@[simp] theorem reverseEdge_one (e : CoreEdge) :
    reverseEdge e 1 = subdividedGraph.vertex (oldVertex (coreGraph.target e)) := by
  norm_num [reverseEdge]

def reverseRaw : coreGraph.PreRealization → subdividedGraph.Realization
  | Sum.inl v => subdividedGraph.vertex (oldVertex v)
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

/-- The inverse subdivision map on the actual graph quotient. -/
def reverse : coreGraph.Realization → subdividedGraph.Realization :=
  Quotient.lift reverseRaw fun _ _ h => reverseRaw_equivalent h

@[simp] theorem reverse_vertex (v : CoreVertex) :
    reverse (coreGraph.vertex v) = subdividedGraph.vertex (oldVertex v) := rfl
@[simp] theorem reverse_edge (e : CoreEdge) (s : unitInterval) :
    reverse (coreGraph.edge e s) = reverseEdge e s := rfl

theorem continuous_reverseRaw : Continuous reverseRaw := by
  apply continuous_sum_dom.2
  constructor
  · exact continuous_of_discreteTopology
  · apply continuous_prod_of_discrete_left.2
    exact continuous_reverseEdge

theorem continuous_reverse : Continuous reverse :=
  continuous_reverseRaw.quotient_lift _

/-- On its own third, rescaling exactly inverts the affine parametrization. -/
@[simp] theorem rescale_affine (i : Fin 3) (s : unitInterval) :
    rescale i (affine i s) = s := by
  have h : 3 * (affine i s : ℝ) - i.val = (s : ℝ) := by
    simp only [affine]
    ring
  unfold rescale
  rw [h]
  exact Set.projIcc_val zero_le_one s

/-- In the closed `i`-th third, the affine parametrization inverts rescaling. -/
theorem affine_rescale (i : Fin 3) (s : unitInterval)
    (hlo : (i.val : ℝ) / 3 ≤ s) (hhi : (s : ℝ) ≤ (i.val + 1) / 3) :
    affine i (rescale i s) = s := by
  have hmem : 3 * (s : ℝ) - i.val ∈ Set.Icc (0 : ℝ) 1 := by
    constructor <;> linarith
  apply Subtype.ext
  change ((Set.projIcc 0 1 zero_le_one (3 * (s : ℝ) - i.val) : ℝ) + i.val) / 3 = s
  rw [Set.projIcc_of_mem zero_le_one hmem]
  ring

/-- The forward map after the reverse edge path is the original core edge. -/
theorem forward_reverseEdge (e : CoreEdge) (s : unitInterval) :
    forward (reverseEdge e s) = coreGraph.edge e s := by
  unfold reverseEdge
  split_ifs with h0 h1
  · simp only [forward_edge, edgeImage_segment]
    apply congrArg (coreGraph.edge e)
    apply affine_rescale
    · norm_num
      exact s.property.1
    · norm_num
      exact h0
  · simp only [forward_edge, edgeImage_segment]
    apply congrArg (coreGraph.edge e)
    apply affine_rescale
    · norm_num
      linarith
    · norm_num
      exact h1
  · simp only [forward_edge, edgeImage_segment]
    apply congrArg (coreGraph.edge e)
    apply affine_rescale
    · norm_num
      linarith
    · norm_num
      exact s.property.2

/-- Conversely each subdivided edge is recovered, including its glued endpoints. -/
theorem reverse_affine (e : CoreEdge) (i : Fin 3) (s : unitInterval) :
    reverseEdge e (affine i s) = subdividedGraph.edge (segmentEdge e i) s := by
  fin_cases i
  · change reverseEdge e (affine 0 s) = subdividedGraph.edge (segmentEdge e 0) s
    have h0 : (affine 0 s : ℝ) ≤ 1 / 3 := by
      simp only [affine, Fin.val_zero, Nat.cast_zero, add_zero]
      linarith [s.property.2]
    simp only [reverseEdge, if_pos h0, rescale_affine]
  · change reverseEdge e (affine 1 s) = subdividedGraph.edge (segmentEdge e 1) s
    have h1 : (affine 1 s : ℝ) ≤ 2 / 3 := by
      norm_num [affine]
      linarith [s.property.2]
    by_cases h0 : (affine 1 s : ℝ) ≤ 1 / 3
    · have hs : s = 0 := by
        apply Subtype.ext
        change (s : ℝ) = 0
        norm_num [affine] at h0
        linarith [s.property.1]
      subst s
      have hle : (third1 : ℝ) ≤ 1 / 3 := by norm_num [third1]
      rw [affine10]
      unfold reverseEdge
      rw [if_pos hle, rescale01]
      simp only [GraphIncidence.edge_one, target_segment0,
        GraphIncidence.edge_zero, source_segment1]
    · simp only [reverseEdge, if_neg h0, if_pos h1, rescale_affine]
  · change reverseEdge e (affine 2 s) = subdividedGraph.edge (segmentEdge e 2) s
    have h0 : ¬(affine 2 s : ℝ) ≤ 1 / 3 := by
      norm_num [affine]
      linarith [s.property.1]
    by_cases h1 : (affine 2 s : ℝ) ≤ 2 / 3
    · have hs : s = 0 := by
        apply Subtype.ext
        change (s : ℝ) = 0
        norm_num [affine] at h1
        linarith [s.property.1]
      subst s
      have hgt : ¬(third2 : ℝ) ≤ 1 / 3 := by norm_num [third2]
      have hle : (third2 : ℝ) ≤ 2 / 3 := by norm_num [third2]
      rw [affine20]
      unfold reverseEdge
      rw [if_neg hgt, if_pos hle, rescale11]
      simp only [GraphIncidence.edge_one, target_segment1,
        GraphIncidence.edge_zero, source_segment2]
    · simp only [reverseEdge, if_neg h0, if_neg h1, rescale_affine]

/-- Every subdivided vertex is either original or one of the two inserted vertices. -/
theorem vertex_cases : ∀ v : Vertex,
    (∃ w, v = oldVertex w) ∨ (∃ e i, v = middleVertex e i) := by decide

theorem reverse_vertexImage (v : Vertex) :
    reverse (vertexImage v) = subdividedGraph.vertex v := by
  rcases vertex_cases v with ⟨w, rfl⟩ | ⟨e, i, rfl⟩
  · simp
  · fin_cases i
    · change reverse (vertexImage (middleVertex e 0)) = subdividedGraph.vertex (middleVertex e 0)
      rw [vertexImage_middle0, reverse_edge]
      simpa only [affine01, GraphIncidence.edge_one, target_segment0] using reverse_affine e 0 1
    · change reverse (vertexImage (middleVertex e 1)) = subdividedGraph.vertex (middleVertex e 1)
      rw [vertexImage_middle1, reverse_edge]
      simpa only [affine11, GraphIncidence.edge_one, target_segment1] using reverse_affine e 1 1

/-- Both composites are proved on representatives of the actual quotient graph. -/
theorem forward_reverse (x : coreGraph.Realization) : forward (reverse x) = x := by
  refine Quotient.inductionOn x ?_
  rintro (v | ⟨e, s⟩)
  · change forward (reverse (coreGraph.vertex v)) = coreGraph.vertex v
    simp
  · exact forward_reverseEdge e s

theorem reverse_forward (x : subdividedGraph.Realization) : reverse (forward x) = x := by
  refine Quotient.inductionOn x ?_
  rintro (v | ⟨e, s⟩)
  · exact reverse_vertexImage v
  · change reverse (coreGraph.edge (edgeCore e) (affine (edgePart e) s)) =
      subdividedGraph.edge e s
    rw [reverse_edge, reverse_affine, segment_decompose]

/-- Explicit homeomorphism from the subdivided graph back to the original graph. -/
def realizationHomeomorph : subdividedGraph.Realization ≃ₜ coreGraph.Realization where
  toFun := forward
  invFun := reverse
  left_inv := reverse_forward
  right_inv := forward_reverse
  continuous_toFun := continuous_forward
  continuous_invFun := continuous_reverse

/-- Subdivision preserves every ordered, labelled configuration space. -/
def configurationHomeomorph (n : ℕ) :
    OrderedConfiguration n subdividedGraph.Realization ≃ₜ
      OrderedConfiguration n coreGraph.Realization :=
  OrderedConfiguration.homeomorph realizationHomeomorph

/-- In particular, the paper's four-particle original configuration space. -/
def fourConfigurationHomeomorph :
    OrderedConfiguration 4 subdividedGraph.Realization ≃ₜ SourceConfigurationSpace :=
  configurationHomeomorph 4

/-- The induced isomorphism in integral singular homology, in every degree. -/
def configurationHomologyIso (q n : ℕ) :
    IntegralHomology q (OrderedConfiguration n subdividedGraph.Realization) ≅
      IntegralHomology q (OrderedConfiguration n coreGraph.Realization) :=
  integralHomologyHomeomorph q (configurationHomeomorph n)

/-- Degree two of the four-particle space is the paper's original homology target. -/
def sourceHomologyIso :
    IntegralHomology 2 (OrderedConfiguration 4 subdividedGraph.Realization) ≅ SourceHomology :=
  configurationHomologyIso 2 4

/-- The same singular-homology isomorphism as an additive equivalence, ready
for transporting the exact additive order of a homology class. -/
def sourceHomologyEquiv :
    IntegralHomology 2 (OrderedConfiguration 4 subdividedGraph.Realization) ≃+ SourceHomology :=
by
  letI : Module ℤ (IntegralHomology 2 (OrderedConfiguration 4 subdividedGraph.Realization)) :=
    (IntegralHomology 2 (OrderedConfiguration 4 subdividedGraph.Realization)).isModule
  letI : Module ℤ SourceHomology := SourceHomology.isModule
  exact sourceHomologyIso.toLinearEquiv.toAddEquiv

/-- The subdivision step alone preserves the exact order-six conclusion. -/
theorem orderSix_subdivision_iff :
    (∃ z : IntegralHomology 2 (OrderedConfiguration 4 subdividedGraph.Realization),
      addOrderOf z = 6) ↔ MainTheoremStatement := by
  change (∃ z : IntegralHomology 2 (OrderedConfiguration 4 subdividedGraph.Realization),
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
end Paper23.Subdivision
