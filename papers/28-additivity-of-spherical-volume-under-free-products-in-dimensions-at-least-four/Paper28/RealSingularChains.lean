import Paper28.OrderedSimplicialChains
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Actual continuous and Lipschitz singular simplices on the standard
real barycentric simplex. Their ordinary integer chain complexes are the
native alternating face complexes of the free abelian groups. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open CategoryTheory Set
open scoped Simplicial

theorem simplexCoordinateMap_lipschitz {α β : Type*} [Fintype α] [Fintype β] (f : α → β) :
    ∃ L : NNReal, LipschitzWith L (stdSimplex.map (S := ℝ) f) := by
  let F : (α → ℝ) →L[ℝ] (β → ℝ) := (FunOnFinite.linearMap ℝ ℝ f).toContinuousLinearMap
  refine ⟨‖F‖₊,LipschitzWith.of_dist_le_mul ?_⟩
  intro x y
  exact F.lipschitz.dist_le_mul x.val y.val

def simplexCoordinateMap {α β : Type*} [Fintype α] [Fintype β] (f : α → β) :
    C(stdSimplex ℝ α,stdSimplex ℝ β) :=
  ⟨stdSimplex.map f,(simplexCoordinateMap_lipschitz f).choose_spec.continuous⟩

def realSingularSSet (Y : Type*) [TopologicalSpace Y] : SSet where
  obj n := C(stdSimplex ℝ (Fin (n.unop.len+1)),Y)
  map f := fun σ => σ.comp (simplexCoordinateMap f.unop.toOrderHom)
  map_id _ := by
    funext σ
    apply ContinuousMap.ext
    intro x
    change σ (stdSimplex.map id x) = σ x
    exact congrArg σ (stdSimplex.map_id_apply x)
  map_comp f g := by
    funext σ
    apply ContinuousMap.ext
    intro x
    exact congrArg σ (stdSimplex.map_comp_apply (fun i => g.unop.toOrderHom i)
      (fun i => f.unop.toOrderHom i) x).symm

abbrev LipschitzSingularSimplex (Y : Type*) [MetricSpace Y] (k : ℕ) :=
  {σ : C(stdSimplex ℝ (Fin (k+1)),Y) // ∃ L : NNReal, LipschitzWith L σ}

def lipschitzSingularRestrict {Y : Type*} [MetricSpace Y] {n m : ℕ}
    (f : Fin (m+1) → Fin (n+1)) (σ : LipschitzSingularSimplex Y n) : LipschitzSingularSimplex Y m := by
  refine ⟨σ.val.comp (simplexCoordinateMap f),?_⟩
  obtain ⟨L,hL⟩ := σ.property
  obtain ⟨M,hM⟩ := simplexCoordinateMap_lipschitz f
  exact ⟨L*M,hL.comp hM⟩

def lipschitzSingularSSet (Y : Type*) [MetricSpace Y] : SSet where
  obj n := LipschitzSingularSimplex Y n.unop.len
  map f := fun σ => lipschitzSingularRestrict f.unop.toOrderHom σ
  map_id _ := by
    funext σ
    apply Subtype.ext
    apply ContinuousMap.ext
    intro x
    change σ.val (stdSimplex.map id x) = σ.val x
    exact congrArg σ.val (stdSimplex.map_id_apply x)
  map_comp f g := by
    funext σ
    apply Subtype.ext
    apply ContinuousMap.ext
    intro x
    change σ.val (stdSimplex.map (fun i => f.unop.toOrderHom (g.unop.toOrderHom i)) x) =
      σ.val (stdSimplex.map f.unop.toOrderHom (stdSimplex.map g.unop.toOrderHom x))
    exact congrArg σ.val (stdSimplex.map_comp_apply (fun i => g.unop.toOrderHom i)
      (fun i => f.unop.toOrderHom i) x).symm

def forgetLipschitzSingular (Y : Type*) [MetricSpace Y] : lipschitzSingularSSet Y ⟶ realSingularSSet Y where
  app _ := Subtype.val
  naturality _ _ _ := rfl

def freeSSetChainComplex (X : SSet) : ChainComplex AddCommGrpCat ℕ :=
  (AlgebraicTopology.alternatingFaceMapComplex AddCommGrpCat).obj (X ⋙ AddCommGrpCat.free)

def freeSSetChainMap {X Y : SSet} (f : X ⟶ Y) : freeSSetChainComplex X ⟶ freeSSetChainComplex Y :=
  (AlgebraicTopology.alternatingFaceMapComplex AddCommGrpCat).map
    (Functor.whiskerRight f AddCommGrpCat.free)

abbrev realSingularChainComplex (Y : Type*) [TopologicalSpace Y] := freeSSetChainComplex (realSingularSSet Y)
abbrev lipschitzSingularChainComplex (Y : Type*) [MetricSpace Y] := freeSSetChainComplex (lipschitzSingularSSet Y)

def forgetLipschitzSingularChainMap (Y : Type*) [MetricSpace Y] :
    lipschitzSingularChainComplex Y ⟶ realSingularChainComplex Y := freeSSetChainMap (forgetLipschitzSingular Y)

end Paper28
