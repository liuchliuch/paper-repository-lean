import Paper28.SphericalChartEmbedding

/-! Exact intrinsic finite-cell metric data on one connected component:
distance is the infimum of the lengths of actual finite spherical cell
chains. The one-cell upper bound and global Lipschitz consequence are
proved from that formula, not supplied as realization estimates. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Set
universe w
variable {V Idx : Type*} [Fintype V] [DecidableEq V] [Fintype Idx]
  {d : ℕ} {K : FiniteEuclideanComplex (EuclideanAmbient d)}
  {B : FullSubcomplexBarycentricAtlas K V Idx} {Y : Type w} [MetricSpace Y]

structure SphericalCellStep (C : FullSubcomplexSphericalCharts B Y) (x y : Y) where
  cell : Idx
  left : EuclideanAmbient (C.dimension cell)
  right : EuclideanAmbient (C.dimension cell)
  left_mem : left ∈ closedSphericalPatch (C.vertex cell) (B.cells cell ∩ B.selected)
  right_mem : right ∈ closedSphericalPatch (C.vertex cell) (B.cells cell ∩ B.selected)
  left_eq : C.chart cell left = x
  right_eq : C.chart cell right = y

inductive SphericalCellPath (C : FullSubcomplexSphericalCharts B Y) : Y → Y → Type _
  | nil (x : Y) : SphericalCellPath C x x
  | cons {x y z : Y} (step : SphericalCellStep C x y) (rest : SphericalCellPath C y z) : SphericalCellPath C x z

def SphericalCellPath.length {C : FullSubcomplexSphericalCharts B Y} {x y : Y} : SphericalCellPath C x y → ℝ
  | .nil _ => 0
  | .cons step rest => angular step.left step.right+rest.length

theorem SphericalCellPath.length_nonneg {C : FullSubcomplexSphericalCharts B Y} {x y : Y}
    (p : SphericalCellPath C x y) : 0 ≤ p.length := by
  induction p with
  | nil => exact le_rfl
  | cons step rest ih => exact add_nonneg (Real.arccos_nonneg _) ih

def sphericalCellPathLengths (C : FullSubcomplexSphericalCharts B Y) (x y : Y) : Set ℝ :=
  Set.range (fun p : SphericalCellPath C x y => p.length)

structure SphericalCellPathMetricInput (C : FullSubcomplexSphericalCharts B Y) : Prop where
  path_exists : ∀ x y, Nonempty (SphericalCellPath C x y)
  distance_formula : ∀ x y, dist x y = sInf (sphericalCellPathLengths C x y)

theorem spherical_cell_distance_le_angle (C : FullSubcomplexSphericalCharts B Y)
    (M : SphericalCellPathMetricInput C) (j : Idx) (u v : EuclideanAmbient (C.dimension j))
    (hu : u ∈ closedSphericalPatch (C.vertex j) (B.cells j ∩ B.selected))
    (hv : v ∈ closedSphericalPatch (C.vertex j) (B.cells j ∩ B.selected)) :
    dist (C.chart j u) (C.chart j v) ≤ angular u v := by
  rw [M.distance_formula]
  apply csInf_le
  · exact ⟨0,by rintro r ⟨p,rfl⟩; exact p.length_nonneg⟩
  · exact ⟨SphericalCellPath.cons ⟨j,u,v,hu,hv,rfl,rfl⟩ (.nil _),by simp [SphericalCellPath.length]⟩

theorem spherical_cell_path_map_bound {C : FullSubcomplexSphericalCharts B Y}
    {Z : Type*} [PseudoMetricSpace Z] (f : Y → Z) (L : ℝ)
    (hCell : ∀ j u v, u ∈ closedSphericalPatch (C.vertex j) (B.cells j ∩ B.selected) →
      v ∈ closedSphericalPatch (C.vertex j) (B.cells j ∩ B.selected) →
      dist (f (C.chart j u)) (f (C.chart j v)) ≤ L*angular u v)
    {x y : Y} (p : SphericalCellPath C x y) : dist (f x) (f y) ≤ L*p.length := by
  induction p with
  | nil => simp [SphericalCellPath.length]
  | @cons x y z step rest ih =>
      have hs := hCell step.cell step.left step.right step.left_mem step.right_mem
      rw [step.left_eq,step.right_eq] at hs
      calc
        _ ≤ dist (f x) (f y)+dist (f y) (f z) := dist_triangle _ _ _
        _ ≤ L*angular step.left step.right+L*rest.length := add_le_add hs ih
        _ = L*(SphericalCellPath.cons step rest).length := by dsimp [SphericalCellPath.length]; ring

theorem lipschitz_of_spherical_cell_bounds (C : FullSubcomplexSphericalCharts B Y)
    (M : SphericalCellPathMetricInput C) {Z : Type*} [PseudoMetricSpace Z]
    (f : Y → Z) (L : NNReal) (hL : 0 < (L : ℝ))
    (hCell : ∀ j u v, u ∈ closedSphericalPatch (C.vertex j) (B.cells j ∩ B.selected) →
      v ∈ closedSphericalPatch (C.vertex j) (B.cells j ∩ B.selected) →
      dist (f (C.chart j u)) (f (C.chart j v)) ≤ (L : ℝ)*angular u v) : LipschitzWith L f := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  obtain ⟨p⟩ := M.path_exists x y
  have hInf : dist (f x) (f y)/(L : ℝ) ≤ sInf (sphericalCellPathLengths C x y) := by
    apply le_csInf (show (sphericalCellPathLengths C x y).Nonempty from ⟨p.length,⟨p,rfl⟩⟩)
    rintro r ⟨q,rfl⟩
    apply (div_le_iff₀ hL).mpr
    simpa only [mul_comm] using spherical_cell_path_map_bound f L hCell q
  rw [← M.distance_formula] at hInf
  simpa only [mul_comm] using (div_le_iff₀ hL).mp hInf

end Paper28
