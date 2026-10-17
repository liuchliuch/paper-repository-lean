import Paper27.Geometry.PuncturedSectionRemovability

/-!
# Restricting actual normal atlases to smaller actual neighbourhoods

The forward and inverse chart functions do not change. Only their open source
and target are restricted. Thus normal slices and actual derivative quotients
remain the same germs, while the splittings and action can live on a common
smaller invariant neighbourhood.
-/
noncomputable section
open scoped Manifold Topology
open Filter
namespace Paper27.Geometry.RetractionCoordinateGerms.NormalAtlas
variable {X : CompactComplexSurface} {D : EmbeddedCurve X}
  {U W : D.Neighbourhood} {r₁ r₂ : D.Retraction U} {n : ℕ}
  (A : RetractionCoordinateGerms.NormalAtlas D U r₁ r₂ n)

/-- Restrict actual charts and actual retractions to a smaller neighbourhood. -/
def restrict (r s : D.Retraction W) (hr : r.toFun = r₁.toFun) (hs : s.toFun = r₂.toFun) :
    RetractionCoordinateGerms.NormalAtlas D W r s n where
  chart i p :=
    { coordinates := (A.chart i p).coordinates.restrOpen W.domain W.open_domain
      r_source := fun x hx => by rw [hr]; exact (A.chart i p).r_source x hx.1
      s_source := fun x hx => by rw [hs]; exact (A.chart i p).s_source x hx.1
      r_normal := fun x hx => by rw [hr]; exact (A.chart i p).r_normal x hx.1
      s_normal := fun x hx => by rw [hs]; exact (A.chart i p).s_normal x hx.1 }
  source_mem i p hi := ⟨A.source_mem i p hi, W.contains p⟩
  centre i p hi := A.centre i p hi
  source_subset _ _ _ hx := hx.2
  holomorphic i p := (A.holomorphic i p).mono (fun _ hx => hx.1)
  inverse_holomorphic i p := (A.inverse_holomorphic i p).mono (fun _ hx => hx.1)

 theorem restrict_chart_apply (r s : D.Retraction W)
    (hr : r.toFun = r₁.toFun) (hs : s.toFun = r₂.toFun) (i p : D.curve) (x : X) :
    ((A.restrict r s hr hs).chart i p).coordinates x = (A.chart i p).coordinates x := rfl

 theorem restrict_chart_symm_apply (r s : D.Retraction W)
    (hr : r.toFun = r₁.toFun) (hs : s.toFun = r₂.toFun) (i p : D.curve) (z : ℂ × ℂ) :
    ((A.restrict r s hr hs).chart i p).coordinates.symm z = (A.chart i p).coordinates.symm z := rfl

 theorem restrict_slice (r s : D.Retraction W)
    (hr : r.toFun = r₁.toFun) (hs : s.toFun = r₂.toFun) (i p : D.curve) :
    (A.restrict r s hr hs).slice i p = A.slice i p := rfl

 theorem restrict_third (r s : D.Retraction W)
    (hr : r.toFun = r₁.toFun) (hs : s.toFun = r₂.toFun)
    (t : D.Retraction W) (r₃ : D.Retraction U) (ht : t.toFun = r₃.toFun) (i p : D.curve) :
    (A.restrict r s hr hs).third t i p = A.third r₃ i p := by
  funext z
  change (chartAt ℂ i) (t.toFun (A.slice i p z)) - (chartAt ℂ i) p = _
  rw [ht]
  rfl

 theorem restrict_coordinate (r s : D.Retraction W)
    (hr : r.toFun = r₁.toFun) (hs : s.toFun = r₂.toFun)
    (t : D.Retraction W) (r₃ : D.Retraction U) (ht : t.toFun = r₃.toFun) (i p : D.curve) :
    (A.restrict r s hr hs).coordinate t i p = A.coordinate r₃ i p := by
  funext z
  change (chartAt ℂ i) (t.toFun ((A.chart i p).coordinates.symm z)) = _
  rw [ht]
  rfl

 theorem restrict_verticalSplitting (r s : D.Retraction W)
    (hr : r.toFun = r₁.toFun) (hs : s.toFun = r₂.toFun)
    (t : D.Retraction W) (r₃ : D.Retraction U) (ht : t.toFun = r₃.toFun) (i p : D.curve) :
    (A.restrict r s hr hs).verticalSplitting t i p = A.verticalSplitting r₃ i p := by
  funext y
  simp only [verticalSplitting, horizontalPartial, normalPartial,
    A.restrict_coordinate r s hr hs t r₃ ht i p]

end Paper27.Geometry.RetractionCoordinateGerms.NormalAtlas
