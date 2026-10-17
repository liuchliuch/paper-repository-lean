import Mathlib.Probability.Independence.InfinitePi
import Mathlib.MeasureTheory.Constructions.Pi

open MeasureTheory ProbabilityTheory Finset BigOperators Classical
noncomputable section
namespace Paper09.ProductCoordinates

/-- Distinct coordinates of an actual infinite product have exactly the
corresponding finite product distribution. -/
theorem infinitePi_map_injective {J I X : Type*} [Fintype I]
    [MeasurableSpace X] (μ : J → Measure X) [∀ j, IsProbabilityMeasure (μ j)]
    (f : I → J) (hf : Function.Injective f) :
    (Measure.infinitePi μ).map (fun x i => x (f i)) =
      Measure.pi (fun i => μ (f i)) := by
  have hind := (iIndepFun_infinitePi (μ := μ) (X := fun _ (x : X) => x)
    (fun _ => measurable_id)).precomp hf
  have hh := (iIndepFun_iff_map_fun_eq_pi_map
    (fun i : I => (measurable_pi_apply (f i)).aemeasurable)).mp hind
  have heval : ∀ i : I, (Measure.infinitePi μ).map (fun x => x (f i)) = μ (f i) :=
    fun i => (measurePreserving_eval_infinitePi μ (f i)).map_eq
  simpa only [heval] using hh

/-- Flattening independent finite coordinate groups is measure preserving.
This proves group independence from site independence, including non-rectangular
measurable events within a group. -/
theorem pi_map_uncurry {I X : Type*} {K : I → Type*}
    [Fintype I] [∀ i, Fintype (K i)] [MeasurableSpace X]
    (μ : (i : I) → K i → Measure X) [∀ i k, IsProbabilityMeasure (μ i k)] :
    (Measure.pi (fun i => Measure.pi (μ i))).map
      (fun x (p : Sigma K) => x p.1 p.2) =
        Measure.pi (fun p : Sigma K => μ p.1 p.2) := by
  symm
  apply Measure.pi_eq
  intro s hs
  rw [Measure.map_apply (by fun_prop) (MeasurableSet.univ_pi hs)]
  have hpre : (fun x (p : Sigma K) => x p.1 p.2) ⁻¹' (Set.univ.pi s) =
      Set.univ.pi (fun i => Set.univ.pi (fun k => s ⟨i,k⟩)) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_const]
    exact ⟨fun h i k => h ⟨i,k⟩, fun h p => h p.1 p.2⟩
  rw [hpre, Measure.pi_pi]
  simp_rw [Measure.pi_pi]
  exact (Fintype.prod_sigma (fun p : Sigma K => μ p.1 p.2 (s p))).symm

/-- The converse grouping map, derived from the actual flattening equality. -/
theorem pi_map_curry {I X : Type*} {K : I → Type*}
    [Fintype I] [∀ i, Fintype (K i)] [MeasurableSpace X]
    (μ : (i : I) → K i → Measure X) [∀ i k, IsProbabilityMeasure (μ i k)] :
    (Measure.pi (fun p : Sigma K => μ p.1 p.2)).map
      (fun x i k => x ⟨i,k⟩) = Measure.pi (fun i => Measure.pi (μ i)) := by
  rw [← pi_map_uncurry μ, Measure.map_map (by fun_prop) (by fun_prop)]
  change Measure.map id (Measure.pi (fun i => Measure.pi (μ i))) = _
  exact Measure.map_id

/-- Disjoint finite coordinate groups cut out of the full environment have
an actual product joint law; no independence certificate is assumed. -/
theorem infinitePi_map_groups {J I X : Type*} {K : I → Type*}
    [Fintype I] [∀ i, Fintype (K i)] [MeasurableSpace X]
    (μ : J → Measure X) [∀ j, IsProbabilityMeasure (μ j)]
    (f : Sigma K → J) (hf : Function.Injective f) :
    (Measure.infinitePi μ).map (fun x i k => x (f ⟨i,k⟩)) =
      Measure.pi (fun i => Measure.pi (fun k => μ (f ⟨i,k⟩))) := by
  have h := congrArg (fun ν : Measure (Sigma K → X) =>
    ν.map (fun x i k => x ⟨i,k⟩)) (infinitePi_map_injective μ f hf)
  dsimp only at h
  rw [Measure.map_map (by fun_prop) (by fun_prop)] at h
  have hc := pi_map_curry (fun i k => μ (f ⟨i,k⟩))
  simpa only [Function.comp_def] using h.trans hc

/-- Pair independent fields and independent auxiliary variables at distinct
sites of their actual product law. -/
theorem product_infinitePi_map_pairs {J I X Y : Type*} [Fintype I]
    [MeasurableSpace X] [MeasurableSpace Y]
    (μ : J → Measure X) (ν : J → Measure Y)
    [∀ j, IsProbabilityMeasure (μ j)] [∀ j, IsProbabilityMeasure (ν j)]
    (f : I → J) (hf : Function.Injective f) :
    ((Measure.infinitePi μ).prod (Measure.infinitePi ν)).map
      (fun z i => (z.1 (f i), z.2 (f i))) =
      Measure.pi (fun i => (μ (f i)).prod (ν (f i))) := by
  have hprod := Measure.map_prod_map (Measure.infinitePi μ) (Measure.infinitePi ν)
    (f := fun x i => x (f i)) (g := fun x i => x (f i))
    (by fun_prop) (by fun_prop)
  rw [infinitePi_map_injective μ f hf, infinitePi_map_injective ν f hf] at hprod
  have he := (measurePreserving_arrowProdEquivProdArrow X Y I
    (fun i => μ (f i)) (fun i => ν (f i))).symm.map_eq
  rw [hprod, Measure.map_map (by fun_prop) (by fun_prop)] at he
  exact he

end Paper09.ProductCoordinates
