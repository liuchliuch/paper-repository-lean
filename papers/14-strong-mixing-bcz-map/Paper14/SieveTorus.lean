import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Probability.Independence.Integration

open MeasureTheory Function ProbabilityTheory
namespace Paper14
noncomputable section

/-- The actual integer torus endomorphism in paper Ex38. -/
def sieveTorusHom {G : Type*} [AddCommGroup G] (q q' : ℤ) : G × G →+ G × G where
  toFun z := (q • z.1 - z.2, q' • z.1 - z.2)
  map_zero' := by simp
  map_add' z w := by ext <;> simp only [Prod.fst_add,Prod.snd_add,smul_add] <;> abel

lemma sieveTorusHom_continuous {G : Type*} [AddCommGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] (q q' : ℤ) : Continuous (sieveTorusHom (G := G) q q') := by
  change Continuous (fun z : G × G => (q • z.1 - z.2, q' • z.1 - z.2))
  fun_prop

lemma sieveTorusHom_surjective {G : Type*} [AddCommGroup G] [DivisibleBy G ℤ]
    {q q' : ℤ} (hqq : q ≠ q') : Surjective (sieveTorusHom (G := G) q q') := by
  rintro ⟨u,v⟩
  obtain ⟨θ,hθ⟩ := smul_right_surj_of_divisibleBy G ℤ (n := q'-q) (sub_ne_zero.mpr hqq.symm) (v-u)
  refine ⟨(θ,q • θ-u),?_⟩
  change (q • θ - (q • θ-u),q' • θ - (q • θ-u)) = (u,v)
  change (q'-q) • θ = v-u at hθ
  rw [sub_smul] at hθ
  ext
  · abel
  · change q' • θ - (q • θ-u) = v
    calc q' • θ - (q • θ-u) = (q' • θ-q • θ)+u := by abel
         _ = v := by rw [hθ]; abel

/-- Surjectivity of the integer endomorphism proves its Haar pushforward,
including the independence of its two output coordinates. -/
theorem sieveTorus_measurePreserving {G : Type*} [AddCommGroup G] [DivisibleBy G ℤ]
    [TopologicalSpace G] [IsTopologicalAddGroup G] [CompactSpace G]
    [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsAddHaarMeasure] [IsProbabilityMeasure μ]
    {q q' : ℤ} (hqq : q ≠ q') :
    MeasurePreserving (sieveTorusHom (G := G) q q') (μ.prod μ) (μ.prod μ) := by
  exact AddMonoidHom.measurePreserving (sieveTorusHom_continuous q q')
    (sieveTorusHom_surjective hqq) (by simp)

theorem sieveTorus_independent {G : Type*} [AddCommGroup G] [DivisibleBy G ℤ]
    [TopologicalSpace G] [IsTopologicalAddGroup G] [CompactSpace G]
    [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsAddHaarMeasure] [IsProbabilityMeasure μ]
    {q q' : ℤ} (hqq : q ≠ q') :
    IndepFun (fun z : G × G => q • z.1-z.2) (fun z : G × G => q' • z.1-z.2) (μ.prod μ) := by
  have hmp := sieveTorus_measurePreserving μ hqq
  have hf := (measurePreserving_fst (μ := μ) (ν := μ)).comp hmp
  have hg := (measurePreserving_snd (μ := μ) (ν := μ)).comp hmp
  apply (indepFun_iff_map_prod_eq_prod_map_map hf.measurable.aemeasurable hg.measurable.aemeasurable).mpr
  change Measure.map (sieveTorusHom (G := G) q q') (μ.prod μ) = _
  rw [hmp.map_eq,hf.map_eq,hg.map_eq]

/-- Measurable periodic sieve indicators inherit the actual pairwise
independence, rather than taking it as a certificate. -/
theorem sieveTorus_functions_independent {G A B : Type*} [AddCommGroup G] [DivisibleBy G ℤ]
    [TopologicalSpace G] [IsTopologicalAddGroup G] [CompactSpace G]
    [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure G) [μ.IsAddHaarMeasure] [IsProbabilityMeasure μ]
    {q q' : ℤ} (hqq : q ≠ q') (f : G → A) (g : G → B)
    (hf : Measurable f) (hg : Measurable g) :
    IndepFun (fun z : G × G => f (q • z.1-z.2)) (fun z : G × G => g (q' • z.1-z.2)) (μ.prod μ) :=
  (sieveTorus_independent μ hqq).comp hf hg

end
end Paper14
