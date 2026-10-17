import Paper36.RowTapes
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Independence.InfinitePi

/-! Constructed infinite categorical row tapes. The arbitrary latent-model prior
is combined with a measurable infinite product kernel. Every finite selection
has its genuine product law; no iid conclusion is included as a new premise. -/
namespace Paper36.InfiniteTapes
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory Paper36.CVaR Paper36.Trajectories

variable {I J S M : Type*} [Fintype S] [MeasurableSpace S] [DiscreteMeasurableSpace S]
  [MeasurableSpace M]

/-- A finite product of possibly different categorical rows. -/
def finiteLaw [Fintype J] [DecidableEq J] (P : J → Law S) : Law (J → S) where
  mass x := ∏ j, (P j).mass (x j)
  nonneg x := Finset.prod_nonneg fun j _ => (P j).nonneg _
  total := by
    classical
    rw [← Fintype.prod_sum]
    simp [Law.total]

lemma lawMeasure_singleton (P : Law S) (s : S) :
    lawMeasure P {s} = ENNReal.ofReal (P.mass s) := by
  rw [lawMeasure, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  rfl

lemma lawMeasure_finiteLaw [Fintype J] [DecidableEq J] (P : J → Law S) :
    lawMeasure (finiteLaw P) = Measure.pi (fun j => lawMeasure (P j)) := by
  classical
  apply Measure.ext_of_singleton
  intro x
  rw [lawMeasure_singleton, ← Set.univ_pi_singleton x, Measure.pi_pi]
  simp only [lawMeasure_singleton, finiteLaw]
  exact ENNReal.ofReal_prod_of_nonneg (fun j _ => (P j).nonneg _)

/-- The raw infinite tape distribution at a fixed model. -/
def infiniteLaw (P : I → Law S) : Measure (I → S) :=
  Measure.infinitePi (fun i => lawMeasure (P i))

instance infiniteLaw_probability (P : I → Law S) : IsProbabilityMeasure (infiniteLaw P) := by
  unfold infiniteLaw
  infer_instance

/-- Finite-dimensional measurability implies measurability of the actual infinite
product probability measure, by a cylinder pi-system argument. -/
theorem measurable_infiniteLaw (P : M → I → Law S)
    (hP : ∀ i s, Measurable (fun m => (P m i).mass s)) :
    Measurable (fun m => infiniteLaw (P m)) := by
  classical
  apply Measurable.measure_of_isPiSystem_of_isProbabilityMeasure
    (generateFrom_measurableCylinders (α := fun _ : I => S)).symm
    isPiSystem_measurableCylinders
  intro B hB
  obtain ⟨F, C, hC, rfl⟩ := (mem_measurableCylinders B).mp hB
  have heq (m : M) : infiniteLaw (P m) (cylinder F C) =
      (Measure.pi (fun j : F => lawMeasure (P m j))) C := by
    exact Measure.infinitePi_cylinder (fun i => lawMeasure (P m i)) hC
  simp_rw [heq]
  have hmass : ∀ x : F → S, Measurable (fun m => (finiteLaw (fun j : F => P m j)).mass x) := by
    intro x
    exact Finset.measurable_prod _ (fun (j : F) _ => hP j (x j))
  have hm := (lawKernel (fun m => finiteLaw (fun j : F => P m j)) hmass).measurable_coe hC
  simpa only [lawKernel, lawMeasure_finiteLaw] using hm

/-- The canonical measurable row-tape sampling kernel. -/
def infiniteKernel (P : M → I → Law S)
    (hP : ∀ i s, Measurable (fun m => (P m i).mass s)) : ProbabilityTheory.Kernel M (I → S) where
  toFun m := infiniteLaw (P m)
  measurable' := measurable_infiniteLaw P hP

instance infiniteKernel_markov (P : M → I → Law S)
    (hP : ∀ i s, Measurable (fun m => (P m i).mass s)) :
    IsMarkovKernel (infiniteKernel P hP) := ⟨fun m => infiniteLaw_probability (P m)⟩

/-- Any injective finite list of infinite-tape coordinates has precisely the
product law of those coordinates. -/
theorem infinite_projection [Fintype J] [DecidableEq J] (P : I → Law S) (e : J ↪ I) :
    (infiniteLaw P).map (fun tape j => tape (e j)) = lawMeasure (finiteLaw (fun j => P (e j))) := by
  classical
  have hind : iIndepFun (fun i (tape : I → S) => tape i) (infiniteLaw P) := by
    simpa only [infiniteLaw] using
      (iIndepFun_infinitePi (μ := fun i => lawMeasure (P i))
        (X := fun _ (s : S) => s) (fun _ => measurable_id))
  have hsel := hind.precomp e.injective
  have hmap := (iIndepFun_iff_map_fun_eq_pi_map
    (fun j => (measurable_pi_apply (e j)).aemeasurable)).mp hsel
  have heval : ∀ j, (infiniteLaw P).map (fun tape : I → S => tape (e j)) = lawMeasure (P (e j)) := by
    intro j
    exact (measurePreserving_eval_infinitePi (fun i => lawMeasure (P i)) (e j)).map_eq
  simpa only [heval, lawMeasure_finiteLaw] using hmap

section RowStacks
variable {Row : Type*}

def rowKernel (P : M → Row → Law S)
    (hP : ∀ r s, Measurable (fun m => (P m r).mass s)) :
    ProbabilityTheory.Kernel M (Row × ℕ → S) :=
  infiniteKernel (fun m => fun c : Row × ℕ => P m c.1) (fun c s => hP c.1 s)

instance rowKernel_markov (P : M → Row → Law S)
    (hP : ∀ r s, Measurable (fun m => (P m r).mass s)) :
    IsMarkovKernel (rowKernel P hP) := by
  unfold rowKernel
  infer_instance

def tapePrefix (r : Row) (n : ℕ) (tape : Row × ℕ → S) : Fin n → S :=
  fun i => tape (r, i.val)

lemma measurable_prefix (r : Row) (n : ℕ) : Measurable (tapePrefix (S := S) r n) := by
  apply measurable_pi_lambda
  intro i
  exact measurable_pi_apply _

/-- The infinite row kernel has exactly the iid tapePrefix laws used by the
method-of-types and Weissman inputs. -/
theorem row_prefix_law (P : Row → Law S) (r : Row) (n : ℕ) :
    (infiniteLaw (fun c : Row × ℕ => P c.1)).map (tapePrefix r n) =
      lawMeasure (RowTapes.iidLaw (P r) n) := by
  let e : Fin n ↪ Row × ℕ := ⟨fun i => (r, i.val), fun i j h => Fin.ext (congrArg (fun c => c.2) h)⟩
  exact infinite_projection (fun c : Row × ℕ => P c.1) e

theorem rowKernel_prefix (P : M → Row → Law S)
    (hP : ∀ r s, Measurable (fun m => (P m r).mass s)) (r : Row) (n : ℕ) :
    (rowKernel P hP).map (tapePrefix r n) = RowTapes.iidKernel (fun m => P m r) (hP r) n := by
  ext m B hB
  rw [ProbabilityTheory.Kernel.map_apply _ (measurable_prefix r n)]
  exact congrArg (fun ν : Measure (Fin n → S) => ν B) (row_prefix_law (P m) r n)

/-- An arbitrary prior, without row-independence or any parametric assumption,
is combined with the constructed conditional iid tape law. -/
def priorTapes (ν : Measure M) (P : M → Row → Law S)
    (hP : ∀ r s, Measurable (fun m => (P m r).mass s)) : Measure (M × (Row × ℕ → S)) :=
  ν ⊗ₘ rowKernel P hP

instance priorTapes_probability (ν : Measure M) [IsProbabilityMeasure ν]
    (P : M → Row → Law S) (hP : ∀ r s, Measurable (fun m => (P m r).mass s)) :
    IsProbabilityMeasure (priorTapes ν P hP) := by
  unfold priorTapes
  infer_instance

lemma priorTapes_latent_law (ν : Measure M) [IsProbabilityMeasure ν]
    (P : M → Row → Law S) (hP : ∀ r s, Measurable (fun m => (P m r).mass s)) :
    (priorTapes ν P hP).map Prod.fst = ν := by
  exact Measure.fst_compProd ν (rowKernel P hP)

/-- The exact posterior-system tape-law field is a theorem of the canonical
infinite product realization, for every row and every finite tapePrefix. -/
theorem priorTapes_prefix_condDistrib [Nonempty S] (ν : Measure M) [IsProbabilityMeasure ν]
    (P : M → Row → Law S) (hP : ∀ r s, Measurable (fun m => (P m r).mass s))
    (r : Row) (n : ℕ) :
    condDistrib (fun x : M × (Row × ℕ → S) => tapePrefix r n x.2) Prod.fst (priorTapes ν P hP)
      =ᵐ[ν] RowTapes.iidKernel (fun m => P m r) (hP r) n := by
  have hjoint : (priorTapes ν P hP).map (fun x => (x.1, tapePrefix r n x.2)) =
      (priorTapes ν P hP).map Prod.fst ⊗ₘ RowTapes.iidKernel (fun m => P m r) (hP r) n := by
    rw [priorTapes_latent_law, ← rowKernel_prefix P hP r n,
      Measure.compProd_map (measurable_prefix r n)]
    rfl
  have hc := condDistrib_ae_eq_of_measure_eq_compProd_of_measurable
    (μ := priorTapes ν P hP) measurable_fst ((measurable_prefix r n).comp measurable_snd) hjoint
  simpa only [priorTapes_latent_law] using hc

end RowStacks
end
end Paper36.InfiniteTapes
