import Paper14.Background.HorocycleErgodic
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.Instances.Int
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.IsUniformGroup.Basic
import Mathlib.Topology.DiscreteSubset

open Matrix Set Topology Filter
open scoped Matrix MatrixGroups
namespace Paper14.Background
noncomputable section

abbrev SL2Z := Matrix.SpecialLinearGroup (Fin 2) ℤ

def slIntegerEmbedding : SL2Z →* SL2R :=
  Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)

def slIntegerSubgroup : Subgroup SL2R := slIntegerEmbedding.range

instance : Countable (Matrix (Fin 2) (Fin 2) ℤ) :=
  inferInstanceAs (Countable (Fin 2 → Fin 2 → ℤ))
instance : Countable SL2Z :=
  inferInstanceAs (Countable {g : Matrix (Fin 2) (Fin 2) ℤ // g.det=1})
instance : Countable slIntegerSubgroup :=
  (Set.countable_range slIntegerEmbedding).to_subtype

lemma slIntegerEmbedding_injective : Function.Injective slIntegerEmbedding := by
  intro g h heq
  exact Matrix.SpecialLinearGroup.map_intCast_inj.mp heq

lemma mem_slIntegerSubgroup (g : SL2R) : g∈slIntegerSubgroup ↔
    ∀ i j : Fin 2,∃ n : ℤ,g i j=n := by
  constructor
  · rintro ⟨h,rfl⟩ i j
    exact ⟨h i j,rfl⟩
  · intro h
    choose z hz using h
    let M : Matrix (Fin 2) (Fin 2) ℤ := Matrix.of z
    have hm : M.map (Int.castRingHom ℝ)=(g : Matrix (Fin 2) (Fin 2) ℝ) := by
      ext i j
      exact (hz i j).symm
    have hdR : (z 0 0 : ℝ)*(z 1 1 : ℝ)-(z 0 1 : ℝ)*(z 1 0 : ℝ)=1 := by
      rw [← hz 0 0,← hz 1 1,← hz 0 1,← hz 1 0]
      simpa only [Matrix.det_fin_two] using g.property
    have hd : M.det=1 := by
      simpa only [Matrix.det_fin_two] using (show z 0 0*z 1 1-z 0 1*z 1 0=1 by exact_mod_cast hdR)
    refine ⟨⟨M,hd⟩,?_⟩
    apply Subtype.ext
    exact hm

lemma isClosed_slIntegerSubgroup : IsClosed (slIntegerSubgroup : Set SL2R) := by
  have heq : (slIntegerSubgroup : Set SL2R)=
      ⋂ i : Fin 2,⋂ j : Fin 2,(fun g : SL2R => g i j) ⁻¹' range ((↑) : ℤ → ℝ) := by
    ext g
    change g∈slIntegerSubgroup ↔ _
    rw [mem_slIntegerSubgroup]
    simp only [mem_iInter,mem_preimage,mem_range]
    simp only [eq_comm]
  rw [heq]
  apply isClosed_iInter
  intro i
  apply isClosed_iInter
  intro j
  apply Int.isClosedEmbedding_coe_real.isClosed_range.preimage
  exact (continuous_apply j).comp ((continuous_apply i).comp continuous_subtype_val)

instance : PolishSpace (Matrix (Fin 2) (Fin 2) ℝ) :=
  inferInstanceAs (PolishSpace (Fin 2 → Fin 2 → ℝ))
instance : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) ℝ) :=
  inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → ℝ))

lemma isClosed_sl2DetOne : IsClosed {g : Matrix (Fin 2) (Fin 2) ℝ | g.det=1} :=
  isClosed_eq (by fun_prop) continuous_const

instance : PolishSpace SL2R := isClosed_sl2DetOne.polishSpace
instance : LocallyCompactSpace SL2R := isClosed_sl2DetOne.locallyCompactSpace


lemma isEmbedding_slIntegerEmbedding : Topology.IsEmbedding slIntegerEmbedding := by
  have hcomp : Topology.IsEmbedding
      ((Matrix.SpecialLinearGroup.toGL : SL2R → GL (Fin 2) ℝ) ∘ slIntegerEmbedding) := by
    exact Matrix.SpecialLinearGroup.isEmbedding_mapGL Int.isClosedEmbedding_coe_real.isEmbedding
  exact Topology.IsEmbedding.of_comp continuous_of_discreteTopology
    Matrix.SpecialLinearGroup.continuous_toGL hcomp

lemma isClosedEmbedding_slIntegerEmbedding : Topology.IsClosedEmbedding slIntegerEmbedding :=
  ⟨isEmbedding_slIntegerEmbedding,isClosed_slIntegerSubgroup⟩

instance : DiscreteTopology slIntegerSubgroup :=
  isEmbedding_slIntegerEmbedding.toHomeomorph.discreteTopology

instance : ProperlyDiscontinuousSMul slIntegerSubgroup.op SL2R :=
  slIntegerSubgroup.properlyDiscontinuousSMul_opposite_of_tendsto_cofinite
    slIntegerSubgroup.tendsto_coe_cofinite_of_discrete

instance : T2Space (SL2R ⧸ slIntegerSubgroup) :=
  inferInstanceAs (T2Space (Quotient (MulAction.orbitRel slIntegerSubgroup.op SL2R)))
instance : SecondCountableTopology (SL2R ⧸ slIntegerSubgroup) := inferInstance

end
end Paper14.Background
