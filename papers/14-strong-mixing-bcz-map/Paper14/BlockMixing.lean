import Paper14.Completion

open MeasureTheory Filter Topology Set
namespace Paper14
noncomputable section

/-- A measurable finite block of observations along the actual BCZ orbit. -/
def bczBlock (I : Finset ℕ) (A : ℕ → Set (ℝ × ℝ)) : Set (ℝ × ℝ) :=
  {x | ∀ i∈I,B^[i] x∈A i}

lemma measurableSet_bczBlock (I : Finset ℕ) {A : ℕ → Set (ℝ × ℝ)}
    (hA : ∀ i,MeasurableSet (A i)) : MeasurableSet (bczBlock I A) := by
  simp only [bczBlock,setOf_forall]
  exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun _hi =>
    (measurable_B.iterate i) (hA i)

/-- The source finite-block asymptotic independence holds along all integer times. -/
theorem finite_block_mixing (I J : Finset ℕ) (A C : ℕ → Set (ℝ × ℝ))
    (hA : ∀ i,MeasurableSet (A i)) (hC : ∀ j,MeasurableSet (C j)) :
    Tendsto (fun n : ℕ => m ((B^[n]) ⁻¹' bczBlock I A ∩ bczBlock J C)) atTop
      (𝓝 (m (bczBlock I A)*m (bczBlock J C))) :=
  Theorem1 _ _ (measurableSet_bczBlock I hA) (measurableSet_bczBlock J hC)

end
end Paper14
