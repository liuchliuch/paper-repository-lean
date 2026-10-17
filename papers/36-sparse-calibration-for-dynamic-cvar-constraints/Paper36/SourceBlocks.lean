import Paper36.AdaptiveTapes

/-! One physical episode consumes the actual original row heads. The joint law
of its trajectory and every unused row is derived from the row-product law. -/
namespace Paper36.SourceBlocks
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Paper36.CVaR Paper36.Simulation
  Paper36.Trajectories Paper36.AdaptiveTapes

universe u
variable {S A X Y : Type u} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
  [MeasurableSpace S] [DiscreteMeasurableSpace S]

/-- The finite pushforward law. -/
def pushLaw [Fintype X] [Fintype Y] (P : Law X) (f : X → Y) : Law Y :=
  bindLaw P (fun x => dirac (f x))

lemma pushLaw_expect [Fintype X] [Fintype Y] (P : Law X) (f : X → Y) (g : Y → ℝ) :
    expect (pushLaw P f).mass g = expect P.mass (fun x => g (f x)) := by
  rw [pushLaw, bindLaw_expect]
  simp only [expect_dirac]

/-- Both the actual trajectory and its unused stack are retained. -/
def blockLaw (π : Policy S A) (L : ℕ) : (n : ℕ) → ℕ → S →
    Stack (S × A) S (L+n) → Law (Trajectory S A n × Stack (S × A) S L)
  | 0, _, s, tape => dirac (s,tape)
  | n+1, h, s, tape => bindLaw (π h s) (fun a =>
      pushLaw (blockLaw π L n (h+1) (head (s,a) tape) (remaining (s,a) tape))
        (fun z => ((s,a,z.1),z.2)))

/-- The entire unused stack is independent of the episode, with its original
law. This is stronger than the episode-marginal Markov trajectory statement. -/
theorem blockLaw_expect_average (π : Policy S A) (p : Simulation.Kernel S A)
    (L n h : ℕ) (s : S) (f : Trajectory S A n × Stack (S × A) S L → ℝ) :
    expect (stackLaw (fun r : S × A => p r.1 r.2) (L+n)).mass
      (fun tape => expect (blockLaw π L n h s tape).mass f) =
    expect (trajectoryLaw π p n h s).mass
      (fun path => expect (stackLaw (fun r : S × A => p r.1 r.2) L).mass
        (fun tape => f (path,tape))) := by
  induction n generalizing h s with
  | zero => simp only [blockLaw, expect_dirac, trajectoryLaw, Nat.add_zero]
  | succ n ih =>
    simp only [blockLaw, bindLaw_expect, pushLaw_expect]
    rw [expect_swap]
    have heq (a : A) :
        expect (stackLaw (fun r : S × A => p r.1 r.2) (L+(n+1))).mass
          (fun tape => expect (blockLaw π L n (h+1) (head (s,a) tape)
            (remaining (s,a) tape)).mass (fun z => f ((s,a,z.1),z.2))) =
        expect (p s a).mass (fun y =>
          expect (trajectoryLaw π p n (h+1) y).mass (fun path =>
            expect (stackLaw (fun r : S × A => p r.1 r.2) L).mass
              (fun tape => f ((s,a,path),tape)))) := by
      have hp := pop_expect (fun r : S × A => p r.1 r.2) (s,a) (L+n)
        (fun y tape => expect (blockLaw π L n (h+1) y tape).mass
          (fun z => f ((s,a,z.1),z.2)))
      apply hp.trans
      apply Finset.sum_congr rfl
      intro y _
      exact congrArg ((p s a).mass y * ·) (ih (h+1) y (fun z => f ((s,a,z.1),z.2)))
    simp_rw [heq]
    rw [trajectoryLaw, expect_joint]
    change _ = expect (dirac s).mass (fun u =>
      expect (joint (π h u) (fun a => bindLaw (p u a) (fun t => trajectoryLaw π p n (h+1) t))).mass
        (fun z => expect (stackLaw (fun r : S × A => p r.1 r.2) L).mass
          (fun tape => f ((u,z),tape))))
    rw [expect_dirac]
    simp only [expect_joint, bindLaw_expect]
    rfl

end
end Paper36.SourceBlocks
