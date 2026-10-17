import CounterFreeHDA.EndpointCriterion
import CounterFreeHDA.BoundedPowers

namespace CounterFreeHDA.FinCat
universe u v
variable {O : Type u} {C : FinCat.{u,v} O}

/-- One aperiodicity identity stabilizes every greater exponent. -/
theorem power_stable_above {h n : ℕ} (ha : C.AperiodicExponent h) (hn : h ≤ n)
    (U : O) (c : C.Hom U U) : pow c n = pow c (n+1) := by
  obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le hn
  induction d with
  | zero => simpa only [Nat.add_zero] using ha U c
  | succ d ih =>
    change C.comp (pow c (h+d)) c = C.comp (pow c (h+d+1)) c
    exact congrArg (fun a => C.comp a c) (ih (by omega))

end CounterFreeHDA.FinCat

namespace CounterFreeHDA.Cubical.OrderedPomsetRecognizer
universe u v
variable {Lab : Type u} {k h : ℕ} {L : Set (IntervalPom Lab)}
    (F : OrderedPomsetRecognizer.{u,v} (k := k) L h) {U : Cube Lab k}

theorem map_actual_power (P : EndoPom (cubeInterface U)) (hw : P.pom.val.WidthLE k) (n : ℕ) :
    F.map (P.boundedPower hw n) = FinCat.pow (F.map (P.bounded hw)) n := by
  induction n with
  | zero => exact F.map_id U
  | succ n ih =>
    rw [EndoPom.boundedPower_succ,F.map_comp,ih]
    rfl

/-- Recognized powers of the actual reduced middle pomset stabilize once
its exponent reaches h; this does not assume any boundary factorization. -/
theorem map_actual_power_stable (P : EndoPom (cubeInterface U)) (hw : P.pom.val.WidthLE k)
    {n : ℕ} (hn : h ≤ n) : F.map (P.boundedPower hw n) = F.map (P.boundedPower hw (n+1)) := by
  rw [F.map_actual_power,F.map_actual_power]
  exact FinCat.power_stable_above F.aperiodic hn U _

end CounterFreeHDA.Cubical.OrderedPomsetRecognizer
