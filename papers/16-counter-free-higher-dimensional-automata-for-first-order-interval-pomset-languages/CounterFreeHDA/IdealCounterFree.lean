import CounterFreeHDA.PowerWidth

namespace CounterFreeHDA.Cubical.OrderedPomsetRecognizer
universe u v
variable {Lab : Type u} {k h : ℕ} {L : Set (IntervalPom Lab)}
    (F : OrderedPomsetRecognizer.{u,v} (k := k) L h) {U S : Cube Lab k}

/-- The whole family of actual endpoint inequalities is identical at adjacent
large powers; compatibility and every corner image are proved to stabilize. -/
theorem stable_endpoint_criterion (P : EndoPom (cubeInterface U)) (hw : P.pom.val.WidthLE k)
    (x y : IdealDiagram F.C F.order F.stepImage S U) (n : ℕ) (hn : 2*k+h ≤ n) :
    (P.boundedPower hw n).toArrow.EndpointCriterion F (P.width_pow hw n) x y ↔
    (P.boundedPower hw (n+1)).toArrow.EndpointCriterion F (P.width_pow hw (n+1)) x y := by
  have hc : ∀ {T W : Cube Lab k} (α : Face T U) (β : Face W U),
      (P.boundedPower hw n).toArrow.Compatible α β ↔ P.StableCompatible α β := by
    intro T W α β
    exact P.compatible_pow_iff (Nat.le_of_lt_succ U.1.isLt) (by omega) α.status β.status
  have hc' : ∀ {T W : Cube Lab k} (α : Face T U) (β : Face W U),
      (P.boundedPower hw (n+1)).toArrow.Compatible α β ↔ P.StableCompatible α β := by
    intro T W α β
    exact P.compatible_pow_iff (Nat.le_of_lt_succ U.1.isLt) (by omega) α.status β.status
  constructor
  · intro H T W α β hab
    have hs := (hc' α β).mp hab
    have he := F.corollary_4_4 P hw α β hs n hn
    simpa only [← he] using H T W α β ((hc α β).mpr hs)
  · intro H T W α β hab
    have hs := (hc α β).mp hab
    have he := F.corollary_4_4 P hw α β hs n hn
    simpa only [he] using H T W α β ((hc' α β).mpr hs)

/-- Full endpoint stabilization inside any coefficient component, for every
actual bounded endomorphism, including the identity up to isomorphism. -/
theorem component_power_stable (P : EndoPom (cubeInterface U)) (hw : P.pom.val.WidthLE k)
    (x y : IdealDiagram F.C F.order F.stepImage S U) (n : ℕ)
    (hn : 2*k+h ≤ n) (hi : k+1 ≤ n) :
    y ∈ (ideal F.C F.order F.stepImage S).dPom x (P.pow n).pom ↔
    y ∈ (ideal F.C F.order F.stepImage S).dPom x (P.pow (n+1)).pom := by
  classical
  by_cases hid : IntervalPomIso P.pom (identityPom Lab U.dim U.lab)
  · obtain ⟨φ⟩ := hid
    have he : P.pom.n = U.dim := by
      simpa only [Fintype.card_fin] using Fintype.card_congr φ.toEquiv
    have hniso := P.powerIdentityIso he n
    have hsiso := P.powerIdentityIso he (n+1)
    exact (congrArg (fun a => y ∈ a) ((ideal F.C F.order F.stepImage S).dPom_iso (hniso.trans hsiso.symm) x)).to_iff
  · have hint := P.lemma_4_2_full hid (Nat.le_of_lt_succ U.1.isLt) hi
    have hint' := P.lemma_4_2_full hid (Nat.le_of_lt_succ U.1.isLt) (show k+1 ≤ n+1 by omega)
    exact ((P.boundedPower hw n).toArrow.endpoint_iff F (P.width_pow hw n) x y hint).trans
      ((F.stable_endpoint_criterion P hw x y n hn).trans
        ((P.boundedPower hw (n+1)).toArrow.endpoint_iff F (P.width_pow hw (n+1)) x y hint').symm)

end CounterFreeHDA.Cubical.OrderedPomsetRecognizer
