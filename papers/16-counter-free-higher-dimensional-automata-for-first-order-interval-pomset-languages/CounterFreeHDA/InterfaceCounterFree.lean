import CounterFreeHDA.PowerWidth
import CounterFreeHDA.InterfaceStableCorners
import CounterFreeHDA.CoproductCounterFree

namespace CounterFreeHDA.Cubical.OrderedPomsetRecognizer
universe u v
variable {Lab : Type u} {k h : ℕ} {L : Set (IntervalPom Lab)}
    (F : OrderedPomsetRecognizer.{u,v} (k := k) L h) {U S : Cube Lab k}

/-- The whole family of actual endpoint inequalities is identical at adjacent
large powers; compatibility and every corner image are proved to stabilize. -/
theorem stable_endpoint_criterion_interface (P : EndoPom (cubeInterface U)) (hw : P.pom.val.WidthLE k)
    (x y : IdealDiagram F.C F.order F.stepImage S U) (n : ℕ) (hn : 2*U.dim+h ≤ n) :
    (P.boundedPower hw n).toArrow.EndpointCriterion F (P.width_pow hw n) x y ↔
    (P.boundedPower hw (n+1)).toArrow.EndpointCriterion F (P.width_pow hw (n+1)) x y := by
  have hc : ∀ {T W : Cube Lab k} (α : Face T U) (β : Face W U),
      (P.boundedPower hw n).toArrow.Compatible α β ↔ P.StableCompatible α β := by
    intro T W α β
    exact P.compatible_pow_iff (le_refl U.dim) (by omega) α.status β.status
  have hc' : ∀ {T W : Cube Lab k} (α : Face T U) (β : Face W U),
      (P.boundedPower hw (n+1)).toArrow.Compatible α β ↔ P.StableCompatible α β := by
    intro T W α β
    exact P.compatible_pow_iff (le_refl U.dim) (by omega) α.status β.status
  constructor
  · intro H T W α β hab
    have hs := (hc' α β).mp hab
    have he := F.corollary_4_4_interface P hw α β hs n hn
    simpa only [← he] using H T W α β ((hc α β).mpr hs)
  · intro H T W α β hab
    have hs := (hc α β).mp hab
    have he := F.corollary_4_4_interface P hw α β hs n hn
    simpa only [he] using H T W α β ((hc' α β).mpr hs)

/-- Full endpoint stabilization inside any coefficient component, for every
actual bounded endomorphism, including the identity up to isomorphism. -/
theorem component_power_stable_interface (P : EndoPom (cubeInterface U)) (hw : P.pom.val.WidthLE k)
    (x y : IdealDiagram F.C F.order F.stepImage S U) (n : ℕ)
    (hn : 2*U.dim+h ≤ n) (hi : U.dim+1 ≤ n) :
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
  · have hint := P.lemma_4_2_full hid (le_refl U.dim) hi
    have hint' := P.lemma_4_2_full hid (le_refl U.dim) (show U.dim+1 ≤ n+1 by omega)
    exact ((P.boundedPower hw n).toArrow.endpoint_iff F (P.width_pow hw n) x y hint).trans
      ((F.stable_endpoint_criterion_interface P hw x y n hn).trans
        ((P.boundedPower hw (n+1)).toArrow.endpoint_iff F (P.width_pow hw (n+1)) x y hint').symm)


theorem full_power_stable_interface (P : EndoPom (cubeInterface U)) (x y : F.hda.Cell U)
    (n : ℕ) (hn : 2*U.dim+h ≤ n) (hh : 1 ≤ h) :
    y ∈ F.hda.toPrecubical.dPom x (P.pow n).pom ↔
    y ∈ F.hda.toPrecubical.dPom x (P.pow (n+1)).pom := by
  classical
  have hi : U.dim+1 ≤ n := by omega
  by_cases hw : P.pom.val.WidthLE k
  · rcases x with ⟨S,x⟩
    rcases y with ⟨T,y⟩
    by_cases he : S = T
    · subst T
      exact (F.component_reachability _ x y).trans
        ((F.component_power_stable_interface P hw x y n hn hi).trans (F.component_reachability _ x y).symm)
    · exact iff_of_false (F.no_cross_component he _ x y) (F.no_cross_component he _ x y)
  · constructor
    · intro hr
      exact False.elim (hw (P.width_of_positive_power (by omega) (F.hda.toPrecubical.reachable_width hr)))
    · intro hr
      exact False.elim (hw (P.width_of_positive_power (by omega) (F.hda.toPrecubical.reachable_width hr)))


/-- S4.p16: the same ideal-diagram HDA has bound 2r+h at an interface of
size r. No bound by r is imposed on internal events or intermediate cubes. -/
theorem interface_endpoint_stable (hh : 1 ≤ h) (U : Cube Lab k)
    (x : F.hda.Cell U) (P : EndoPom (cubeInterface U))
    (n : ℕ) (hn : 2*U.dim+h ≤ n) :
    F.hda.toPrecubical.dPom (V := U) x (P.pow n).pom =
      F.hda.toPrecubical.dPom x (P.pow (n+1)).pom := by
  ext y
  exact F.full_power_stable_interface P x y n hn hh

/-- S4.p16, empty interface: the exponent is h itself in the same HDA,
even when the actual closed pomset has internal width greater than zero. -/
theorem empty_interface_endpoint_stable (hh : 1 ≤ h) (U : Cube Lab k)
    (hr : U.dim = 0) (x : F.hda.Cell U) (P : EndoPom (cubeInterface U))
    (n : ℕ) (hn : h ≤ n) :
    F.hda.toPrecubical.dPom (V := U) x (P.pow n).pom =
      F.hda.toPrecubical.dPom x (P.pow (n+1)).pom :=
  F.interface_endpoint_stable hh U x P n (by omega)

end CounterFreeHDA.Cubical.OrderedPomsetRecognizer
