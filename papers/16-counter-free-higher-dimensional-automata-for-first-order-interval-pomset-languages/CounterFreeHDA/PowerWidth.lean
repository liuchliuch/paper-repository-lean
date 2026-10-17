import CounterFreeHDA.TypedEndpointCriterion
import CounterFreeHDA.Identity

namespace CounterFreeHDA.EndoPom
universe u
open Cubical.TrackGlue
variable {Lab : Type u} {U : Interface Lab}

theorem width_of_positive_power (P : EndoPom U) {n k : ℕ} (hn : 1 ≤ n)
    (hw : (P.pow n).pom.val.WidthLE k) : P.pom.val.WidthLE k := by
  obtain ⟨d,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  apply hw.ofEmbedding
    ⟨rightEvent (GlueMatch.ofType ((P.pow d).target.trans P.source.symm)),
      (index _).injective.comp (GluedE.rightMap_inj _ _ _)⟩
  intro e f hef
  exact (rightEvent_prec _ P.pom.property e f).mp hef

noncomputable def powerIdentityIso (P : EndoPom U) (hs : P.pom.n = U.1) (n : ℕ) :
    PomsetIso (P.pow n).pom.val (identityPom Lab U.1 U.2).val :=
  (P.pow n).isoIdentityOfSizeEq (by rw [P.size_pow,hs,Nat.sub_self,Nat.mul_zero,Nat.add_zero])

end CounterFreeHDA.EndoPom
