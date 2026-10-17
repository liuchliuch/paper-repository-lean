import Paper19.Presentation
import Paper19.LocalRank

namespace Paper19
open scoped symmDiff

def vectorLevel {T : Tree} (x : Carrier T) : ℕ :=
  match x.val with | .idx _ => 0 | .vec n _ => n

/-- Translation constraints in formula (8), together with the singleton
numeral definitions for index-sort coordinates. -/
def LocalAction (T : Tree) (N : ℕ) (z : Finset Node) (x y : Carrier T) : Prop :=
  match x.val, y.val with
  | .idx k, .idx l => l = k
  | .vec n F, .vec m G => m = n ∧ G = F ∆ projectTo T N z n
  | _, _ => False

theorem localAction_coherent {T : Tree} (c : ValidAut T) {N : ℕ} (x y : Carrier T)
    (hN : vectorLevel x ≤ N) :
    LocalAction T N (c.val.h N) x y ↔ y = Carrier.translate c.val.h c.property x := by
  rcases x with ⟨x, hx⟩
  rcases y with ⟨y, hy⟩
  cases x with
  | idx k => cases y <;> simp [LocalAction, Carrier.translate, translateDom, Subtype.ext_iff]
  | vec n F =>
    have hn : n ≤ N := hN
    cases y <;> simp [LocalAction, Carrier.translate, translateDom, Subtype.ext_iff,
      coherent_projectTo c.val hn]

def ActualTupleOrbit (T : Tree) (tag : Bool) {m : ℕ} (a b : Fin m → Carrier T) : Prop :=
  ∃ f : PresentationIso T (namedRoot T tag) (namedRoot T tag), ∀ i, f.map (a i) = b i

/-- The orbit formula uses the genuine rank-at-least predicate at the
single common level N. It also covers mixed and empty tuples. -/
def ActualTupleFormula (T : Tree) {m : ℕ} (N : ℕ) (a b : Fin m → Carrier T) : Prop :=
  ∃ z : Finset Node, GMem T N z ∧
    HeightGE (fun y x : Dom T => IsChildG x y) (.vec N z) (localBound T N) ∧
    projectTo T N z 0 = ∅ ∧ ∀ i, LocalAction T N z (a i) (b i)

/-- Complete semantic orbit equivalence, for both named-root structures and
all finite tuples. No coherent-extension hypothesis is assumed. -/
theorem actual_tuple_orbit_formula {T : Tree} {m N : ℕ} (tag : Bool)
    (a b : Fin m → Carrier T) (hN : ∀ i, vectorLevel (a i) ≤ N) :
    ActualTupleOrbit T tag a b ↔ ActualTupleFormula T N a b := by
  constructor
  · rintro ⟨f, hf⟩
    let c := f.toValidAut
    have hc : ∀ i, b i = Carrier.translate c.val.h c.property (a i) := by
      intro i
      exact (hf i).symm.trans (f.translation_action (a i))
    have hl : LiftSeq T N (c.val.h N) := ⟨fun k => c.val.h (N + k), rfl,
      fun k => c.val.coherence (N + k), fun k => c.property (N + k)⟩
    refine ⟨c.val.h N, c.property N, ?_, ?_, ?_⟩
    · apply (theta_iff_extendible_support (c.property N)).mpr
      exact lemma6_ext_of_infiniteLift (hasInfiniteLiftG_of_liftSeq hl)
    · rw [coherent_projectTo c.val (Nat.zero_le N), c.val.root]
    · intro i
      exact (localAction_coherent c (a i) (b i) (hN i)).mpr (hc i)
  · rintro ⟨z, hz, htheta, hroot, hab⟩
    have he := (theta_iff_extendible_support hz).mp htheta
    obtain ⟨c, hc, hG⟩ := extend_lift (liftSeq_of_subset_ext he) hroot
    let c' : ValidAut T := ⟨c, hG⟩
    refine ⟨validAutToPresentation c' tag, ?_⟩
    intro i
    have hh := hab i
    rw [← hc] at hh
    exact ((localAction_coherent c' (a i) (b i) (hN i)).mp hh).symm

end Paper19
