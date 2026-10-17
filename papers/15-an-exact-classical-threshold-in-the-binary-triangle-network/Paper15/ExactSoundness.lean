import Paper15.ExactChecker
import Paper15.ProductCells

/-! # Kernel proof of exact-checker soundness

An accepted finite integer trace yields a covering certificate tree for the
continuous product of probability simplexes. Packed checkpoints are accepted
only after equality to the reconstructed integer cell is verified.
-/
namespace Paper15.Exact
open Finset BigOperators

@[simp] lemma Tri.get_tabulate {α} (f : Fin 3 → α) (i : Fin 3) :
    (Tri.tabulate f).get i = f i := by fin_cases i <;> rfl

lemma Tri.all_iff {α} (v : Tri α) (p : α → Bool) :
    v.all p = true ↔ ∀ i : Fin 3, p (v.get i) = true := by
  constructor
  · intro h i
    have hh : (p v.a = true ∧ p v.b = true) ∧ p v.c = true := by
      simpa only [Tri.all, Bool.and_eq_true] using h
    fin_cases i
    · exact hh.1.1
    · exact hh.1.2
    · exact hh.2
  · intro h
    have hh := And.intro (And.intro (h 0) (h 1)) (h 2)
    simpa only [Tri.all, Bool.and_eq_true] using hh

@[simp] lemma Cube.get_tabulate (f : Fin 3 → Fin 3 → Fin 3 → Corner) (i j k : Fin 3) :
    Cube.get (Cube.tabulate f) i j k = f i j k := by simp [Cube.get, Cube.tabulate]

lemma Cube.all_iff (v : Cube) (p : Corner → Bool) :
    v.all (fun xs => xs.all (fun ys => ys.all p)) = true ↔
      ∀ i j k, p (Cube.get v i j k) = true := by
  simp only [Tri.all_iff, Cube.get]

def Corner.eval (f : Corner) (u : Fin 3) : Int :=
  if u = 0 then f.one else if u = 1 then f.three else f.pair

lemma Corner.eval_add (f g : Corner) (u : Fin 3) :
    (f.add g).eval u = f.eval u + g.eval u := by
  fin_cases u <;> rfl

lemma Corner.eval_double (f : Corner) (u : Fin 3) :
    f.double.eval u = 2 * f.eval u := by fin_cases u <;> rfl

lemma child_eval (c : Cell) (a r s u i j k : Fin 3) :
    (Cube.get (child c a r s).corners i j k).eval u =
      if a = 0 then
        if i = r then (Cube.get c.corners i j k).eval u + (Cube.get c.corners s j k).eval u
        else 2 * (Cube.get c.corners i j k).eval u
      else if a = 1 then
        if j = r then (Cube.get c.corners i j k).eval u + (Cube.get c.corners i s k).eval u
        else 2 * (Cube.get c.corners i j k).eval u
      else
        if k = r then (Cube.get c.corners i j k).eval u + (Cube.get c.corners i j s).eval u
        else 2 * (Cube.get c.corners i j k).eval u := by
  simp only [child, Cube.get_tabulate]
  split_ifs <;> first | exact Corner.eval_add _ _ _ | exact Corner.eval_double _ _

noncomputable section

def momentWeight (T : DetTriangle) (u : Fin 3) : Fin 3 → Fin 3 → Fin 3 → ℝ :=
  if u = 0 then w1 T else if u = 1 then w2 T else w3 T

def moment (T : DetTriangle) (c : ProductCell) (u i j k : Fin 3) : ℝ :=
  weightExp (momentWeight T u) (c 0 i) (c 1 j) (c 2 k)

/-- Exact scaled corner-value invariant. -/
def Represents (T : DetTriangle) (z : Cell) (c : ProductCell) : Prop :=
  0 < z.den ∧ ∀ u i j k,
    ((Cube.get z.corners i j k).eval u : ℝ) = (z.den : ℝ) * moment T c u i j k

lemma sign_cast (w n : Nat) : (sign w n : ℝ) = signOfBit (bitOf w n) := by
  cases h : w.testBit n <;> simp [sign, signOfBit, bitOf, h]

lemma weightExp_dirac (w : Fin 3 → Fin 3 → Fin 3 → ℝ) (i j k : Fin 3) :
    weightExp w (Simplex2.dirac i) (Simplex2.dirac j) (Simplex2.dirac k) = w i j k := by
  simp [weightExp, Simplex2.dirac, ite_mul, mul_ite]

lemma represents_root (w : Nat) : Represents (DetTriangle.ofPattern w) (root w) fullSourceCell := by
  refine ⟨by change (0 : Int) < 1; decide, ?_⟩
  intro u i j k
  fin_cases u <;>
    simp [root, Corner.eval, moment, momentWeight, fullSourceCell, weightExp_dirac,
      w1, w2, w3, DetTriangle.ofPattern, sign_cast]

lemma weightExp_mid_fst (w : Fin 3 → Fin 3 → Fin 3 → ℝ) (p q r s : Simplex2) :
    weightExp w (p.mid q) r s = (weightExp w p r s + weightExp w q r s) / 2 := by
  simp only [weightExp, Simplex2.mid, Fin.sum_univ_three]
  ring

lemma weightExp_mid_snd (w : Fin 3 → Fin 3 → Fin 3 → ℝ) (p q r s : Simplex2) :
    weightExp w p (q.mid r) s = (weightExp w p q s + weightExp w p r s) / 2 := by
  simp only [weightExp, Simplex2.mid, Fin.sum_univ_three]
  ring

lemma weightExp_mid_third (w : Fin 3 → Fin 3 → Fin 3 → ℝ) (p q r s : Simplex2) :
    weightExp w p q (r.mid s) = (weightExp w p q r + weightExp w p q s) / 2 := by
  simp only [weightExp, Simplex2.mid, Fin.sum_univ_three]
  ring

lemma moment_child (T : DetTriangle) (c : ProductCell) (a r s u i j k : Fin 3) :
    moment T (cellChild c a r s) u i j k =
      if a = 0 then
        if i = r then (moment T c u i j k + moment T c u s j k) / 2 else moment T c u i j k
      else if a = 1 then
        if j = r then (moment T c u i j k + moment T c u i s k) / 2 else moment T c u i j k
      else
        if k = r then (moment T c u i j k + moment T c u i j s) / 2 else moment T c u i j k := by
  fin_cases a
  · by_cases hi : i = r
    · subst i; simp [moment, cellChild, bisectVertices, Function.update, weightExp_mid_fst]
    · simp [moment, cellChild, bisectVertices, Function.update, hi]
  · by_cases hj : j = r
    · subst j; simp [moment, cellChild, bisectVertices, Function.update, weightExp_mid_snd]
    · simp [moment, cellChild, bisectVertices, Function.update, hj]
  · by_cases hk : k = r
    · subst k; simp [moment, cellChild, bisectVertices, Function.update, weightExp_mid_third]
    · simp [moment, cellChild, bisectVertices, Function.update, hk]

lemma Represents.child {T : DetTriangle} {z : Cell} {c : ProductCell}
    (h : Represents T z c) (a r s : Fin 3) :
    Represents T (Exact.child z a r s) (cellChild c a r s) := by
  refine ⟨mul_pos (by decide) h.1, ?_⟩
  intro u i j k
  have hden : (Exact.child z a r s).den = 2*z.den := rfl
  rw [child_eval, moment_child, hden]
  split_ifs <;> simp only [Int.cast_add, Int.cast_mul, Int.cast_ofNat, h.2] <;> ring

/-- All 27 integer checks imply a real affine certificate on the cell. -/
lemma leafValid_sound {T : DetTriangle} {z : Cell} {c : ProductCell}
    (hrep : Represents T z c) (kind : Nat) (j k : Fin 27)
    (hvalid : leafValid z kind j k = true) :
    ∃ lam mu : ℝ, ∀ i j k, certForm T lam mu (c 0 i) (c 1 j) (c 2 k) ≤ 0 := by
  let w := witness z kind j k
  change ((decide (0 < z.den) && decide (0 < w.d)) && _) = true at hvalid
  have hden : 0 < z.den := of_decide_eq_true (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hvalid).1).1
  have hd : 0 < w.d := of_decide_eq_true (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hvalid).1).2
  have hall := (Cube.all_iff z.corners (fun f => satisfies (plane z.den f) w)).mp
    (Bool.and_eq_true_iff.mp hvalid).2
  have hdenR : (0 : ℝ) < z.den := by exact_mod_cast hden
  have hdR : (0 : ℝ) < w.d := by exact_mod_cast hd
  refine ⟨(w.x : ℝ) / w.d, (w.y : ℝ) / w.d, ?_⟩
  intro i j k
  let f := Cube.get z.corners i j k
  have hi : (plane z.den f).c * w.d ≤ (plane z.den f).a * w.x + (plane z.den f).b * w.y :=
    of_decide_eq_true (hall i j k)
  have hiR : (((plane z.den f).c * w.d : Int) : ℝ) ≤
      (((plane z.den f).a * w.x + (plane z.den f).b * w.y : Int) : ℝ) := by exact_mod_cast hi
  simp only [plane, Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_ofNat] at hiR
  have he1 : (f.one : ℝ) = (z.den : ℝ) * weightExp (w1 T) (c 0 i) (c 1 j) (c 2 k) := hrep.2 0 i j k
  have he3 : (f.three : ℝ) = (z.den : ℝ) * weightExp (w2 T) (c 0 i) (c 1 j) (c 2 k) := hrep.2 1 i j k
  have he2 : (f.pair : ℝ) = (z.den : ℝ) * weightExp (w3 T) (c 0 i) (c 1 j) (c 2 k) := hrep.2 2 i j k
  have he : (25 * (z.den : ℝ) * (w.d : ℝ)) *
      certForm T ((w.x : ℝ) / w.d) ((w.y : ℝ) / w.d) (c 0 i) (c 1 j) (c 2 k) =
      (25 * (f.pair : ℝ) - 27 * z.den) * w.d -
        25 * f.one * w.x - 25 * f.three * w.y := by
    simp only [certForm, twentySevenTwentyFifths]
    rw [he1, he3, he2]
    field_simp [hdR.ne'] <;> ring
  have hfactor : (0 : ℝ) < 25 * (z.den : ℝ) * (w.d : ℝ) := by positivity
  apply (mul_le_mul_left hfactor).mp
  rw [mul_zero, he]
  linarith

/-- An accepted executable trace constructs a genuine covering tree. -/
theorem valid_sound (t : Trace) : ∀ {T : DetTriangle} {z : Cell} {c : ProductCell},
    Represents T z c → valid z t = true → Nonempty (FullCertTree T c) := by
  induction t with
  | leaf kind j k =>
    intro T z c hrep hv
    obtain ⟨lam, mu, hc⟩ := leafValid_sound hrep kind j k hv
    exact ⟨FullCertTree.leaf lam mu hc⟩
  | split a i j l r ihl ihr =>
    intro T z c hrep hv
    change ((decide (i ≠ j) && valid (Exact.child z a i j) l) && valid (Exact.child z a j i) r) = true at hv
    obtain ⟨⟨hij, hl⟩, hr⟩ := (Bool.and_eq_true_iff.mp hv).imp (fun h => Bool.and_eq_true_iff.mp h) id
    obtain ⟨tl⟩ := ihl (hrep.child a i j) hl
    obtain ⟨tr⟩ := ihr (hrep.child a j i) hr
    exact ⟨FullCertTree.split a i j (of_decide_eq_true hij) tl tr⟩
  | checkpoint claimed t ih =>
    intro T z c hrep hv
    obtain ⟨he, ht⟩ := Bool.and_eq_true_iff.mp hv
    have heq : z = claimed := of_decide_eq_true he
    subst claimed
    exact ih hrep ht

/-- The main reflection theorem: a successful integer check proves the
continuous gap on the full probability domain for the decoded response word. -/
theorem gapHolds_of_valid (word : Nat) (t : Trace) (h : valid (root word) t = true) :
    GapHolds (DetTriangle.ofPattern word) := by
  obtain ⟨tree⟩ := valid_sound t (represents_root word) h
  exact gapHolds_of_fullCertTree tree

end
end Paper15.Exact
