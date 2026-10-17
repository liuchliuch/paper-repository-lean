import ELV.OracleReflection
import ELV.LpTimeStack

/-! Convert reflection-query adversary contributions into two genuine full
state-generating oracle contributions, with exactly twice their norm cost. -/
noncomputable section
namespace ELV.Query
open ELV.Model ELV.Stabilize
variable {n : ℕ} [NeZero n] {C : Type*}

/-- Forward input q and inverse input Z O q, in the actual bidirectional interface. -/
def reflectionWitness (O : Oracle n) (q : lp (fun _ : C => Mspace n) 2) : OracleQuerySpace n C :=
  lpPair.symm (WithLp.toLp 2 (q,lpCongr (answerReflection n) (lpCongr O.unitary q)))

@[simp] lemma reflectionWitness_fst (O : Oracle n) (q : lp (fun _ : C => Mspace n) 2) (i : C) :
    (reflectionWitness O q i).fst = q i := rfl
@[simp] lemma reflectionWitness_snd (O : Oracle n) (q : lp (fun _ : C => Mspace n) 2) (i : C) :
    (reflectionWitness O q i).snd = answerReflection n (O.unitary (q i)) := rfl

/-- The two real query gates each process the same norm. -/
theorem reflectionWitness_norm_sq (O : Oracle n) (q : lp (fun _ : C => Mspace n) 2) :
    ‖reflectionWitness O q‖ ^ 2 = 2*‖q‖ ^ 2 := by
  unfold reflectionWitness
  rw [LinearIsometryEquiv.norm_map,WithLp.prod_norm_sq_eq_of_L2]
  change ‖q‖ ^ 2 + ‖lpCongr (answerReflection n) (lpCongr O.unitary q)‖ ^ 2 = _
  rw [LinearIsometryEquiv.norm_map,LinearIsometryEquiv.norm_map]
  ring

lemma bidirectional_reflectionWitness (O : Oracle n) (q : lp (fun _ : C => Mspace n) 2) :
    bidirectional C O (reflectionWitness O q) =
      lpPair.symm (WithLp.toLp 2 (lpCongr O.unitary q,lpCongr O.pulledReflection q)) := by
  apply Subtype.ext
  funext i
  rfl

/-- Telescope through O, the fixed Z, and O inverse, for two arbitrary completions. -/
theorem reflectionWitness_filter (Ox Oy : Oracle n)
    (qx qy : lp (fun _ : C => Mspace n) 2) :
    inner ℂ (reflectionWitness Ox qx) (reflectionWitness Oy qy) -
      inner ℂ (bidirectional C Ox (reflectionWitness Ox qx))
        (bidirectional C Oy (reflectionWitness Oy qy)) =
      inner ℂ qx qy - inner ℂ (lpCongr Ox.pulledReflection qx) (lpCongr Oy.pulledReflection qy) := by
  rw [bidirectional_reflectionWitness,bidirectional_reflectionWitness]
  unfold reflectionWitness
  rw [LinearIsometryEquiv.inner_map_map,LinearIsometryEquiv.inner_map_map]
  change (inner ℂ qx qy + inner ℂ (lpCongr (answerReflection n) (lpCongr Ox.unitary qx))
    (lpCongr (answerReflection n) (lpCongr Oy.unitary qy))) -
      (inner ℂ (lpCongr Ox.unitary qx) (lpCongr Oy.unitary qy) +
       inner ℂ (lpCongr Ox.pulledReflection qx) (lpCongr Oy.pulledReflection qy)) = _
  rw [LinearIsometryEquiv.inner_map_map]
  ring

lemma bidirectional_timeStack {I : Type*} [Fintype I] (O : Oracle n)
    (v : I → OracleQuerySpace n C) :
    bidirectional (I × C) O (timeStack v) = timeStack (fun i => bidirectional C O (v i)) := rfl

end ELV.Query
