import Paper19.UniformConstruction
import Paper19.NatReductions

namespace Paper19
open UniformOracleComputable

/-- A single oracle containing the input tree and the proposed solution. -/
def joinOracle (t s : Stream) (n : ℕ) : ℕ := if n%2=0 then t (n/2) else s (n/2)
def treePart (o : Stream) (n : ℕ) : ℕ := o (2*n)
def solutionPart (o : Stream) (n : ℕ) : ℕ := o (2*n+1)

@[simp] theorem treePart_join (t s : Stream) : treePart (joinOracle t s)=t := by
  funext n; simp [treePart,joinOracle]
@[simp] theorem solutionPart_join (t s : Stream) : solutionPart (joinOracle t s)=s := by
  funext n; simp [solutionPart,joinOracle]

theorem treePart_uniform : UniformOracleComputable treePart :=
  query.comp (base (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id).to_comp)
theorem solutionPart_uniform : UniformOracleComputable solutionPart :=
  query.comp (base (Primrec.succ.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id)).to_comp)

noncomputable def forwardAllProgram (o : Stream) (n : ℕ) : ℕ :=
  rankProgram (treePart o) (rawIsoProgram (solutionPart o) (enumProgram (treePart o) n))

noncomputable def rawFromAllProgram (o : Stream) (n : ℕ) : ℕ :=
  enumProgram (treePart o) (solutionPart o (rankProgram (treePart o) n))

noncomputable def backwardAllProgram (o : Stream) : Stream := backwardIsoProgram (rawFromAllProgram o)

theorem forwardAll_uniform : UniformOracleComputable forwardAllProgram :=
  (rankProgram_uniform.substitute treePart_uniform).comp
    ((rawIso_uniform.substitute solutionPart_uniform).comp (enumProgram_uniform.substitute treePart_uniform))

theorem rawFromAll_uniform : UniformOracleComputable rawFromAllProgram :=
  (enumProgram_uniform.substitute treePart_uniform).comp
    (solutionPart_uniform.comp (rankProgram_uniform.substitute treePart_uniform))

theorem backwardAll_uniform : UniformOracleComputable backwardAllProgram :=
  backwardIso_uniform.substitute rawFromAll_uniform

@[simp] theorem forwardAll_correct (T : Tree) (o : Stream) :
    forwardAllProgram (joinOracle (treeOracle T) o)=forwardNatProgram T o := by
  funext n
  simp [forwardAllProgram,forwardNatProgram]

@[simp] theorem backwardAll_correct (T : Tree) (o : Stream) :
    backwardAllProgram (joinOracle (treeOracle T) o)=backwardNatProgram T o := by
  unfold backwardAllProgram backwardNatProgram rawFromAllProgram rawFromNatProgram
  simp only [treePart_join,solutionPart_join,enumProgram_correct,rankProgram_correct]

/-- The root-completion step is itself one fixed oracle program, so empty
source trees need no nonuniform preprocessing. -/
def rootOracleProgram (o : Stream) (n : ℕ) : ℕ :=
  if Denumerable.ofNat Node n=[] then 1 else o n

theorem rootOracle_uniform : UniformOracleComputable rootOracleProgram := by
  have he := (Primrec.eq.comp (Primrec.ofNat Node) (Primrec.const ([] : Node))).decide.to_comp
  exact (cond (base he) (const 1) query).of_eq (by simp [rootOracleProgram,Bool.cond_decide])

def InputTree.oracle (T : InputTree) : Stream := fun c =>
  if T.mem (Denumerable.ofNat Node c) then 1 else 0

@[simp] theorem rootOracle_correct (T : InputTree) : rootOracleProgram T.oracle=treeOracle T.rootCompletion := by
  funext n
  by_cases h : Denumerable.ofNat Node n=[] <;>
    simp [rootOracleProgram,treeOracle,InputTree.oracle,InputTree.rootCompletion,h]

theorem treeOracle_computable (T : Tree) (hT : ComputablePred T.mem) : Computable (treeOracle T) := by
  exact (hT.comp' (Primrec.ofNat Node).to_comp).ite (Computable.const 1) (Computable.const 0)

theorem InputTree.oracle_computable (T : InputTree) (hT : ComputablePred T.mem) : Computable T.oracle := by
  exact (hT.comp' (Primrec.ofNat Node).to_comp).ite (Computable.const 1) (Computable.const 0)

/-- Explicit uniformity certificates for every field of the constructor and
both solution conversions. All program derivations precede the quantifier
for T, and use no extendibility oracle or ordinal bound as input. -/
def UniformConstructionStatement : Prop :=
  (∀ tag, (constructorPrograms tag).Uniform) ∧
  UniformOracleComputable rootOracleProgram ∧
  UniformOracleComputable forwardAllProgram ∧
  UniformOracleComputable backwardAllProgram ∧
  (∀ (T : InputTree) tag,
    (constructorPrograms tag).run (rootOracleProgram T.oracle)=natModel T.rootCompletion tag) ∧
  (∀ (T : InputTree) o,
    forwardAllProgram (joinOracle (rootOracleProgram T.oracle) o)=forwardNatProgram T.rootCompletion o) ∧
  (∀ (T : InputTree) o,
    backwardAllProgram (joinOracle (rootOracleProgram T.oracle) o)=backwardNatProgram T.rootCompletion o)

theorem uniform_construction_all_inputs : UniformConstructionStatement :=
  ⟨constructorPrograms_uniform,rootOracle_uniform,forwardAll_uniform,backwardAll_uniform,
    fun T tag => by rw [rootOracle_correct]; exact constructorPrograms_correct _ tag,
    fun T o => by rw [rootOracle_correct]; exact forwardAll_correct _ o,
    fun T o => by rw [rootOracle_correct]; exact backwardAll_correct _ o⟩

end Paper19
