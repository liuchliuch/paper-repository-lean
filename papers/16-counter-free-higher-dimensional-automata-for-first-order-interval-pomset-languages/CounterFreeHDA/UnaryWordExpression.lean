import CounterFreeHDA.UnaryBlockLanguage
import CounterFreeHDA.LiveProfileTable

namespace CounterFreeHDA.Appendix.Residual
open Cubical Compare

theorem cube_eq_of_dim {U V : UCube} (h : U.dim = V.dim) : U = V := by
  rcases U with ⟨u,lu⟩
  rcases V with ⟨v,lv⟩
  have huv : u = v := Fin.ext h
  subst v
  exact congrArg (Sigma.mk u) (Subsingleton.elim lu lv)

theorem dead_word {U V : UCube} (p : Word U V) : wordKind p (dead U.1) = dead V.1 := by
  have hstep {U V : UCube} (s : Step U V) : stepKind s (dead U.1) = dead V.1 := by
    apply Fin.ext
    exact congrArg (fun x : Fin 4 => x.val) ((code_step s (dead U.1)).trans (code_dead_step s))
  induction p with
  | nil => rfl
  | cons s p ih => simpa only [wordKind,hstep] using ih

private theorem expression_prepend {c p : ClosedWord} (hc : ConcurrentBlock c) (hp : ExpressionWord p) :
    ExpressionWord (c.append p) := by
  cases hp with
  | star hs => exact .star (.cons hc hs)
  | tail hs ha hn =>
    rw [← Word.append_assoc]
    exact .tail (.cons hc hs) ha hn

/-- Every accepted closed ST word has exactly the displayed regular
expression C* union C*aP+, with actual concurrent blocks. -/
theorem accepts_expression (p : ClosedWord) (ha : acceptBit (wordKind p (0 : Fin 4)) = true) : ExpressionWord p := by
  generalize hn : p.length = n
  induction n using Nat.strong_induction_on generalizing p with
  | h n ih =>
    cases p with
    | nil => exact .star .nil
    | @cons Z U Z' s p =>
      cases s with
      | stop f hu hd => change 0 = U.dim+1 at hd; omega
      | start f hf hd =>
        have hU : U = Unary.one := cube_eq_of_dim hd
        subst U
        cases p with
        | @cons U V Z s2 p =>
          cases s2 with
          | stop g hg hgd =>
            have hV : V = Unary.zero := cube_eq_of_dim (by change 1 = V.dim+1 at hgd; change V.dim = 0; omega)
            subst V
            let c : ClosedWord := .cons (.start f hf hd) (.cons (.stop g hg hgd) (.nil _))
            have hc : SingleBlock c := .mk f g hf hg hd
            have hac : acceptBit (wordKind p (1 : Fin 4)) = true := ha
            have hp := (closed_word_B p).mp hac
            exact .tail .nil hc hp
          | start g hg hgd =>
            have hV : V = Unary.two := cube_eq_of_dim (by change V.dim = 1+1 at hgd; exact hgd)
            subst V
            cases p with
            | @cons V W Z s3 p =>
              cases s3 with
              | start h hh hhd =>
                have hb := W.1.isLt
                change W.dim = 2+1 at hhd
                change W.dim < 3 at hb
                omega
              | stop h hh hhd =>
                have hW : W = Unary.one := cube_eq_of_dim (by change 2 = W.dim+1 at hhd; change W.dim = 1; omega)
                subst W
                cases p with
                | @cons W T Z s4 p =>
                  cases s4 with
                  | start l hl hld =>
                    have hT : T = Unary.two := cube_eq_of_dim (by change T.dim = 1+1 at hld; exact hld)
                    subst T
                    have hfalse : acceptBit (wordKind p (dead Unary.two.1)) = true := ha
                    rw [dead_word] at hfalse
                    change false = true at hfalse
                    cases hfalse
                  | stop l hl hld =>
                    have hT : T = Unary.zero := cube_eq_of_dim (by change 1 = T.dim+1 at hld; change T.dim = 0; omega)
                    subst T
                    let c : ClosedWord := .cons (.start f hf hd) (.cons (.start g hg hgd)
                      (.cons (.stop h hh hhd) (.cons (.stop l hl hld) (.nil _))))
                    have hc : ConcurrentBlock c := .mk f g h l hf hg hh hl hd hgd hhd hld
                    have hap : acceptBit (wordKind p (0 : Fin 4)) = true := ha
                    have hp : ExpressionWord p := ih p.length (by change (((p.length+1)+1)+1)+1 = n at hn; omega) p hap rfl
                    exact expression_prepend hc hp

end CounterFreeHDA.Appendix.Residual
