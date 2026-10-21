module

public import ClaferCompiler.Correctness.ExpressionMeaning

/-! [proof->req~compiler-expression-encoding~1] -/

@[expose] public section
namespace ClaferCompiler.Correctness.ExpressionMeaning
open Backend.Alloy Backend.Alloy.Expressions IR.Expr SemanticsBridge.Expr
open ExpressionRelations ExpressionConstruction

@[simp] theorem propBool_bool (b : Bool) : propBool (b = true) = b := by
  cases b <;> simp [propBool]

theorem lifted_true (p : ULift Prop) : p = ⟨True⟩ ↔ p.down := by
  cases p with
  | up p => simp only [ULift.up.injEq, eq_iff_iff, iff_true]

theorem agrees_all {s : Support n m} {f : Atom → Nat} {w : Nat} {i : Instance}
    {env : List Nat} {x : Fin n} {S : Set Atom}
    {d : Code (.collection (.objects x))} {c : Code (.boolean : Ty n)}
    (hd : Built d) (hc : Built c) (hdom : Agrees s f w i env (some S) d)
    (body : Atom → Option (ULift Prop))
    (hbody : ∀ a ∈ S, Agrees s f w i (f a :: env) (body a) c) :
    Agrees s f w i env (t := .boolean) (Clafer.Constraints.universal S body)
      ⟨.conj d.defined (.all d.value c.defined), .all d.value c.value⟩ := by
  classical
  have hr : Unary f S (d.value.eval i env) := hdom.2 S rfl
  have hdef : (Clafer.Constraints.universal S body).isSome =
      propBool (∀ a ∈ S, (body a).isSome = true) := by
    unfold Clafer.Constraints.universal
    split <;> simp_all [propBool]
  constructor
  · rw [Formula.eval_conj hd.1 (.all _ hc.1), hdom.1]
    rw [eval_all_prop hc.1 hr (fun a => (body a).isSome = true) (by
      intro a ha
      simpa only [propBool_bool] using (hbody a ha).1)]
    simp only [bind, Option.bind, pure, Pure.pure, Option.isSome_some, Bool.true_and, hdef]
  · intro p hp
    unfold Clafer.Constraints.universal at hp
    split at hp
    · rename_i hall
      have he : (⟨∀ a ∈ S, body a = some ⟨True⟩⟩ : ULift Prop) = p := Option.some.inj hp
      subst p
      apply eval_all_prop hc.2 hr
      intro a ha
      obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp (hall a ha)
      have hv := (hbody a ha).2 p hp
      change c.value.eval w i (f a :: env) = some (propBool p.down) at hv
      rw [hp, hv]
      congr 2
      exact propext (by simp only [Option.some.injEq, lifted_true])
    · cases hp

end ClaferCompiler.Correctness.ExpressionMeaning
