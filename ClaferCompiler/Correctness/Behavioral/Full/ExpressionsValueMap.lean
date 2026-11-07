module

public import ClaferCompiler.Correctness.Behavioral.Full.ExpressionsFormulaMap
public import ClaferCompiler.Correctness.Behavioral.Full.ExpressionsBuilt

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral.Full.Expressions
open Backend.Alloy.Temporal
open Backend.Alloy.Behavioral.Full
open Backend.Alloy.Behavioral.Full.Expressions

theorem forall₂_member_left {R : α → β → Prop} {xs : List α} {ys : List β}
    (paired : List.Forall₂ R xs ys) (x : α) (hx : x ∈ xs) : ∃ y ∈ ys, R x y := by
  induction paired with
  | nil => simp at hx
  | cons hp ht ih =>
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨_, List.mem_cons_self, hp⟩
    · obtain ⟨y, hy, hr⟩ := ih hx
      exact ⟨y, List.mem_cons_of_mem _ hy, hr⟩

def valueResult (f : α → Result (Value β)) (x : α) : Value β :=
  match f x with | .ok value => value | .error _ => .missing

theorem valueMapM_expansion (a : Value α) (f : α → Result (Value β))
    (success : valueMapM a f = .ok result) :
    result = a.bind (valueResult f) ∧
      ∀ g x, (g, x) ∈ a.cases → ∃ body, f x = .ok body := by
  unfold valueMapM at success
  cases run : a.cases.mapM (fun input =>
      (fun (value : Value β) => value.cases.map fun output =>
        (Formula.binary .conj input.1 output.1, output.2)) <$> f input.2) with
  | error err => simp [run] at success
  | ok choices =>
    have paired := mapM_ok _ _ _ run
    have canonical : List.Forall₂ (fun input output => output =
        (valueResult f input.2).cases.map (fun entry => (Formula.binary .conj input.1 entry.1, entry.2))) a.cases choices := by
      apply paired.imp
      intro input output ho
      cases hf : f input.2 with
      | error err => simp [hf] at ho
      | ok value =>
        have eq : value.cases.map (fun entry => (Formula.binary .conj input.1 entry.1, entry.2)) = output := by
          simpa [hf, bind, Except.bind, pure, Except.pure] using ho
        simpa [valueResult, hf] using eq.symm
    have eq : choices = a.cases.map (fun input =>
        (valueResult f input.2).cases.map (fun entry => (Formula.binary .conj input.1 entry.1, entry.2))) := by
      rw [← List.forall₂_eq_eq_eq, List.forall₂_map_right_iff]
      exact canonical.flip
    constructor
    · have resultEq : Value.mk choices.flatten = result := by simpa [run] using success
      rw [← resultEq, eq]
      rfl
    · intro g x hx
      obtain ⟨output, _, ho⟩ := forall₂_member_left paired (g, x) hx
      cases hf : f x with
      | error err => simp [hf] at ho
      | ok value => exact ⟨value, rfl⟩

theorem valueResult_built (f : α → Result (Value β))
    (bodies : ∀ x result, f x = .ok result → Full.Value.Built result) (x : α) :
    Full.Value.Built (valueResult f x) := by
  cases hf : f x with
  | error err => intro g y hy; simp [valueResult, hf, Value.missing] at hy
  | ok value => simpa [valueResult, hf] using bodies x value hf

-- [proof->req~compiler-behavioral-partial-lowering~1]
theorem valueMapM_meaning (a : Value α) (f : α → Result (Value β))
    (ha : Full.Value.Built a)
    (bodies : ∀ x result, f x = .ok result → Full.Value.Built result)
    (success : valueMapM a f = .ok result) :
    Full.Value.Meaning s w τ e t result y ↔
      ∃ x body, Full.Value.Meaning s w τ e t a x ∧ f x = .ok body ∧
        Full.Value.Meaning s w τ e t body y := by
  obtain ⟨rfl, branches⟩ := valueMapM_expansion a f success
  rw [Full.Value.bind_meaning a _ ha (valueResult_built f bodies)]
  constructor
  · rintro ⟨x, hx, hy⟩
    obtain ⟨g, hg, hh⟩ := hx
    obtain ⟨body, hb⟩ := branches g x hg
    exact ⟨x, body, ⟨g, hg, hh⟩, hb, by simpa [valueResult, hb] using hy⟩
  · rintro ⟨x, body, hx, hb, hy⟩
    exact ⟨x, hx, by simpa [valueResult, hb] using hy⟩

end ClaferCompiler.Correctness.Behavioral.Full.Expressions
