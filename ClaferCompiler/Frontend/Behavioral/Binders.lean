module

public import ClaferCompiler.Frontend.Behavioral.Surface
public import ClaferCompiler.Frontend.Resolve
public import ClaferCompiler.IR.Behavioral.Binders

@[expose] public section
namespace ClaferCompiler.Frontend.Behavioral.Binders

/-- Anonymous generated captures are deliberately absent from source lookup.
The parameter retains the expression elaborator's type information. -/
abbrev Context (α : Type) (n : Nat) := Vector (Option (Name × α)) n

def First (Γ : Context α n) (name : String) (i : Fin n) : Prop :=
  ∀ j : Fin n, j.val < i.val → (Γ[j].map (fun a => a.1.text)) ≠ some name

instance (Γ : Context α n) (name : String) (i : Fin n) : Decidable (First Γ name i) := by
  unfold First; infer_instance

/-- Independent nearest-binding rule, including the original declaration token. -/
structure Lookup (Γ : Context α n) (name : String) where
  index : Fin n
  token : Name
  type : α
  entry : Γ[index] = some (token, type)
  spelling : token.text = name
  first : First Γ name index

-- [impl->req~compiler-behavioral-elaboration~1]
def lookup (Γ : Context α n) (name : String) : Option (Lookup Γ name) := Id.run do
  for i in List.finRange n do
    match hi : Γ[i] with
    | none => pure ()
    | some (token, type) =>
      if hn : token.text = name then
        if hf : First Γ name i then return some ⟨i, token, type, hi, hn, hf⟩
  return none

/-- Source order is reversed in lexical indices. Exactly one hidden domain
capture separates the group's locals from the enclosing environment. -/
def context (Γ : Context α n) (names : List Name) (type : α) :
    Context α (n + 1 + names.length) :=
  Vector.ofFn fun i : Fin (n + 1 + names.length) => if h : i.val < names.length then
    some (names[ names.length - (i.val + 1) ], type)
  else if he : i.val = names.length then none
  else Γ[(⟨i.val - (names.length + 1), by omega⟩ : Fin n)]

-- [proof->req~compiler-behavioral-elaboration~1]
theorem context_local (Γ : Context α n) (names : List Name) (type : α) (i : Fin names.length) :
    (context Γ names type)[(⟨i.val, by omega⟩ : Fin (n + 1 + names.length))] =
      some (names[names.length - (i.val + 1)], type) := by
  simp [context, i.isLt]

theorem context_hidden (Γ : Context α n) (names : List Name) (type : α) :
    (context Γ names type)[(⟨names.length, by omega⟩ : Fin (n + 1 + names.length))] = none := by simp [context]

theorem context_outer (Γ : Context α n) (names : List Name) (type : α) (i : Fin n) :
    (context Γ names type)[(⟨i.val + (names.length + 1), by omega⟩ : Fin (n + 1 + names.length))] = Γ[i] := by
  simp [context, show ¬ i.val + (names.length + 1) < names.length by omega,
    show i.val + (names.length + 1) ≠ names.length by omega]

def Legal (names : List Name) : Prop :=
  names ≠ [] ∧ (∀ name ∈ names, Resolution.reserved name.text = false) ∧
    (names.map (·.text)).Nodup

instance (names : List Name) : Decidable (Legal names) := by unfold Legal; infer_instance

structure Plan (Γ : Context α n) (names : List Name) (type : α) : Type where
  legal : Legal names

def Plan.bodyContext {Γ : Context α n} {names : List Name} {type : α}
    (_ : Plan Γ names type) : Context α (n + 1 + names.length) :=
  context Γ names type

-- [impl->req~compiler-diagnostics~1]
def prepare (Γ : Context α n) (quantifier : Token) (names : List Name) (type : α) :
    Except Diagnostic (Plan Γ names type) := do
  for name in names do
    if Resolution.reserved name.text then
      throw (Resolution.errorAt name "behavioral.reserved-binder" "Reserved binder name.")
  if h : Legal names then return ⟨h⟩
  else throw (Resolution.errorAt quantifier "behavioral.binder-group"
    "A binder group must be nonempty and have distinct names.")

def QuantifierSpelling (spelling : String) (q : IR.Behavioral.Quantifier) : Prop :=
  match q with
  | .all => spelling = "all"
  | .some => spelling = "some"
  | .no => spelling = "no" ∨ spelling = "not"
  | .one => spelling = "one"
  | .lone => spelling = "lone"

def quantifier (token : Token) :
    Except Diagnostic {q : IR.Behavioral.Quantifier // QuantifierSpelling token.text q} :=
  if h : token.text = "all" then .ok ⟨.all, h⟩
  else if h : token.text = "some" then .ok ⟨.some, h⟩
  else if h : token.text = "no" ∨ token.text = "not" then .ok ⟨.no, h⟩
  else if h : token.text = "one" then .ok ⟨.one, h⟩
  else if h : token.text = "lone" then .ok ⟨.lone, h⟩
  else .error (Resolution.errorAt token "behavioral.quantifier" "Unknown quantifier.")

end ClaferCompiler.Frontend.Behavioral.Binders
