module

public import ClaferCompiler.Correctness.Behavioral.Full.Frontend
public import ClaferCompiler.SemanticsBridge.Behavioral.Source

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral.Full
open Frontend.Behavioral

/-- Reuse the standard vector traversal equation to recover each successful
element elaboration; no custom traversal is introduced into the compiler. -/
theorem vector_ofFnM_success {α ε : Type} {n : Nat} {f : Fin n → Except ε α}
    {values : Vector α n} (success : Vector.ofFnM f = .ok values) :
    ∀ i, f i = .ok values[i] := by
  induction n with
  | zero => intro i; exact Fin.elim0 i
  | succ n ih =>
    rw [Vector.ofFnM_succ] at success
    cases prior : Vector.ofFnM (fun i => f i.castSucc) with
    | error err => rw [prior] at success; contradiction
    | ok previous =>
      cases last : f (Fin.last n) with
      | error err => rw [prior, last] at success; contradiction
      | ok value =>
        have same : previous.push value = values := by
          simpa [prior, last, bind, Except.bind, pure, Except.pure] using success
        subst values
        intro i
        by_cases h : i.val < n
        · have hi := ih prior ⟨i.val, h⟩
          simpa [Vector.getElem_push_lt h] using hi
        · have same : i = Fin.last n := Fin.ext (by simp; omega)
          subst i
          simpa using last

/-- Every source inventory entry retains its independent elaboration derivation.
Declaration resolution and modifier spelling already carry their own evidence. -/
structure SourceElaborated (e : Elaborated source) : Prop where
  authored : ∀ i : Fin (properties e.declarations).length,
    Frontend.Behavioral.Expressions.FormulaElaborates e.model.structural
      (properties e.declarations)[i].owner (properties e.declarations)[i].expression e.bodies[i]
  generated : ∀ i : Fin e.headers.length,
    HeaderElaborates e.declarations e.headers[i] e.headerBodies[i]

-- [proof->req~compiler-behavioral-elaboration~1]
theorem elaborate_source (success : elaborate profile source = .ok e) : SourceElaborated e := by
  unfold elaborate at success
  cases declarations : bindDeclarations profile source with
  | error err => rw [declarations] at success; contradiction
  | ok d =>
    simp only [declarations, bind, Except.bind] at success
    cases modifiers : bindModifiers d with
    | error err => rw [modifiers] at success; contradiction
    | ok mods =>
      simp only [modifiers] at success
      cases bodies : Vector.ofFnM (fun i : Fin (properties d).length =>
          Frontend.Behavioral.Expressions.elaborate source d.resolved.admitted
            (properties d)[i].owner (source.source.utf8ByteSize + 1) (properties d)[i].expression) with
      | error err => rw [bodies] at success; contradiction
      | ok bs =>
        simp only [bodies] at success
        cases headers : headerProperties d with
        | error err => rw [headers] at success; contradiction
        | ok hs =>
          simp only [headers] at success
          cases generated : Vector.ofFnM (fun i : Fin hs.length => elaborateHeader d hs[i]) with
          | error err => rw [generated] at success; contradiction
          | ok gs =>
            have same : (⟨d, mods, bs, hs, gs⟩ : Elaborated source) = e := by
              simpa only [generated, bind, Except.bind, pure, Except.pure, Except.ok.injEq] using success
            subst e
            constructor
            · intro i
              exact Frontend.Behavioral.Expressions.elaborate_sound (vector_ofFnM_success bodies i)
            · intro i
              exact elaborateHeader_sound (vector_ofFnM_success generated i)

theorem check_model {source : Frontend.Behavioral.Document}
    (e : Elaborated source)
    {request : Backend.Alloy.Behavioral.Full.Request e.declarations.resolved.count}
    (success : e.check index = .ok request) : request.model = e.model := by
  unfold Elaborated.check at success
  split at success
  · cases success; rfl
  · contradiction

-- [proof->req~compiler-behavioral-property-commands~1]
theorem check_source {source : Document} (e : Elaborated source)
    {request : Backend.Alloy.Behavioral.Full.Request e.declarations.resolved.count}
    (success : e.check index = .ok request) :
    ∃ i : Fin e.model.assertions.length, i.val = index ∧ request = ⟨e.model, .check i⟩ := by
  unfold Elaborated.check at success
  split at success
  · rename_i h
    cases success
    exact ⟨⟨index, h⟩, rfl, rfl⟩
  · contradiction

theorem run_model {source : Frontend.Behavioral.Document}
    (e : Elaborated source)
    (scenarios : List (ScenarioSource e.declarations.resolved.count))
    {request : Backend.Alloy.Behavioral.Full.Request e.declarations.resolved.count}
    (success : e.run scenarios = .ok request) : request.model = e.model := by
  unfold Elaborated.run at success
  simp only [bind, Except.bind] at success
  split at success
  · contradiction
  · cases success; rfl

/-- Successful scenario elaboration retains every body, attachment and source
span in the original order. Non-constraint elements have no successful derivation. -/
def ScenarioElementElaborated {source : Document} (e : Elaborated source)
    (scenario : ScenarioSource e.declarations.resolved.count)
    (element : Frontend.Behavioral.Element)
    (constraints : List (Backend.Alloy.Behavioral.Full.Constraint e.declarations.resolved.count)) : Prop :=
  match element with
  | .property .constraint bodies span => Traversal.Related
      (fun body a => a.owner = scenario.owner ∧ a.source = span ∧
        Expressions.FormulaElaborates e.model.structural scenario.owner body a.body) bodies constraints
  | _ => False

def ScenarioElaborated {source : Document} (e : Elaborated source)
    (scenario : ScenarioSource e.declarations.resolved.count)
    (constraints : List (Backend.Alloy.Behavioral.Full.Constraint e.declarations.resolved.count)) : Prop :=
  ∃ lists, Traversal.Related (ScenarioElementElaborated e scenario) scenario.document.elements lists ∧
    lists.flatten = constraints

-- [proof->req~compiler-behavioral-elaboration~1]
theorem run_source {source : Document} (e : Elaborated source)
    (scenarios : List (ScenarioSource e.declarations.resolved.count))
    {request : Backend.Alloy.Behavioral.Full.Request e.declarations.resolved.count}
    (success : e.run scenarios = .ok request) :
    ∃ lists, Traversal.Related (ScenarioElaborated e) scenarios lists ∧
      request = ⟨e.model, .run lists.flatten⟩ := by
  unfold Elaborated.run at success
  simp only [ValueRules.bind_success] at success
  obtain ⟨lists, lowered, result⟩ := success
  cases Except.ok.inj result
  refine ⟨lists, Traversal.list_relation ?_ lowered, rfl⟩
  intro scenario constraints success
  simp only [ValueRules.bind_success] at success
  obtain ⟨elements, lowered, result⟩ := success
  cases Except.ok.inj result
  refine ⟨elements, Traversal.list_relation ?_ lowered, rfl⟩
  intro element bodies success
  cases element with
  | declaration header children => contradiction
  | enumeration name literals span => contradiction
  | property kind expressions span =>
    cases kind with
    | assertion => contradiction
    | constraint =>
      apply Traversal.list_relation ?_ success
      intro body a success
      simp only [ValueRules.bind_success] at success
      obtain ⟨formula, lowered, result⟩ := success
      cases Except.ok.inj result
      exact ⟨rfl, rfl, Expressions.elaborate_sound lowered⟩

end ClaferCompiler.Correctness.Behavioral.Full
