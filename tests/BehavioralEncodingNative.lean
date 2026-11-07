module

public import tests.BehavioralNative
public import tests.ComparisonNative
public import ClaferCompiler.Backend.Alloy.Behavioral.Representation
public import ClaferCompiler.Backend.Alloy.Temporal.Print

@[expose] public section
namespace ClaferCompiler.Tests.BehavioralEncoding
open IR.Behavioral
open Backend.Alloy (Scope)

def document (f : Formula 4 0) (d : Fin 4) : Document 4 :=
  { Behavioral.document with attachments :=
    [{id := 74, owner := d.val, body := .formula f}] }

def admitted (f : Formula 4 0) (d : Fin 4) : Admitted 4 where
  document := document f d
  version := rfl
  profile := rfl
  coreChecked := by change IR.Structural.coreChecks Behavioral.core Behavioral.certificate; decide
  supportChecked := by change IR.Structural.supportChecks Behavioral.core Behavioral.certificate; decide
  metadataChecked := by
    constructor
    · change [74].Nodup
      decide
    constructor
    · intro a ha
      have he : a = {id := 74, owner := d.val, body := .formula f} := List.mem_singleton.mp ha
      subst a
      constructor
      · exact ⟨d, by simp [document, Behavioral.document, Behavioral.core, IR.Structural.Core.get]⟩
      · intro span hs
        cases hs
    · change ∀ i : Fin 4, ∀ span ∈ (Behavioral.core.get i).source, span.startByte ≤ span.endByte
      decide
  bodiesChecked := by simp [supportedBodies, document, Attachment.Supported]

def bounds : Backend.Alloy.Behavioral.Bounds :=
  ⟨⟨[(0, ⟨1, true⟩), (1, ⟨2, true⟩), (2, ⟨2, true⟩), (3, ⟨1, true⟩)], 6, 5⟩, 4, 4⟩

/-- Two reference heads distinguish bag occurrences even when their targets agree.
The first parent disappears at phase 2 and reappears at phase 3. -/
def identities : Identities 4 6 :=
  ⟨#v[100, 101, 102, 103, 104, 105], 0,
    #v[0, 1, 1, 2, 2, 3], #v[none, some 0, some 0, some 1, some 1, some 0]⟩

def frame (i : Fin 4) : Frame 4 6 where
  live := Vector.ofFn fun x => decide (x = 0 ∨ x = 5 ∨
    (x = 1 ∧ i ≠ 2) ∨ (x = 2 ∧ i = 2) ∨
    (x = 3 ∧ (i = 0 ∨ i = 3)) ∨ (x = 4 ∧ i = 0))
  references := if i = 0 then [(2, 3, 5), (2, 4, 5)]
    else if i = 3 then [(2, 3, 5)] else []

def stable : Lasso 4 6 4 := ⟨identities, Vector.ofFn frame, 0⟩

/-- A new head belongs to a different fixed parent; the old head is not renamed. -/
def replaced : Lasso 4 6 4 :=
  {stable with
    identities := {identities with parent := identities.parent.set 4 (some 2)}
    frames := Vector.ofFn fun i =>
      if i = 0 then ⟨#v[true, true, false, true, false, true], [(2, 3, 5)]⟩
      else if i = 3 then ⟨#v[true, false, true, false, true, true], [(2, 4, 5)]⟩
      else frame i }

/-- Each live reference head's own parent is absent in the next state. -/
def alternating : Lasso 4 6 4 :=
  {stable with
    identities := {identities with parent := identities.parent.set 4 (some 2)}
    frames := #v[
      ⟨#v[true, true, false, true, false, true], [(2, 3, 5)]⟩,
      ⟨#v[true, false, true, false, true, true], [(2, 4, 5)]⟩,
      ⟨#v[true, true, false, false, false, true], []⟩,
      ⟨#v[true, false, true, false, false, true], []⟩] }

def conjoin (fs : List Backend.Alloy.Temporal.Formula) : Backend.Alloy.Temporal.Formula := fs.foldr (.binary .conj) .truth
def atom (objects : List Nat) (x : Nat) : Backend.Alloy.Temporal.Rel := .var (objects.idxOf x)
def set (objects xs : List Nat) : Backend.Alloy.Temporal.Rel := xs.foldr (fun x r => .union (atom objects x) r) (.empty .unary)
def relation (objects : List Nat) (rows : Backend.Alloy.Relation) : Backend.Alloy.Temporal.Rel :=
  rows.foldr (fun row r => match row with
    | [x, y] => .union (.product (atom objects x) (atom objects y)) r
    | _ => r) (.empty .binary)

def statePin (objects : List Nat) (s : Backend.Alloy.Instance) : Backend.Alloy.Temporal.Formula :=
  conjoin (s.signatures.zipIdx.map (fun (xs, i) => .equal (.sig i) (set objects xs)) ++
    s.fields.zipIdx.map (fun (rows, i) => .equal (.field i) (relation objects rows)))

/-- Pins the actual encoder's observations using one frozen enumeration. All
four frames differ, so the fifth observation fixes the loop entry uniquely. -/
def tracePin (l : Backend.Alloy.Temporal.Lasso) : Backend.Alloy.Temporal.Formula :=
  let states := l.frames.zipIdx.map fun (s, t) =>
    Nat.repeat (Backend.Alloy.Temporal.Formula.unary .after) t (statePin l.inventory s)
  let atLoop := Nat.repeat (Backend.Alloy.Temporal.Formula.unary .after) l.frames.length
    (statePin l.inventory (l.frames[l.loop]'(l.loopValid)))
  let distinct := (List.range l.inventory.length).flatMap fun x =>
    ((List.range x).map fun y => Backend.Alloy.Temporal.Formula.unary .neg (.equal (.var x) (.var y)))
  Nat.repeat (Backend.Alloy.Temporal.Formula.exists_ (.sig 0)) l.inventory.length
    (conjoin (distinct ++ states ++ [atLoop]))

def falsehood : Formula 4 n := .atom (.inhabited .empty)
def hasThis : Formula 4 n := .atom (.inhabited .this)
def hasParent : Formula 4 n := .atom (.inhabited (.thisStep .parent))

structure Case where
  name : String
  expected : Bool
  formula : Formula 4 0 := .truth
  owner : Fin 4 := 2
  trace : Lasso 4 6 4 := stable
  enough : sizeOf formula < 256

def sample (name : String) (expected : Bool) (formula : Formula 4 0 := .truth)
    (owner : Fin 4 := 2) (trace : Lasso 4 6 4 := stable)
    (enough : sizeOf formula < 256 := by decide) : Case :=
  ⟨name, expected, formula, owner, trace, enough⟩

-- [utest->req~compiler-behavioral-encoding~1]
-- [utest->req~compiler-behavioral-correctness~1]
/-- Expected results follow the source parent lifetime. Object death alone does
not cancel X; a parent gap cancels F and U even when its identity returns. -/
def cases : List Case := [
  (sample "stable-bag" true),
  (sample "replaced-head" true .truth 2 replaced),
  (sample "next-object-death" false falsehood.next),
  (sample "next-parent-visible" true hasParent.next),
  (sample "next-parent-cancellation" true falsehood.next 2 alternating),
  (sample "negative-next-parent-cancellation" true (Formula.next .truth).not 2 alternating),
  (sample "eventual-parent-cancellation" true falsehood.eventually),
  (sample "eventual-no-root-cancellation" false falsehood.eventually 0),
  (sample "negative-eventually" true falsehood.eventually.not),
  (sample "negative-always" true (Formula.always .truth).not),
  (sample "until-parent-cancellation" true (.strongUntil .truth falsehood)),
  (sample "weak-until" true (.weakUntil .truth falsehood)),
  (sample "negative-until" true (Formula.strongUntil .truth falsehood).not),
  (sample "negative-weak-until" true (Formula.weakUntil .truth falsehood).not),
  (sample "always-self-observed" false hasThis.always),
  (sample "always-parent-observed" true hasParent.always),
  (sample "initial-observation" true hasThis.initially),
  (sample "final-observation" true hasThis.finally),
  (sample "false-at-birth" false falsehood.initially),
  (sample "false-at-death" false falsehood.finally),
  (sample "capture-survives-death" true (.letSet .this (.next (.atom (.inhabited (.var 0)))))),
  (sample "capture-current-navigation" false (.letSet .this (.next (.atom (.inhabited (.step (.deref 2) (.var 0))))))),
  (sample "capture-whole-bag" true (.implies
    (.atom (.inhabited (.diff (.extent 2) .this)))
    (.quant .all (.extent 2) (.letSet (.extent 2)
      (.next (.atom (.inhabited (.diff (.var 0) (.var 1))))))))),
  (sample "one-raw-negation-barrier" false (.quant .one .this falsehood.eventually.not)),
  (sample "negative-one-barrier" true (Formula.quant .one .this falsehood.eventually.not).not),
  (sample "lone-raw-negation-barrier" true (.quant .lone .this falsehood.eventually.not)),
  (sample "all-signed-body" true (.quant .all .this falsehood.eventually.not)),
  (sample "some-signed-body" true (.quant .some .this falsehood.eventually.not)),
  (sample "no-signed-body" true (.quant .no .this falsehood.eventually))]

def compiled (c : Case) : Except Backend.Alloy.Structural.Error Backend.Alloy.Behavioral.Compiled :=
  Backend.Alloy.Behavioral.compile (admitted c.formula c.owner) bounds 256 (by
    intro a ha f hf
    simp only [admitted, document, List.mem_singleton] at ha
    subst a
    cases hf
    exact c.enough)

def writeModule (directory : System.FilePath) (name : String) (expected : Bool)
    (m : Backend.Alloy.Temporal.Module) : IO Unit := do
  let .ok checked := Backend.Alloy.Temporal.check m | throw (IO.userError s!"target admission {name}")
  let .ok out := Backend.Alloy.Temporal.Text.render checked (Backend.Alloy.Temporal.Text.anonymousNames m) |
    throw (IO.userError s!"render {name}")
  IO.FS.writeFile (directory / s!"{name}.als") out.text
  IO.FS.writeFile (directory / s!"{name}.expected") (if expected then "sat" else "bounded_unsat")
  IO.FS.writeFile (directory / s!"{name}.bounds")
    (s!"{m.command.bitwidth}\t{m.command.minSteps}\t{m.command.maxSteps}\n" ++
      String.join (m.command.scopes.zipIdx.map fun (scope, i) =>
        s!"cc{i * 4}\t{scope.size}\t{scope.exact}\n"))

def swapParents (s : Backend.Alloy.Instance) : Backend.Alloy.Instance :=
  let rename := fun x => if x == 101 then 102 else if x == 102 then 101 else x
  {s with signatures := s.signatures.map (List.map rename), fields := s.fields.map (List.map (List.map rename))}

-- [utest->req~compiler-behavioral-encoding~1]
-- [utest->req~compiler-trace-representation~1]
/-- Negative mutants retain valid snapshots but break the shared parent table,
or expose an orphan only after removing the emitted snapshot invariants. -/
def mutations (directory : System.FilePath) : IO Unit := do
  let c := sample "mutations" true
  let .ok compiled := compiled c | throw (IO.userError "mutation base compile")
  let v := (admitted c.formula c.owner).structural.toLayout
  let base := compiled.module.raw
  let encoded := Backend.Alloy.Behavioral.encode v stable
  let renamed := {encoded with frames := encoded.frames.modify 1 swapParents}
  if (Backend.Alloy.Behavioral.decode v renamed).toOption.isSome then
    throw (IO.userError "per-state renaming accepted by decoder")
  let withPin := fun m l => {m with facts := m.facts ++ [tracePin l] : Backend.Alloy.Temporal.Module}
  let noHeads := Backend.Alloy.Temporal.Formula.unary .always
    (.unary .neg (.mult .some (Backend.Alloy.Behavioral.head v 2)))
  let assertion := {base with command := {base.command with kind := .check, body := noHeads}}
  writeModule directory "bag-counterexample" true (withPin assertion encoded)
  writeModule directory "renaming-static-rejected" false (withPin base renamed)
  let mutableParent := {base with schema :=
    {base.schema with mutableFields := base.schema.mutableFields.set 0 true}}
  writeModule directory "renaming-mutable-parent-mutant" true (withPin mutableParent renamed)
  let orphanFrame : Frame 4 6 := ⟨#v[true, false, true, true, false, true], [(2, 3, 5)]⟩
  let orphan := {stable with frames := stable.frames.set 2 orphanFrame}
  let orphanTarget := Backend.Alloy.Behavioral.encode v orphan
  writeModule directory "orphan-rejected" false (withPin base orphanTarget)
  let identityCount := (Backend.Alloy.Behavioral.identityFacts v).length
  let stateCount := (Backend.Alloy.Behavioral.stateFacts v).length
  let kept := base.facts.take identityCount ++ base.facts.drop (identityCount + stateCount)
  let missingStates := {base with facts := kept}
  writeModule directory "missing-state-invariants-mutant" true (withPin missingStates orphanTarget)
  let wrongParent := {stable with identities :=
    {stable.identities with parent := stable.identities.parent.set 3 (some 5)}}
  writeModule directory "wrong-declared-parent-rejected" false
    (withPin base (Backend.Alloy.Behavioral.encode v wrongParent))

-- [utest->req~compiler-trace-representation~1]
/-- Replay actual Analyzer tuples through the production lasso/identity decoder.
The existing numeric table transport is test-only; it invents no source truth. -/
def replay (directory expected : String) : IO Unit := do
  let directory := System.FilePath.mk directory
  let .ok [count, loop] := Comparison.numbers
    (← IO.FS.readFile (directory / "trace.rows")).trimAscii.toString |
      throw (IO.userError "trace header")
  let .ok inventory := Comparison.numbers
    (← IO.FS.readFile (directory / "inventory.rows")).trimAscii.toString |
      throw (IO.userError "trace inventory")
  let frames ← (List.range count).mapM fun t => do
    let .ok frame := Comparison.tables (← IO.FS.readFile (directory / s!"frame-{t}.rows")) |
      throw (IO.userError "frame transport")
    pure frame
  let v := (admitted .truth 2).structural.toLayout
  let .ok lasso := Backend.Alloy.Temporal.checkLasso
    (Backend.Alloy.Behavioral.schema v) inventory frames loop |
      throw (IO.userError "candidate shape")
  match Backend.Alloy.Behavioral.decode v lasso with
  | .error _ =>
      unless expected == "changing-identity" do throw (IO.userError "unexpected decode rejection")
  | .ok ⟨_, _, decoded⟩ =>
      unless expected != "changing-identity" do throw (IO.userError "renaming was accepted")
      let checked := admitTrace Behavioral.core ⟨6, 4, 4, 2⟩ decoded
      unless checked.isOk == (expected == "valid") do throw (IO.userError "source trace admission")
      let roundtrip := Backend.Alloy.Behavioral.encode v decoded
      unless roundtrip.loop == lasso.loop &&
          (roundtrip.frames.zip lasso.frames).all (fun (a, b) =>
            (a.signatures.zip b.signatures).all (fun (x, y) => Backend.Alloy.Behavioral.sameSet x y) &&
            (a.fields.zip b.fields).all (fun (x, y) => Backend.Alloy.Behavioral.sameRelation x y)) do
        throw (IO.userError "actual witness observation roundtrip")
  IO.println s!"actual Alloy witness replay: {expected}"

-- [utest->req~compiler-trace-representation~1]
def run (args : List String) : IO Unit := do
  if let ["replay", directory, expected] := args then
    replay directory expected
    return
  let [directory] := args | throw (IO.userError "expected directory")
  let directory := System.FilePath.mk directory
  IO.FS.createDirAll directory
  for c in cases do
    let .ok result := compiled c | throw (IO.userError s!"compile {c.name}")
    let v := (admitted c.formula c.owner).structural.toLayout
    let encoded := Backend.Alloy.Behavioral.encode v c.trace
    let .ok ⟨_, _, decoded⟩ := Backend.Alloy.Behavioral.decode v encoded |
      throw (IO.userError s!"decode {c.name}")
    if decoded.identities.ids.toList != c.trace.identities.ids.toList ||
        decoded.loop.val != c.trace.loop.val ||
        decoded.frames.toList.map (fun s => s.references.length) !=
          c.trace.frames.toList.map (fun s => s.references.length) then
      throw (IO.userError s!"roundtrip {c.name}")
    writeModule directory c.name c.expected
      { result.module.raw with facts := result.module.raw.facts ++ [tracePin encoded] }
  mutations directory
  IO.println s!"{cases.length} behavioral compiler Alloy cases and native trace roundtrips"

end ClaferCompiler.Tests.BehavioralEncoding
