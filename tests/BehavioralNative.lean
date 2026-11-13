module

public import ClaferCompiler.IR.Behavioral

@[expose] public section
namespace ClaferCompiler.Tests.Behavioral
open IR.Behavioral IR.Structural

def core : Core 4 := ⟨Vector.ofFn (fun d => {
  id := d.val
  name := if d = 0 then "Sing" else "C"
  origin := if d = 0 then .syntheticRoot else .user
  parent := if d = 0 then none else if d = 2 then some 1 else some 0
  reference := if d = 2 then .bag 3 else .basic }), 0⟩
def certificate : Certificate 4 := ⟨#v[0, 1, 2, 1], #v[0, 0, 0, 0], #v[false, false, false, false]⟩
def error : Formula 4 n := .atom (.inhabited .empty)
def attached : Attachment 4 := { id := 17, owner := 2, body := .formula error.eventually.not, source := some ⟨"machine.cfr", 12, 30⟩ }
def document : Document 4 := ⟨"clafer-behavioral-ir/1", "behavioral-core/1",
  core, certificate, [attached]⟩

def pool : Identities 4 8 where
  ids := #v[100, 101, 102, 103, 104, 105, 106, 107]
  root := 0
  directType := #v[0, 1, 1, 2, 2, 3, 3, 1]
  parent := #v[none, some 0, some 0, some 1, some 1, some 0, some 0, some 0]

def frame (i : Fin 4) : Frame 4 8 where
  live := Vector.ofFn fun x => decide (x = 0 ∨ x = 5 ∨ x = 6 ∨
    (x = 1 ∧ i ≠ 2) ∨ (x = 2 ∧ i = 2) ∨ ((x = 3 ∨ x = 4) ∧ (i = 0 ∨ i = 3)))
  references := if i = 0 then [(2, 3, 5), (2, 4, 5)]
    else if i = 3 then [(2, 3, 6), (2, 4, 6)] else []

def cycling : Lasso 4 8 4 := ⟨pool, Vector.ofFn frame, 0⟩
def bounds : ObservationBounds := ⟨8, 1, 4, 2⟩

def result (d : Document k) : String := match admitBehavioral d with
  | .ok _ => "ok" | .error e => e.code

def cases : List (String × Document 4 × String) := [
  ("guarded temporal core", document, "ok"),
  ("empty attachments", {document with attachments := []}, "ok"),
  ("unknown version", {document with version := "clafer-behavioral-ir/2"}, "behavioral.version"),
  ("static profile", {document with profile := "m1-effective"}, "behavioral.profile"),
  ("full profile is not this slice", {document with profile := "behavioral-0.5.8/v1"}, "behavioral.profile"),
  ("duplicate occurrences", {document with attachments := [attached, attached]}, "behavioral.metadata"),
  ("unknown owner", {document with attachments := [{attached with owner := 99}]}, "behavioral.metadata"),
  ("bad attachment span", {document with attachments := [{attached with source := some ⟨"m", 4, 2⟩}]}, "behavioral.metadata"),
  ("assertion", {document with attachments := [{attached with kind := .assertion}]}, "behavioral.constructor"),
  ("scenario", {document with attachments := [{attached with kind := .scenario}]}, "behavioral.constructor"),
  ("unsupported arithmetic", {document with attachments := [{attached with body := .unsupported "integer-add"}]}, "behavioral.constructor"),
  ("unsupported surface", {document with attachments := [{attached with body := .unsupported "transition-chain"}]}, "behavioral.constructor"),
  ("bad parent rank", {document with certificate := {certificate with parentRank := #v[0, 0, 0, 0]}}, "behavioral.core"),
  ("effective versus authored", {document with core := {core with declarations := core.declarations.set 1 {core.get 1 with authored := some ⟨true, some ⟨7, .finite 8⟩, none⟩}}}, "ok"),
  ("primitive excluded", {document with core := {core with declarations := core.declarations.set 3 {core.get 3 with origin := .integer}}}, "behavioral.structural-profile")]

def traceResult (b : ObservationBounds) (l : Lasso 4 8 4) : String :=
  match admitTrace core b l with | .ok _ => "ok" | .error e => e.code

def check (name : String) (ok : Bool) : IO Unit :=
  unless ok do throw (IO.userError name)

-- [utest->req~compiler-behavioral-ir~1]
-- [utest->req~compiler-behavioral-interpretation~1]
def run : IO Unit := do
  for (label, d, expected) in cases do
    check label (result d == expected)
    if let .error e := admitBehavioral d then
      let malformed := expected == "behavioral.core" || expected == "behavioral.metadata"
      check (label ++ " category") (e.category == if malformed then .malformed else .unsupported)
  check "trace admission" (traceResult bounds cycling == "ok")
  check "identity capacity" (traceResult {bounds with identities := 7} cycling == "behavioral.observation-bounds")
  check "step capacity" (traceResult {bounds with maxSteps := 3} cycling == "behavioral.observation-bounds")
  check "step lower bound" (traceResult {bounds with minSteps := 5} cycling == "behavioral.observation-bounds")
  check "reference capacity" (traceResult {bounds with referencesPerFrame := 1} cycling == "behavioral.observation-bounds")
  check "duplicate identity" (traceResult bounds {cycling with identities := {pool with ids := pool.ids.set 4 103}} == "behavioral.trace")
  check "wrong fixed parent" (traceResult bounds {cycling with identities := {pool with parent := pool.parent.set 3 (some 5)}} == "behavioral.trace")
  check "root disappears" (traceResult bounds {cycling with frames := cycling.frames.set 2 {frame 2 with live := (frame 2).live.set 0 false}} == "behavioral.trace")
  check "orphan across replacement" (traceResult bounds {cycling with frames := cycling.frames.set 2 {frame 2 with live := (frame 2).live.set 3 true}} == "behavioral.trace")
  check "absent reference target" (traceResult bounds {cycling with frames := cycling.frames.set 0 {frame 0 with references := [(2, 3, 7)]}} == "behavioral.trace")
  check "duplicate reference row" (traceResult bounds {cycling with frames := cycling.frames.set 0 {frame 0 with references := [(2, 3, 5), (2, 3, 5)]}} == "behavioral.trace")
  for t in List.range 24 do
    check "loop unfolding" ((cycling.index t).val == t % 4)
  let suffix := {cycling with loop := 2}
  check "nonzero loop" ((List.range 9).map (fun t => (suffix.index t).val) == [0,1,2,3,2,3,2,3,2])
  let ρ : Environment 8 0 := .closed 3
  let observed (t : Nat) (e : SetExpr 4 0) (h : sizeOf e < 256) :=
    (List.finRange 8).filter (e.eval core pool (cycling.at t) ρ 256 h)
  check "absent this" (observed 1 .this (by decide) == [])
  check "direct parent after death" (observed 1 (.thisStep .parent) (by decide) == [1])
  check "observed this cannot navigate" (observed 1 (.step .parent .this) (by decide) == [])
  check "two bag heads" (observed 0 (.extent 2) (by decide) == [3, 4])
  check "one target" (observed 0 (.step (.deref 2) (.extent 2)) (by decide) == [5])
  let captured := ρ.push (fun x => x == 3)
  let deref : SetExpr 4 1 := .step (.deref 2) (.var 0)
  check "capture is retained" ((SetExpr.var 0 : SetExpr 4 1).eval core pool (cycling.at 1) captured 256 (by decide) 3)
  check "capture sees new target" (deref.eval core pool (cycling.at 3) captured 256 (by decide) 6)
  check "capture sees current target" (deref.eval core pool (cycling.at 4) captured 256 (by decide) 5)
  check "old target is absent from result" (!(deref.eval core pool (cycling.at 4) captured 256 (by decide) 6))
  check "set difference" (observed 0 (.diff (.extent 2) .this) (by decide) == [4])
  check "set intersection" (observed 0 (.inter (.extent 2) .this) (by decide) == [3])
  check "set union" (observed 0 (.union .this (.extent 2)) (by decide) == [3,4])
  check "negative next" (match (error.next : Formula 4 0).normalize false 256 (by decide) with
    | (.next (.not (.atom (.inhabited .empty)))) => true | _ => false)
  check "negative eventually" (match (error.eventually : Formula 4 0).normalize false 256 (by decide) with
    | (.always (.not (.atom (.inhabited .empty)))) => true | _ => false)
  check "negative always" (match (error.always : Formula 4 0).normalize false 256 (by decide) with
    | (.eventually (.not (.atom (.inhabited .empty)))) => true | _ => false)
  check "negative until" (match (Formula.strongUntil .truth error : Formula 4 0).normalize false 256 (by decide) with
    | .weakUntil (.not (.atom (.inhabited .empty))) (.and (.not .truth) (.not (.atom (.inhabited .empty)))) => true | _ => false)
  check "negative weak until" (match (Formula.weakUntil .truth error : Formula 4 0).normalize false 256 (by decide) with
    | .strongUntil (.not (.atom (.inhabited .empty))) (.and (.not .truth) (.not (.atom (.inhabited .empty)))) => true | _ => false)
  check "counting barrier" (match (Formula.quant .one .this error.eventually.not : Formula 4 0).normalize false 256 (by decide) with
    | .not (.quant .one .this (.not (.eventually (.atom (.inhabited .empty))))) => true | _ => false)
  check "lone barrier" (match (Formula.quant .lone .this error.eventually.not : Formula 4 0).normalize true 256 (by decide) with
    | .quant .lone .this (.not (.eventually (.atom (.inhabited .empty)))) => true | _ => false)
  check "all negative" (match (Formula.quant .all .this error.eventually : Formula 4 0).normalize false 256 (by decide) with
    | .quant .some .this (.always (.not (.atom (.inhabited .empty)))) => true | _ => false)
  check "some negative" (match (Formula.quant .some .this error.eventually : Formula 4 0).normalize false 256 (by decide) with
    | .quant .all .this (.always (.not (.atom (.inhabited .empty)))) => true | _ => false)
  check "no positive" (match (Formula.quant .no .this error.eventually : Formula 4 0).normalize true 256 (by decide) with
    | .quant .all .this (.always (.not (.atom (.inhabited .empty)))) => true | _ => false)
  check "let preserves sign" (match (Formula.letSet .this error.eventually : Formula 4 0).normalize false 256 (by decide) with
    | .letSet .this (.always (.not (.atom (.inhabited .empty)))) => true | _ => false)
  check "negative implication" (match (Formula.implies .truth error.eventually : Formula 4 0).normalize false 256 (by decide) with
    | .and .truth (.always (.not (.atom (.inhabited .empty)))) => true | _ => false)
  check "negative equivalence" (match (Formula.iff .truth error.eventually : Formula 4 0).normalize false 256 (by decide) with
    | .or (.and .truth (.always (.not (.atom (.inhabited .empty))))) (.and (.eventually (.atom (.inhabited .empty))) (.not .truth)) => true | _ => false)
  check "positive xor" (match (Formula.xor .truth error.eventually : Formula 4 0).normalize true 256 (by decide) with
    | .or (.and .truth (.always (.not (.atom (.inhabited .empty))))) (.and (.not .truth) (.eventually (.atom (.inhabited .empty)))) => true | _ => false)
  check "negative conditional" (match (Formula.ite error.eventually .truth error : Formula 4 0).normalize false 256 (by decide) with
    | .or (.and (.eventually (.atom (.inhabited .empty))) (.not .truth)) (.and (.always (.not (.atom (.inhabited .empty)))) (.not (.atom (.inhabited .empty)))) => true | _ => false)
  check "initial anchor" (match (error.initially : Formula 4 0).normalize false 256 (by decide) with
    | (.initially (.not (.atom (.inhabited .empty)))) => true | _ => false)
  check "final anchor" (match (error.finally : Formula 4 0).normalize false 256 (by decide) with
    | (.finally (.not (.atom (.inhabited .empty)))) => true | _ => false)
  check "nested negation" (match (error.eventually.not.not.not : Formula 4 0).normalize true 256 (by decide) with
    | (.always (.not (.atom (.inhabited .empty)))) => true | _ => false)
  let normalizedAttachment := attached.normalize 256 (by intro f h; cases h; decide)
  check "attachment occurrence" (normalizedAttachment.id == 17 && normalizedAttachment.owner == 2 &&
    normalizedAttachment.source == attached.source)
  check "static rejects behavioral profile" (match validateDocument "clafer-ir/1" "behavioral-core/1"
    {declarations := #[], root := 0, parentRanks := #[], superRanks := #[], unused := #[]} with
    | .error e => e.code == "ir.profile" | .ok _ => false)
  IO.println "behavioral admission, trace identities, observations and signed normalization passed"

end ClaferCompiler.Tests.Behavioral
