module

public import ClaferCompiler.IR.Structural

@[expose] public section
open ClaferCompiler.IR.Structural
namespace ClaferCompiler.Tests.Structural

def root : Declaration Nat := { id := 100, name := "root", origin := .syntheticRoot }
def child (id : Nat) : Declaration Nat := { id, name := "same", parent := some 100 }
def abstractType (id : Nat) : Declaration Nat := { id, name := "same", isAbstract := true }
def raw (ds : Array (Declaration Nat)) (pr sr : Array Nat) (u : Array Bool) : Raw :=
  ⟨ds, 100, pr, sr, u⟩
def emptyModel := raw #[root] #[0] #[0] #[false]
def two := raw #[root, child 200] #[0, 1] #[0, 0] #[false, false]
def referenceCycle := raw
  #[root, { child 200 with reference := .set 300 }, { child 300 with reference := .bag 200 }]
  #[0, 1, 1] #[0, 0, 0] #[false, false, false]
def inheritance := raw
  #[root, abstractType 20, { child 200 with super := some 20 }]
  #[0, 0, 1] #[0, 0, 1] #[false, false, false]
def unusedChain := raw
  #[root, { abstractType 20 with localBounds := ⟨0, .finite 0⟩ },
    { abstractType 30 with super := some 20, localBounds := ⟨0, .finite 0⟩ }]
  #[0, 0, 0] #[0, 0, 1] #[false, true, true]

def outcome (r : Raw) : String := match validateRaw r with
  | .ok _ => "ok"
  | .error d => d.code

def cases : List (String × Raw × String) := [
  ("synthetic root alone", emptyModel, "ok"),
  ("missing all declarations", raw #[] #[] #[] #[], "ir.missing-root"),
  ("duplicate names", two, "ok"),
  ("cyclic set/bag references", referenceCycle, "ok"),
  ("abstract inheritance", inheritance, "ok"),
  ("unused zero abstract chain", unusedChain, "ok"),
  ("reordered IDs", raw #[child 200, root] #[1, 0] #[0, 0] #[false, false], "ok"),
  ("duplicate IDs", raw #[root, child 100] #[0, 1] #[0, 0] #[false, false], "ir.duplicate-id"),
  ("dangling parent", { two with declarations := #[root, { child 200 with parent := some 88 }] }, "ir.dangling-id"),
  ("dangling target", { two with declarations := #[root, { child 200 with reference := .set 88 }] }, "ir.dangling-id"),
  ("dangling super", { two with declarations := #[root, { child 200 with super := some 88 }] }, "ir.dangling-id"),
  ("parent cycle", { two with declarations := #[root, { child 200 with parent := some 200 }] }, "ir.invalid-core-or-ranks"),
  ("super cycle", { inheritance with declarations := #[root, { abstractType 20 with super := some 20 }, child 200] }, "ir.invalid-core-or-ranks"),
  ("bad interval", { two with declarations := #[root, { child 200 with localBounds := ⟨2, .finite 1⟩ }] }, "ir.invalid-core-or-ranks"),
  ("bad group interval", { two with declarations := #[root, { child 200 with groupBounds := ⟨2, .finite 1⟩ }] }, "ir.invalid-core-or-ranks"),
  ("bad rank", { two with parentRanks := #[0, 0] }, "ir.invalid-core-or-ranks"),
  ("bad certificate length", { two with unused := #[] }, "ir.certificate-length"),
  ("concrete parentless", { two with declarations := #[root, { child 200 with parent := none }] }, "ir.invalid-core-or-ranks"),
  ("second root", { two with declarations := #[root, { child 200 with origin := .syntheticRoot }] }, "ir.invalid-core-or-ranks"),
  ("primitive", { two with declarations := #[root, { child 200 with origin := .integer }] }, "ir.unsupported-or-invalid-certificate"),
  ("abstract with child", raw #[root, abstractType 20, { child 200 with parent := some 20 }] #[0, 0, 1] #[0, 0, 0] #[false, false, false], "ir.unsupported-or-invalid-certificate"),
  ("zero abstract used", { inheritance with declarations := #[root, { abstractType 20 with localBounds := ⟨0, .finite 0⟩ }, { child 200 with super := some 20 }], unused := #[false, true, true] }, "ir.unsupported-or-invalid-certificate"),
  ("concrete super", raw #[root, child 20, { child 200 with super := some 20 }] #[0, 1, 1] #[0, 0, 1] #[false, false, false], "ir.unsupported-or-invalid-certificate"),
  ("reference subtype", { inheritance with declarations := #[root, abstractType 20, { child 200 with super := some 20, reference := .set 20 }] }, "ir.unsupported-or-invalid-certificate"),
  ("root reference target", { two with declarations := #[root, { child 200 with reference := .bag 100 }] }, "ir.unsupported-or-invalid-certificate"),
  ("positive empty group", { emptyModel with declarations := #[{ root with groupBounds := ⟨1, .unbounded⟩ }] }, "ir.unsupported-or-invalid-certificate"),
  ("infeasible group still admitted", { two with declarations := #[{ root with groupBounds := ⟨5, .finite 5⟩ }, { child 200 with localBounds := ⟨0, .finite 0⟩ }] }, "ok"),
  ("invalid byte span", { two with declarations := #[root, { child 200 with source := some ⟨"μ.cfr", 4, 2⟩ }] }, "ir.invalid-span")
]

/-- Executed by a separately linked native test program, never a production command. -/
def run : IO Unit := do
  for (label, input, expected) in cases do
    let actual := outcome input
    unless actual == expected do
      throw (IO.userError s!"{label}: expected {expected}, got {actual}")
    if let .error d := validateRaw input then
      let category := if expected == "ir.unsupported-or-invalid-certificate" then
        Category.unsupported else Category.malformed
      unless d.category == category do throw (IO.userError s!"{label}: wrong category")
  let .error version := validateDocument "clafer-ir/2" "m1-effective" emptyModel
    | throw (IO.userError "unknown version accepted")
  unless version.code == "ir.version" do throw (IO.userError "version diagnostic")
  let .error profile := validateDocument "clafer-ir/1" "m2" emptyModel
    | throw (IO.userError "unknown profile accepted")
  unless profile.code == "ir.profile" do throw (IO.userError "profile diagnostic")
  let .ok v := validateRaw referenceCycle | throw (IO.userError "reference fixture")
  unless (v.core.get ⟨1, by decide⟩).reference == .set ⟨2, by decide⟩ &&
      (v.core.get ⟨2, by decide⟩).reference == .bag ⟨1, by decide⟩ do
    throw (IO.userError "ID binding changed")
  let metadata : Declaration Nat := { child 200 with
    source := some ⟨"μ.cfr", 2, 8⟩
    authored := some ⟨false, some ⟨0, .finite 1⟩, none⟩ }
  let .ok decorated := validateRaw { two with declarations := #[root, metadata] }
    | throw (IO.userError "metadata fixture")
  unless (decorated.core.get ⟨1, by decide⟩).source == metadata.source &&
      (decorated.core.get ⟨1, by decide⟩).authored == metadata.authored do
    throw (IO.userError "metadata changed during resolution")
  let .error dangling := validateRaw { two with
      declarations := #[root, { child 200 with reference := .set 88 }] }
    | throw (IO.userError "dangling ID accepted")
  unless dangling.pointer == "/declarations/1" && dangling.declaration == some 200 do
    throw (IO.userError "dangling ID location")
  let heads : Array ReferenceOccurrence := #[⟨200, 11, 0, 9⟩, ⟨200, 12, 0, 9⟩]
  unless heads.size == 2 && heads[0].head != heads[1].head do
    throw (IO.userError "repeated targets collapsed")
  IO.println s!"{cases.length} admission cases; version, profile, ID binding and bag identities passed"

end ClaferCompiler.Tests.Structural
