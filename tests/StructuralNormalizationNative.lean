module

public import ClaferCompiler.IR.StructuralNormalization
public import tests.StructuralNative

@[expose] public section
namespace ClaferCompiler.Tests.StructuralNormalization
open IR.Structural IR.Structural.Normalization

/-- Arbitrary IDs, a nonzero root index, an unused abstract chain, repeated
names, punctuation, set/bag references and opaque provenance all survive. -/
def input : Core 7 := ⟨#v[
  { id := 40, name := "a'__1", isAbstract := true, localBounds := ⟨0, .finite 0⟩,
    source := some ⟨"model.cfr", 2, 8⟩,
    authored := some ⟨true, some ⟨0, .finite 0⟩, none⟩ },
  { id := 50, name := "a'__1", isAbstract := true, super := some 0,
    localBounds := ⟨0, .finite 0⟩ },
  { id := 100, name := "Sing", origin := .syntheticRoot, localBounds := ⟨3, .finite 5⟩ },
  { id := 900, name := "a'_1", parent := some 2, reference := .set 5,
    localBounds := ⟨2, .finite 4⟩ },
  { id := 700, name := "a'_1", parent := some 2, reference := .bag 5 },
  { id := 17, name := "a__1", parent := some 2 },
  { id := 18, name := "a_1", parent := some 2, reference := .set 3 }], 2⟩

def cert : Certificate 7 :=
  ⟨#v[0, 0, 0, 1, 1, 1, 1], #v[0, 1, 0, 0, 0, 0, 0],
    #v[true, true, false, false, false, false, false]⟩

def expected : Core 7 := ⟨#v[
  { id := 40, name := "a'__1", isAbstract := true,
    source := some ⟨"model.cfr", 2, 8⟩,
    authored := some ⟨true, some ⟨0, .finite 0⟩, none⟩ },
  { id := 50, name := "a'__1", isAbstract := true, super := some 0 },
  { id := 100, name := "Sing", origin := .syntheticRoot, localBounds := ⟨3, .finite 5⟩ },
  { id := 900, name := "a'_1", parent := some 2, reference := .set 5,
    localBounds := ⟨2, .finite 4⟩ },
  { id := 700, name := "a'_1", parent := some 2, reference := .bag 5 },
  { id := 17, name := "a__1", parent := some 2 },
  { id := 18, name := "a_1", parent := some 2, reference := .set 3 }], 2⟩

def invalidInterval : Core 7 :=
  { input with
    declarations := input.declarations.set 0 { (input.get 0) with localBounds := ⟨2, .finite 1⟩ } }

def missingUnused : Certificate 7 := { cert with unused := #v[false, false, false, false, false, false, false] }

def checkValid (label : String) (m : Core n) (k : Certificate n) : IO Unit := do
  let .ok v := checked m k | throw (IO.userError s!"{label}: normalization failed")
  unless v.certificate == k do throw (IO.userError s!"{label}: certificate changed")
  unless v.core.root == m.root do throw (IO.userError s!"{label}: root changed")
  for d in List.finRange n do
    let before := m.get d
    let after := v.core.get d
    unless { after with localBounds := before.localBounds } == before do
      throw (IO.userError s!"{label}: identity, reference or metadata changed")
    if before.parent.isSome || !before.isAbstract then
      unless after.localBounds == before.localBounds do
        throw (IO.userError s!"{label}: observable multiplicity changed")
    else
      unless after.localBounds == ({} : Bounds) do
        throw (IO.userError s!"{label}: noncanonical parentless abstract")
  let .ok second := checked v.core v.certificate
    | throw (IO.userError s!"{label}: second normalization failed")
  unless second.core == v.core && second.certificate == v.certificate do
    throw (IO.userError s!"{label}: second pass changed data")

def checkRejected (label : String) (m : Core n) (k : Certificate n) (code : String) : IO Unit := do
  let .error original := validate m k | throw (IO.userError s!"{label}: invalid test fixture")
  let .error actual := checked m k | throw (IO.userError s!"{label}: invalid input repaired")
  unless actual == original && actual.code == code do
    throw (IO.userError s!"{label}: original diagnostic changed")

-- [utest->req~compiler-resolved-normalization~1]
def run : IO Unit := do
  checkValid "unused chain" input cert
  let .ok v := checked input cert | throw (IO.userError "fixture rejected")
  unless v.core == expected && v.core != input do
    throw (IO.userError "expected nontrivial canonicalization")
  checkValid "already canonical" expected cert
  checkRejected "malformed abstract interval" invalidInterval cert "ir.invalid-core-or-ranks"
  checkRejected "missing unused flags" input missingUnused "ir.unsupported-or-invalid-certificate"
  -- Both would pass after the pure projection: admission must precede it.
  let .ok _ := validate (normalize invalidInterval) cert
    | throw (IO.userError "invalid interval witness does not expose validation order")
  let .ok _ := validate (normalize input) missingUnused
    | throw (IO.userError "unused witness does not expose validation order")
  for (label, raw, _) in Structural.cases do
    match resolveRaw raw with
    | .error _ => pure () -- Raw decoding has its own mandatory rejection tests.
    | .ok (core, certificate) =>
      match validate core certificate with
      | .ok _ => checkValid label core certificate
      | .error e => checkRejected label core certificate e.code
  -- The pure projection must preserve a parented abstract's bound even though
  -- M1 admission rejects that richer structural form.
  let parented : Core 7 :=
    { input with
      declarations := input.declarations.set 0 { (input.get 0) with parent := some 2 } }
  unless (normalize parented).get 0 == parented.get 0 do
    throw (IO.userError "parented abstract multiplicity changed")
  checkRejected "parented abstract" parented cert "ir.invalid-core-or-ranks"
  IO.println "Resolved normalization: canonicalization, fixed points, preservation and rejection passed"

end ClaferCompiler.Tests.StructuralNormalization
