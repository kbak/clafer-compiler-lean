module

public import ClaferCompiler.Backend.Alloy.Print
public import tests.AlloyCore

@[expose] public section

namespace ClaferCompiler.Tests.AlloyText
open Backend.Alloy Backend.Alloy.Text AlloyCore

/-! Canonical reconstruction and adversarial hygiene regressions.
[utest->req~compiler-alloy-text~1] -/

def bodies : List Formula := [
  .truth, .falsity, countEq r 3, .equal (.join a r) b,
  .equal (.join b (.transpose r)) a,
  .equal (.join r (.transpose r)) (.product a a),
  .equal (.join r b) a, countEq (.union a a) 2,
  .equal (.inter r (.product a b)) r, countEq (.diff (.product a b) r) 1,
  .subset (.product a b) r,
  .all a (.mult .some (.join (.var 0) r)),
  .all a (.mult .one (.join (.var 0) r)),
  .exists_ a (.mult .one (.join (.var 0) r)),
  .all a (.exists_ b (.subset (.product (.var 1) (.var 0)) r)),
  .all a (.all (.var 0) (.equal (.var 1) (.var 0))),
  .all (.diff a a) .falsity, .exists_ (.diff a a) .truth,
  .conj (.neg (.subset (.product a b) r))
    (.disj .falsity (.implies .truth (.compare .lt (.literal (-8)) (.literal 7)))),
  .compare .le (.literal (-8)) (.literal 7),
  .mult .set r, .mult .lone a,
  .equal (.empty .binary) (.product (.empty .unary) (.empty .unary)),
  .equal (.empty .unary) (.diff a a),
  .equal (.diff a (.diff a a)) a,
  .equal (.join (.union a b) (.transpose r)) a
]

def modules : List Module :=
  bodies.map model ++ [
    { model .truth with command := ⟨.check, .subset r (.product a b), [⟨2, true⟩, ⟨2, true⟩], 4⟩ },
    { model .truth with facts := [.mult .some a, .mult .lone b] },
    hierarchyModel .truth,
    ⟨⟨[⟨none, true, .set⟩], []⟩, [], ⟨.run, .truth, [⟨1, true⟩], 2⟩⟩,
    ⟨⟨[], []⟩, [], ⟨.run, .truth, [], 1⟩⟩,
    ⟨⟨[{}, {}], [⟨1, 0, .one⟩, ⟨0, 1, .lone⟩, ⟨0, 0, .some⟩]⟩, [],
      ⟨.run, .truth, [⟨1, true⟩, ⟨1, true⟩], 2⟩⟩
  ] ++ [.set, .one, .lone, .some].map (fun m => multiplicityModel m 1)

def roundTrips (m : Module) : Bool :=
  match check m with
  | .error _ => false
  | .ok c => match render c (anonymousNames m) with
    | .error _ => false
    | .ok out => decide (parse out.text = some m)

/-- Bounded exhaustive generator: combine nested unary relations and formulas,
including repeated operands. The generator is deterministic, and every member
must be admitted and rendered; failures cannot be discarded. -/
def generated : List Module :=
  let atoms := [a, b, Rel.empty .unary, Rel.join a r]
  let relations := atoms ++ atoms.flatMap (fun x => atoms.flatMap fun y =>
    [Rel.union x y, Rel.inter x y, Rel.diff x y])
  relations.flatMap fun x =>
    [model (.equal x x), model (.mult .set x),
     model (.all x (.exists_ (.var 0) (.equal (.var 0) (.var 1))))]

def labels : List String := ["same", "same", "sig", "always", "eventually", "var", "Int",
  "cc0", "cc1", "cc2", "Zażółć 🦉", "x\n} run {} //", "/* */", "", "a-b"]

def hostileNames (m : Module) : Names :=
  ⟨m.schema.signatures.zipIdx.map (fun (_, i) => some ⟨labels[i % labels.length]!, none, none, none⟩),
   m.schema.fields.zipIdx.map (fun (_, i) => some ⟨labels[(i + 3) % labels.length]!, none, none, none⟩)⟩

def negativeParses : List String := [
  "set sig cc0 { }\nrun { ( no none ) } for 4 Int , 1 cc0\n", -- illegal signature keyword
  "run { no none } for 4 Int\n", -- lost required grouping
  "sig cc0 { }\nsig cc0 { }\nrun { ( no none ) } for 4 Int , 1 cc0\n", -- alias
  "sig cc0 { }\nrun { ( all cc6 : ( cc0 ) | ( no none ) ) } for 4 Int , 1 cc0\n", -- bad binder
  "sig cc0 { }\nrun { ( all cc2 : ( cc2 ) | ( no none ) ) } for 4 Int , 1 cc0\n", -- domain capture
  "run { ( cc2 ) } for 4 Int\n", -- free variable / not a formula
  "run { ( no none ) } for 4 Int\n// ignored?\n", -- comments not in emitted subset
  "run { ( no none ) } for 4 Int\nrun { ( no none ) } for 4 Int\n"
]

end ClaferCompiler.Tests.AlloyText
