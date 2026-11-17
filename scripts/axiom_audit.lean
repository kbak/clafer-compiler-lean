module

-- PROJECT_IMPORTS
public meta import Lean.Elab.Command
public meta import Lean.Util.CollectAxioms
public meta import Lean.Meta.Constructions.CtorIdx
public meta import Lean.Compiler.ImplementedByAttr

/-!
Audit every declaration originating in the project, including generated/private
ones. Reject new axioms, unsafe/partial declarations and transitive dependencies
outside Lean's standard logical axioms. The shared check retains this output.
Adapted from clafer-semantics at 1454e3bd2ce9697923cdcef3863c816651ffc147
(MIT, copyright 2026 Kacper Bak; see LICENSE).
`scripts/project_modules.py` expands PROJECT_IMPORTS with the complete discovered
module inventory before execution. Running this template alone fails the empty
audit guard. Module origins, not declaration namespaces, select declarations.
-/

open Lean Meta in
/-- Lean 4.36 compiles constructor indices with a native tag read. Check the
registered implementation, its exact body, and the logical index of every constructor. -/
private meta def checkedCtorIdxImpl (env : Environment) (impl : DefinitionVal) : MetaM Bool := do
  let .str index "_impl" := impl.name | return false
  let some ind := isCtorIdxCore? env index | return false
  let some (.defnInfo spec) := env.find? index | return false
  unless ind.numCtors > 1 && !ind.isUnsafe && spec.safety == .safe &&
      spec.type == impl.type && spec.levelParams == impl.levelParams &&
      spec.levelParams == ind.levelParams &&
      env.getModuleIdxFor? ind.name == env.getModuleIdxFor? impl.name &&
      env.getModuleIdxFor? index == env.getModuleIdxFor? impl.name &&
      Compiler.getImplementedBy? env index == some impl.name do return false
  let nativeMatches ← forallTelescope spec.type fun args result => do
    let some x := args.back? | return false
    let ty ← inferType x
    unless ty.getAppFn.isConstOf ind.name && result.isConstOf ``Nat do return false
    let tag := mkApp2 (mkConst ``getObjTagNat [← getLevel ty]) ty x
    return impl.value == (← mkLambdaFVars args tag)
  unless nativeMatches do return false
  let levels := ind.levelParams.map mkLevelParam
  for ctorName in ind.ctors do
    let ctor ← getConstInfoCtor ctorName
    let correct ← forallTelescope ctor.type fun args ty => do
      let value := mkAppN (mkConst ctorName levels) args
      let indexApp := mkApp (mkAppN (mkConst index levels) ty.getAppArgs) value
      withTransparency .all <| isDefEq indexApp (mkNatLit ctor.cidx)
    unless correct do return false
  return true

open Lean in
-- [utest->req~compiler-build~1]
run_cmd do
  let env ← getEnv
  let moduleNames := env.header.moduleNames
  let roots := #[`ClaferCompiler, `Main, `tests]
  let isProject := fun name => roots.any (·.isPrefixOf name)
  for mod in env.header.modules do
    if isProject mod.module && !mod.importAll then
      throwError "audit must import all of project module {mod.module}"
  let standard := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut count := 0
  let mut counts := #[0, 0, 0]
  let mut used : Array Name := #[]
  for (name, info) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let origin := moduleNames[idx.toNat]!
    unless isProject origin do continue
    count := count + 1
    for i in [:roots.size] do
      if roots[i]!.isPrefixOf origin then
        counts := counts.modify i (· + 1)
    if info.isUnsafe || info.isPartial then
      let accepted ← match info with
        | .defnInfo d =>
          if d.safety != .unsafe then pure false
          else Elab.Command.liftTermElabM (checkedCtorIdxImpl env d)
        | _ => pure false
      unless accepted do throwError "unsafe or partial project declaration: {name}"
    if let .axiomInfo _ := info then
      throwError "new project axiom: {name}"
    let axioms ← collectAxioms name
    for ax in axioms do
      unless standard.contains ax do
        throwError "unapproved axiom {ax} in {name}"
      unless used.contains ax do used := used.push ax
    if info matches .thmInfo _ then
      logInfo m!"{name}: {axioms}"
  if count == 0 then throwError "audit found no project declarations"
  if counts[0]! == 0 then throwError "audit found no ClaferCompiler declarations"
  for i in [:roots.size] do
    logInfo m!"{roots[i]!}: {counts[i]!} declarations (zero means scaffolding only)."
  logInfo m!"Audited {count} project declarations. Standard axioms used: {used}. New assumptions: none."
