module

public import Lean

/-!
# `Verification.Replay`

Replays the public theorem dependency cone in a fresh Lean kernel environment.
-/

@[expose] public section

open Lean

def publicRoots : Array Name :=
  #[`Catalan.catalans_conjecture, `Catalan.catalan_int, `Catalan.catalan_int_signed,
    `Catalan.mihailescu_odd_primes, `Catalan.JSP.statement]

def cone (env : Environment) (roots : Array Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut stack := roots
  while !stack.isEmpty do
    let n := stack.back!
    stack := stack.pop
    if seen.contains n then continue
    seen := seen.insert n
    match env.find? n with
    | none => pure ()
    | some ci =>
      for c in ci.getUsedConstantsAsSet do
        unless seen.contains c do stack := stack.push c
      match ci with
      | .inductInfo v => stack := stack ++ v.all.toArray ++ v.ctors.toArray
      | .ctorInfo v => stack := stack.push v.induct
      | .recInfo v => stack := stack ++ v.all.toArray
      | _ => pure ()
  return seen

def isStandardAxiom (name : Name) : Bool :=
  name == `propext || name == `Classical.choice || name == `Quot.sound

unsafe def main (_args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  Lean.withImportModules #[{ module := `Catalan }] {} fun env => do
    IO.println "imported Catalan"
    let mut ok := true

    for root in publicRoots do
      match env.find? root with
      | none =>
        ok := false
        IO.println s!"{root}: MISSING from imported environment"
      | some ci =>
        if ci.isTheorem then
          IO.println s!"{root}: present in imported environment; theorem = true"
        else
          ok := false
          IO.println s!"{root}: present in imported environment; theorem = false"

    let names := cone env publicRoots
    let mut constants : Std.HashMap Name ConstantInfo := {}
    let mut missing : Array Name := #[]
    for name in names do
      match env.find? name with
      | some ci => constants := constants.insert name ci
      | none => missing := missing.push name
    if missing.isEmpty then
      IO.println s!"cone contains {constants.size} constants; all names have ConstantInfo"
    else
      ok := false
      IO.println s!"names without ConstantInfo in imported environment: {missing}"

    let unsafeOrPartial :=
      constants.toList.filter (fun (_, ci) => ci.isUnsafe || ci.isPartial) |>.map (·.1)
    if unsafeOrPartial.isEmpty then
      IO.println "unsafe/partial constants in cone: []"
    else
      ok := false
      IO.println s!"unsafe/partial constants in cone: {unsafeOrPartial}"

    let axioms := constants.toList.filter (fun (_, ci) => ci.isAxiom) |>.map (·.1)
    let nonstandardAxioms := axioms.filter (fun name => !isStandardAxiom name)
    IO.println s!"axioms in cone: {axioms}"
    if nonstandardAxioms.isEmpty then
      IO.println "nonstandard axioms in cone: []"
    else
      ok := false
      IO.println s!"nonstandard axioms in cone: {nonstandardAxioms}"

    (← IO.getStdout).flush
    if !ok then return 1
    let env0 ← mkEmptyEnvironment
    let env' ← env0.replay constants
    let kernelEnv := env'.toKernelEnv

    let mut missingAfterReplay : Array Name := #[]
    for (name, ci) in constants.toList do
      if !(ci.isUnsafe || ci.isPartial) && (kernelEnv.find? name).isNone then
        missingAfterReplay := missingAfterReplay.push name
    if missingAfterReplay.isEmpty then
      IO.println s!"all replayable cone constants are present in the replayed kernel environment"
    else
      ok := false
      IO.println s!"replayable cone constants missing after replay: {missingAfterReplay}"

    for root in publicRoots do
      match env.find? root, kernelEnv.find? root with
      | some imported, some replayed =>
        let theoremRoot := imported.isTheorem && replayed.isTheorem
        let sameType := replayed.type == imported.type
        if theoremRoot && sameType then
          IO.println s!"{root}: present after replay; theorem = true; type identical = true"
        else
          ok := false
          IO.println s!"{root}: present after replay; theorem = {theoremRoot}; type identical = {sameType}"
      | _, _ =>
        ok := false
        IO.println s!"{root}: MISSING after replay"

    IO.println s!"fresh-environment kernel replay of {constants.size} constants; verification passed = {ok}"
    return if ok then 0 else 1
