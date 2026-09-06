import Lean
import LeanChecker.Replay

/-!
Replay the complete declaration dependency closure of the certificate into an
empty environment at trust level zero. This uses the official kernel again;
it is not an independent implementation of Lean's type theory.
-/

open Lean

def certificateName : Name := `NormalLocus.normal_locus_finite_etale_conditional

def dependencyClosure (env : Environment) (root : Name) :
    IO (Std.HashMap Name ConstantInfo) := do
  let mut pending := #[root]
  let mut result : Std.HashMap Name ConstantInfo := {}
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    if result.contains name then continue
    let some ci := env.find? name
      | throw <| IO.userError s!"Missing dependency: {name}"
    if ci.isUnsafe || ci.isPartial then
      throw <| IO.userError s!"Unsafe or partial declaration in proof closure: {name}"
    if let .axiomInfo _ := ci then
      unless #[`propext, `Classical.choice, `Quot.sound].contains name do
        throw <| IO.userError s!"Unapproved axiom in proof closure: {name}"
    result := result.insert name ci
    for dep in ci.getUsedConstantsAsSet do
      pending := pending.push dep
    if let .inductInfo value := ci then
      for dep in value.all do pending := pending.push dep
  return result

def main : IO Unit := do
  initSearchPath (← findSysroot)
  let imported ← importModules #[{ module := `NormalLocus.ConditionalNL }] {}
  let some (.thmInfo certificate) := imported.find? certificateName
    | throw <| IO.userError "Certificate is missing or is not a theorem"
  match certificate.type with
  | .forallE _ domain codomain _ =>
    unless domain.isConstOf `NormalLocus.External.Library &&
        codomain.isConstOf `NormalLocus.NormalLocusTheorem do
      throw <| IO.userError "Certificate has the wrong domain or codomain"
  | _ => throw <| IO.userError "Certificate has the wrong function type"
  let closure ← dependencyClosure imported certificateName
  IO.println s!"REPLAY_START: {closure.size} declarations; empty environment; trust level 0"
  (← IO.getStdout).flush
  let empty ← mkEmptyEnvironment 0
  let checked ← empty.replay' closure
  -- replay' returns a kernel environment without elaborator async-name state.
  -- Inspect the kernel directly rather than using the elaborator's contains.
  let some (.thmInfo replayed) := checked.toKernelEnv.find? certificateName
    | throw <| IO.userError "Certificate absent from the checked kernel environment"
  unless replayed.type == certificate.type && replayed.value == certificate.value &&
      replayed.levelParams == certificate.levelParams do
    throw <| IO.userError "Replayed certificate differs from the imported certificate"
  let mut axioms : Array Json := #[]
  for (name, ci) in closure.toList do
    if let .axiomInfo _ := ci then axioms := axioms.push (toJson name.toString)
  let report := Json.mkObj [
    ("certificate", toJson certificateName.toString),
    ("status", toJson "PASS"),
    ("mode", toJson "official-kernel-fresh-dependency-closure"),
    ("independent_checker", toJson false),
    ("trust_level", toJson (0 : Nat)),
    ("declaration_count", toJson closure.size),
    ("axioms", .arr axioms)]
  IO.FS.writeFile "verification/replay.json" (report.pretty ++ "\n")
  IO.println "REPLAY_VERIFIED: certificate and its declaration dependency closure"
