import Lean
import LeanChecker.Replay

open Lean

/-! Regression check for kernel lookup after replay', including rejection of an ill-typed term. -/

def main : IO Unit := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `Init }] {}
  let mut constants : Std.HashMap Name ConstantInfo := {}
  for name in #[``True, ``True.intro, ``False] do
    let some ci := env.find? name | throw <| IO.userError s!"Missing {name}"
    constants := constants.insert name ci
  let valid : TheoremVal := {
    name := `replayLookupProbe, levelParams := [],
    type := mkConst ``True, value := mkConst ``True.intro }
  let checked ← (← mkEmptyEnvironment 0).replay'
    (constants.insert valid.name (.thmInfo valid))
  let some (.thmInfo found) := checked.toKernelEnv.find? valid.name
    | throw <| IO.userError "Kernel lookup failed after a successful replay"
  unless found.type == valid.type && found.value == valid.value do
    throw <| IO.userError "Kernel returned a different theorem"
  let invalid := { valid with name := `replayInvalidProbe, type := mkConst ``False }
  let rejected ← try
    let _ ← (← mkEmptyEnvironment 0).replay'
      (constants.insert invalid.name (.thmInfo invalid))
    pure false
  catch error =>
    if error.toString.contains "type mismatch" then
      pure true
    else
      throw error
  unless rejected do
    throw <| IO.userError "Kernel accepted an ill-typed theorem"
  IO.println "REPLAY_SELF_TEST_PASS: valid theorem retained; ill-typed theorem rejected"
