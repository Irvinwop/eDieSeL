import tests.PackedReadConsumer
import Lean

open Lean in
elab "#audit_packed_consumer" : command => do
  let env ← getEnv
  let allowed := #[``propext, ``Quot.sound, ``Classical.choice]
  let mut count := 0
  let mut dependencies : Array Name := #[]
  for (name, info) in env.constants.toList do
    if (`EDSL).isPrefixOf name || (`EDSLGrader).isPrefixOf name ||
        (`PackedReadConsumer).isPrefixOf name then
      if info matches .axiomInfo _ then
        throwError "Project axiom: {name}"
      count := count + 1
      for dependency in ← collectAxioms name do
        unless allowed.contains dependency do
          throwError "{name} depends on unapproved axiom {dependency}"
        unless dependencies.contains dependency do
          dependencies := dependencies.push dependency
  if count == 0 then
    throwError "Empty project audit"
  logInfo m!"PACKED_AUDIT_COUNT {count}"
  logInfo m!"PACKED_AUDIT_AXIOMS {Json.compress (toJson (dependencies.map toString))}"
  logInfo m!"ACTUAL_IMPORTS {Json.compress (toJson (env.header.moduleNames.map toString))}"

#audit_packed_consumer
