/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import Lean
import EDSL.Grading.Export.Core
import EDSL.Grading.Runtime.Checker

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 128

/-! Public producer-profile regressions using owned synthetic syntax and real
packet parsing, decoding, auditing and forced kernel checks. Numeric contracts
are selected independently of client theorem types and encoder statistics.
 -/
namespace ClientEncodingTests
open Lean EDSLGrader EDSLGrader.Runtime

private def require (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def unwrap {α : Type} (result : Except Failure α) : IO α :=
  match result with
  | .ok value => pure value
  | .error failure => throw (IO.userError s!"unexpected failure: {failure}")

private def reject {α : Type} (label : String) (kind : FailureKind)
    (result : Except Failure α) (reason : String := "") : IO Unit := do
  match result with
  | .ok _ => throw (IO.userError s!"unexpected acceptance: {label}")
  | .error failure =>
    require (failure.kind == kind) s!"{label}: wrong failure category: {failure}"
    unless reason.isEmpty do
      require (failure.message == reason) s!"{label}: wrong failure reason: {failure}"

private def decode (env : Kernel.Environment) (json : Json)
    (lim : Runtime.Limits := {}) : IO Expr := do
  let (value, _) ← unwrap ((DAG.decodeDag env lim [] [] json).run lim.maxNodes)
  return value

private def reflexivity (value : Expr) : Expr :=
  mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Nat) value

private def naturalContract (n : Nat) : Expr :=
  mkApp3 (mkConst ``Eq [1]) (mkConst ``Nat) (mkRawNatLit n) (mkRawNatLit n)

private def checkNumber (env : Kernel.Environment) (json : Json) (n : Nat) : IO Unit := do
  let value ← decode env json
  let _ ← unwrap (checkExpr env {} (naturalContract n) (reflexivity value)
    `EDSLGrader.Internal.clientEncodingNumber)
  pure ()

private def successors (count : Nat) (base : Expr) : Expr :=
  (List.range count).foldl (fun value _ => mkApp (mkConst ``Nat.succ) value) base

private def padding (count : Nat) (body : Expr) : Expr :=
  (List.range count).foldl (fun value _ =>
    .letE `unused (mkConst ``Nat) (mkRawNatLit 0) value true) body

private def add (env : Kernel.Environment) (decl : Declaration) : IO Kernel.Environment :=
  unwrap (forceDeclaration env 10000000 1024 decl)

private def definition (name : Name) (type value : Expr) : Declaration :=
  .defnDecl {
    name := name
    levelParams := []
    type := type
    value := value
    hints := .abbrev
    safety := .safe
    all := [name] }

private def theoremDeclaration (name : Name) (type value : Expr) : Declaration :=
  .thmDecl { name, levelParams := [], type, value, all := [name] }

private def scalarCases (env : Kernel.Environment) : IO Unit := do
  -- Handwritten v2 syntax: no encoder/serializer supplies the expected rows.
  let scalar : Json := .arr #[.str "dag", .arr #[.arr #[.str "nat", .str "0"]], .str "0"]
  let zero := mkRawNatLit 0
  require ((← unwrap (DAG.encodeDag zero)) == scalar) "default scalar wire syntax changed"
  require ((← unwrap (DAG.encodeDagWith {} zero)) == scalar) "explicit defaults changed syntax"
  reject "zero depth" .resource (DAG.encodeDagWith { maxExprDepth := 0 } zero)
  reject "zero work" .resource (DAG.encodeDagWith { maxFieldSteps := 0 } zero)
  let one ← unwrap (DAG.encodeDagWith { maxExprDepth := 1, maxFieldSteps := 1 } zero)
  require (one == scalar) "one dispatch did not encode a scalar"
  checkNumber env one 0

  -- The body revisits the value: let + Nat + 0 + cached 0 = four dispatches,
  -- while only Nat, 0 and the let have distinct rows.
  let term := Expr.letE `ignored (mkConst ``Nat) zero zero true
  let expected : Json := .arr #[.str "dag", .arr #[
    .arr #[.str "const", .arr #[.str "Nat"], .arr #[]],
    .arr #[.str "nat", .str "0"],
    .arr #[.str "let", .str "0", .str "1", .str "1"]], .str "2"]
  reject "cached child still spends fuel" .resource
    (DAG.encodeDagWith { maxExprDepth := 2, maxFieldSteps := 3 } term)
  let encoded ← unwrap (DAG.encodeDagWithStats { maxExprDepth := 2, maxFieldSteps := 4 } term)
  require (encoded.json == expected && encoded.stats.steps == 4 &&
    encoded.stats.rows == 3 && encoded.stats.expandedHeight == 2)
    "cached-child encoding disagreed with the handwritten trace"
  require ((← unwrap (DAG.encodeDag term)) == expected &&
    (← unwrap (DAG.encodeDagWith { maxExprDepth := 256, maxFieldSteps := 900000 } term)) == expected)
    "profile selection changed let canonicalization"
  checkNumber env encoded.json 0

  -- Metadata dispatch is charged even though its wrapper emits no row.
  let tagged := Expr.mdata {} zero
  reject "metadata dispatch spends fuel" .resource
    (DAG.encodeDagWith { maxFieldSteps := 1 } tagged)
  let erased ← unwrap (DAG.encodeDagWithStats { maxFieldSteps := 2 } tagged)
  require (erased.json == scalar && erased.stats.steps == 2 &&
    erased.stats.rows == 1 && erased.stats.expandedHeight == 1)
    "metadata dispatch/canonicalization changed"
  checkNumber env erased.json 0

private def shallowDepthCases (env : Kernel.Environment) : IO Unit := do
  let three := successors 3 (mkRawNatLit 0)
  let small : ClientEncodingLimits := { maxExprDepth := 4 }
  let boundary ← unwrap (DAG.encodeDagWith small three)
  checkNumber env boundary 3
  reject "custom depth below the old default" .resource
    (DAG.encodeDagWith { maxExprDepth := 3 } three)
  reject "one beyond a custom boundary" .resource
    (DAG.encodeDagWith small (successors 4 (mkRawNatLit 0)))

  -- Three is interned on the left before being encountered beneath four more
  -- successors on the right. Expanded height is nine, despite the cache hit.
  let shared := successors 3 (mkRawNatLit 0)
  let sum := mkApp2 (mkConst ``Nat.add) shared (successors 4 shared)
  let profile : ClientEncodingLimits := { maxExprDepth := 9 }
  let encoded ← unwrap (DAG.encodeDagWithStats profile sum)
  require (encoded.stats.expandedHeight == 9) "cached height lost the deeper occurrence"
  checkNumber env encoded.json 10
  reject "shallow-first cache cannot hide expanded height" .resource
    (DAG.encodeDagWith { maxExprDepth := 8 } sum)
  let tooDeep := mkApp2 (mkConst ``Nat.add) shared (successors 5 shared)
  reject "shared expression one beyond boundary" .resource (DAG.encodeDagWith profile tooDeep)
  let larger ← unwrap (DAG.encodeDagWith { maxExprDepth := 10 } tooDeep)
  checkNumber env larger 11

private def checkDomain (env : Kernel.Environment) (expected actual : Expr) : IO Unit := do
  let contract := Expr.forallE `a expected (mkConst ``True) .default
  let proof := Expr.lam `a actual (mkConst ``True.intro) .default
  let _ ← unwrap (checkExpr env {} contract proof `EDSLGrader.Internal.clientEncodingUniverse)
  pure ()

private def universeCases (env : Kernel.Environment) : IO Unit := do
  -- max 1 2 reduces to 2, but its syntax is taller than the numeral 2.
  let u := Level.max (.succ .zero) (.succ (.succ .zero))
  let profile : ClientEncodingLimits := { maxExprDepth := 5, maxFieldSteps := 1 }
  for (input, domain) in [
      ((Expr.sort u, Expr.sort 2) : Expr × Expr),
      ((mkConst ``PUnit [u], mkConst ``PUnit [2]) : Expr × Expr)] do
    let encoded ← unwrap (DAG.encodeDagWithStats profile input)
    require (encoded.stats.expandedHeight == 5 && encoded.stats.steps == 1)
      "inline universe height was omitted or counted as expression dispatches"
    checkDomain env domain (← decode env encoded.json)
    reject "inline universe exceeds custom expression height" .resource
      (DAG.encodeDagWith { maxExprDepth := 4 } input)

  -- DAG edges are flat; universe JSON remains inline. A permissive producer
  -- cannot raise the grader's separate JSON nesting allowance.
  let tall : Level := (List.range 200).foldl (fun u _ => .succ u) .zero
  let proof := Expr.letE `T (.sort (.succ tall)) (.sort tall) (mkConst ``True.intro) true
  let text ← unwrap (encodePacketWith { maxExprDepth := 204, maxFieldSteps := 4 } [] proof)
  let exprOnly : Runtime.Limits := { maxExprDepth := 204, kernelRecDepth := 1024 }
  reject "expression profile cannot change JSON admission" .resource
    (checkPacket env exprOnly (mkConst ``True) text) "JSON depth"
  let _ ← unwrap (checkPacket env { exprOnly with maxJsonDepth := 256 } (mkConst ``True) text)
  pure ()

private def packetFieldCases (env : Kernel.Environment) : IO Unit := do
  let type := Expr.letE `T (.sort 1) (mkConst ``Nat) (mkConst ``True) true
  let proof := padding 1 (mkConst ``True.intro)
  let declarations := [theoremDeclaration `ClientEncodingFixture.left type proof,
    theoremDeclaration `ClientEncodingFixture.right type proof]
  -- Five expression fields, each requiring four dispatches. Shared syntax in
  -- earlier fields may neither consume this field's fuel nor supply its pool.
  let encoding : ClientEncodingLimits := { maxExprDepth := 4, maxFieldSteps := 4 }
  let text ← unwrap (encodePacketWith encoding declarations proof)
  let fields ← unwrap (Packet.fields {} text)
  let typeDag : Json := .arr #[.str "dag", .arr #[
    .arr #[.str "sort", .arr #[.str "succ", .str "zero"]],
    .arr #[.str "const", .arr #[.str "Nat"], .arr #[]],
    .arr #[.str "const", .arr #[.str "True"], .arr #[]],
    .arr #[.str "let", .str "0", .str "1", .str "2"]], .str "3"]
  let proofDag : Json := .arr #[.str "dag", .arr #[
    .arr #[.str "const", .arr #[.str "Nat"], .arr #[]],
    .arr #[.str "nat", .str "0"],
    .arr #[.str "const", .arr #[.str "True", .str "intro"], .arr #[]],
    .arr #[.str "let", .str "0", .str "1", .str "2"]], .str "3"]
  require (fields.dialect == .dag && fields.proof == proofDag)
    "root pool was not independently encoded as v2"
  for entry in fields.declarations do
    let .arr #[.str "theorem", _, .arr #[], actualType, actualProof] := entry
      | throw (IO.userError "unexpected theorem wire shape")
    require (actualType == typeDag && actualProof == proofDag)
      "declaration type/value reused another field's rows"
  let checked ← unwrap (checkPacket env {} (mkConst ``True) text)
  require (checked.kernelChecks > 1) "auxiliary fields did not reach forced kernel checking"
  reject "per-field work cap is enforced" .resource
    (encodePacketWith { encoding with maxFieldSteps := 3 } declarations proof)

private def packetPolicyCases (env : Kernel.Environment) : IO Unit := do
  let intro := mkConst ``True.intro
  let expected := "[\"edsl-proof-v2\",[],[\"dag\",[[\"const\",[\"True\",\"intro\"],[]]],\"0\"]]"
  require ((← unwrap (encodePacket [] intro)) == expected &&
    (← unwrap (encodePacketWith {} [] intro)) == expected &&
    (← unwrap (encodePacketWith { maxExprDepth := 1, maxFieldSteps := 1 } [] intro)) == expected)
    "default/scalar packet compatibility changed"
  let _ ← unwrap (checkPacket env {} (mkConst ``True) expected)
  let atDefault ← unwrap (encodePacket [] (padding 127 intro))
  let _ ← unwrap (checkPacket env {} (mkConst ``True) atDefault)
  let proof := padding 128 intro
  reject "legacy DAG wrapper retains depth 128" .resource (DAG.encodeDag proof)
  reject "legacy packet wrapper retains depth 128" .resource (encodePacket [] proof)
  let permissive : ClientEncodingLimits := { maxExprDepth := 129 }
  let text ← unwrap (encodePacketWith permissive [] proof)
  reject "producer cannot choose grader expression depth" .resource
    (checkPacket env {} (mkConst ``True) text) "expanded DAG expression depth"
  let larger : Runtime.Limits := { maxExprDepth := 129, kernelRecDepth := 1024 }
  let _ ← unwrap (checkPacket env larger (mkConst ``True) text)
  reject "permissive producer cannot prove False" .rejected
    (checkPacket env larger (mkConst ``False) text)
  let wrong ← unwrap (encodePacketWith permissive [] (padding 128 (mkRawNatLit 0)))
  reject "larger grader still checks proof typing" .rejected
    (checkPacket env larger (mkConst ``True) wrong)

private def exportWith (prepared : Bool) (trusted client : Kernel.Environment)
    (root : Name) (mode : Export.Mode) (lim : Export.Limits) : Except Failure Export.Packet :=
  if prepared then
    (Export.exportTheoremPrepared trusted client root {} mode lim).map (fun packet => packet.toPacket)
  else
    Export.exportTheorem trusted client root mode lim

private def helperExportCases (trusted : Kernel.Environment) : IO Unit := do
  let helper := `ClientEncodingFixture.successor128
  let root := `ClientEncodingFixture.helperRoot
  let functionType := Expr.forallE `n (mkConst ``Nat) (mkConst ``Nat) .default
  let functionValue := Expr.lam `n (mkConst ``Nat) (successors 128 (.bvar 0)) .default
  let client ← add trusted (definition helper functionType functionValue)
  let applied := mkApp (mkConst helper) (mkRawNatLit 0)
  let statement := mkApp3 (mkConst ``Eq [1]) (mkConst ``Nat) applied applied
  let client ← add client (theoremDeclaration root statement (reflexivity applied))
  -- The lambda body has 128 applications, each with a function dispatch, plus
  -- its bvar; the lambda and its Nat domain bring the field to 259 dispatches.
  let profile : Export.Limits := { encoding := { maxExprDepth := 130, maxFieldSteps := 259 } }
  let larger : Runtime.Limits := { maxExprDepth := 130, kernelRecDepth := 1024 }
  for prepared in [false, true] do
    for mode in [Export.Mode.reference, .body] do
      reject "export defaults retain client depth" .resource
        (exportWith prepared trusted client root mode {})
      reject "export forwards custom depth" .resource
        (exportWith prepared trusted client root mode
          { profile with encoding := { profile.encoding with maxExprDepth := 129 } })
      reject "export forwards custom field work" .resource
        (exportWith prepared trusted client root mode
          { profile with encoding := { profile.encoding with maxFieldSteps := 258 } })
      let packet ← unwrap (exportWith prepared trusted client root mode profile)
      reject "export profile cannot raise grader limits" .resource
        (checkPacket trusted {} (naturalContract 128) packet.text) "expanded DAG expression depth"
      let checked ← unwrap (checkPacket trusted larger (naturalContract 128) packet.text)
      require (checked.kernelChecks > 1) "fresh helper closure did not reach the kernel"
      if prepared then
        -- A well-typed replacement gives a valid proof of another arithmetic
        -- contract; it must not inherit the independently selected result 128.
        let replacement := Expr.lam `n (mkConst ``Nat) (successors 127 (.bvar 0)) .default
        let wrong ← unwrap (Export.exportTheoremPrepared trusted client root
          { definitionValues := #[(helper, replacement)] } mode profile)
        let _ ← unwrap (checkPacket trusted larger (naturalContract 127) wrong.text)
        reject "prepared helper cannot select its grading contract" .rejected
          (checkPacket trusted larger (naturalContract 128) wrong.text)

private def headerExportCases (trusted : Kernel.Environment) : IO Unit := do
  let header := `ClientEncodingFixture.Header
  let constructor := `ClientEncodingFixture.Header.pack
  let payload : Expr := (List.range 8).foldl (fun body _ =>
    .letE `T (.sort 1) (mkConst ``Nat) body true) (mkConst ``Nat)
  let client ← add trusted (.inductDecl [] 0 [{
    name := header, type := .sort 1, ctors := [{
      name := constructor, type := .forallE `payload payload (mkConst header) .default }]
    }] false)
  let root := `ClientEncodingFixture.headerRoot
  let proof := Expr.letE `p (mkConst header)
    (mkApp (mkConst constructor) (mkRawNatLit 0)) (mkConst ``True.intro) true
  let client ← add client (theoremDeclaration root (mkConst ``True) proof)
  -- The small root discovers a constructor whose let-padded Nat domain is
  -- the limiting field: height 12 and 27 expression dispatches.
  let profile : Export.Limits := { encoding := { maxExprDepth := 12, maxFieldSteps := 27 } }
  for prepared in [false, true] do
    for mode in [Export.Mode.reference, .body] do
      reject "constructor header receives custom depth" .resource
        (exportWith prepared trusted client root mode
          { profile with encoding := { profile.encoding with maxExprDepth := 11 } })
      reject "constructor header receives custom work" .resource
        (exportWith prepared trusted client root mode
          { profile with encoding := { profile.encoding with maxFieldSteps := 26 } })
      let packet ← unwrap (exportWith prepared trusted client root mode profile)
      let checked ← unwrap (checkPacket trusted {} (mkConst ``True) packet.text)
      require ((checked.env.find? constructor).isSome && checked.kernelChecks > 1)
        "constructor headers were not replayed by the real kernel"

private def runCases (env : Kernel.Environment) : IO Unit := do
  scalarCases env
  shallowDepthCases env
  universeCases env
  packetFieldCases env
  packetPolicyCases env
  helperExportCases env
  headerExportCases env

run_cmd do
  let _ ← runCases (← getEnv).toKernelEnv
  logInfo "ClientEncoding: custom producer limits, fresh fields, independent grader policy and checked exporter closures passed"
end ClientEncodingTests
