/- Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 -/
import EDSL.Source.Objects.BlockEval
import EDSL.Source.Objects.StateVC

set_option autoImplicit false
namespace EDSL.Source.Objects.BlockVC
open StateSyntax Protocol
variable {target : Target} {stateParameters : List IntType} {Environment : Type}

/-- Structural declaration VCs use the actual shared expression computation and
initialization primitive. Binding visibility is exactly the declaration spine;
all identities were reserved by the caller before the first initializer. -/
def vcDecls (dialect : Dialect) (policy : IntegerConversionPolicy) :
    {context : List ArithmeticType} → {result : IntType} →
    (declarations : Decls target context result) → Env context →
    ReservationPlan declarations → Post target stateParameters Environment (Value target result) →
    State target stateParameters Environment → Prop
  | _, _, .body statement, environment, _, post =>
      StateVC.vcStmt dialect policy environment statement post
  | _, _, .declare _ initial rest, environment, plan, post =>
    match plan with
    | .cons reference tail =>
      let initialValue := match initial with
        | none => Op.pure none
        | some expression => Op.bind (StateEval.evalExpr dialect policy environment expression)
            fun value => Op.pure (some value)
      WP initialValue (fun original value middle initialEvents =>
        WP («initialize» dialect reference value)
          (fun _ _ updated initializeEvents =>
            vcDecls dialect policy rest (environment.extend reference) tail
              (fun _ returned final suffix =>
                post original returned final (initialEvents ++ (initializeEvents ++ suffix))) updated)
          middle)

theorem vcDecls_iff_wp (dialect : Dialect) (policy : IntegerConversionPolicy)
    {context : List ArithmeticType} {result : IntType}
    (declarations : Decls target context result) (environment : Env context)
    (plan : ReservationPlan declarations)
    (post : Post target stateParameters Environment (Value target result))
    (initial : State target stateParameters Environment) :
    vcDecls dialect policy declarations environment plan post initial ↔
      WP (BlockEval.evalDecls dialect policy declarations environment plan) post initial := by
  induction declarations generalizing initial with
  | body statement =>
      exact StateVC.vcStmt_iff_wp dialect policy environment statement post initial
  | declare kind value rest ih =>
      cases plan with
      | cons reference tail =>
          simp only [vcDecls, BlockEval.evalDecls, wp_bind]
          apply wp_congr
          intro original evaluated middle initialEvents
          apply wp_congr
          intro ignored ignoredUnit updated initializeEvents
          exact ih _ _ _ _

/-- Generate the finite block's conditions: actual parameter entry and complete
reservation, structural declarations/statements, then actual normal cleanup.
This is not a compiler or a native source-order correspondence theorem. -/
def vcExecute {parameters : List ArithmeticType} {result : IntType}
    (program : StateSyntax.Program target parameters result)
    (inputs : CallInputs target parameters)
    (post : Post target stateParameters Environment (Value target result))
    (initial : State target stateParameters Environment) : Prop :=
  WP (BlockEval.enterParameters program.dialect inputs)
    (fun original parameters afterParameters parameterEvents =>
      WP (BlockEval.reserveAll program.dialect program.body.localKinds)
        (fun _ locals afterReserve reserveEvents =>
          vcDecls program.dialect program.conversions program.body parameters locals
            (fun _ value afterBody bodyEvents =>
              WP (BlockEval.closeAll locals)
                (fun _ _ afterLocals localEvents =>
                  WP (BlockEval.closeAll parameters)
                    (fun _ _ final parameterEndEvents =>
                      post original value final
                        (parameterEvents ++ (reserveEvents ++
                          (bodyEvents ++ (localEvents ++ parameterEndEvents))))) afterLocals)
                afterBody) afterReserve) afterParameters) initial

theorem vcExecute_iff_wp {parameters : List ArithmeticType} {result : IntType}
    (program : StateSyntax.Program target parameters result)
    (inputs : CallInputs target parameters)
    (post : Post target stateParameters Environment (Value target result))
    (initial : State target stateParameters Environment) :
    vcExecute program inputs post initial ↔ WP (BlockEval.execute program inputs) post initial := by
  simp only [vcExecute, BlockEval.execute, wp_bind, vcDecls_iff_wp, wp_pure, List.append_nil]

/-- Public conditions separate complete syntax coverage from demanded execution.
Admissions supplied by clients must independently describe their entry domain. -/
def vcProgram {parameters : List ArithmeticType} {result : IntType}
    (program : StateSyntax.Program target parameters result)
    (post : Post target (VariableTypes parameters) Environment (Value target result))
    (initial : State target (VariableTypes parameters) Environment) : Prop :=
  program.Supported ∧ vcExecute program initial.inputs post initial

theorem vcProgram_iff_wp {parameters : List ArithmeticType} {result : IntType}
    (program : StateSyntax.Program target parameters result)
    (post : Post target (VariableTypes parameters) Environment (Value target result))
    (initial : State target (VariableTypes parameters) Environment) :
    vcProgram program post initial ↔ WP (BlockEval.runProgram program) post initial := by
  unfold vcProgram
  rw [← program.firstUnsupported_eq_none_iff, vcExecute_iff_wp]
  cases coverage : program.firstUnsupported with
  | none => simp only [coverage, true_and, WP, BlockEval.runProgram]
  | some feature => simp only [coverage, reduceCtorEq, false_and, WP, BlockEval.runProgram, Op.reject]

/-- Structural VCs yield useful actual-execution certificates; no source NoUB
or target success can be substituted for checking the generated conditions. -/
theorem certificate_of_vc {parameters : List ArithmeticType} {result : IntType}
    (program : StateSyntax.Program target parameters result)
    (admitted : State target (VariableTypes parameters) Environment → Prop)
    (post : Post target (VariableTypes parameters) Environment (Value target result))
    (useful : ∃ initial, admitted initial)
    (conditions : ∀ initial, admitted initial → vcProgram program post initial) :
    Protocol.Certificate (BlockEval.runProgram program) admitted post where
  useful := useful
  verified := (verifies_iff_wp _ _ _).mpr fun initial allowed =>
    (vcProgram_iff_wp program post initial).mp (conditions initial allowed)

end EDSL.Source.Objects.BlockVC
