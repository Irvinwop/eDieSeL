/- Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 -/
import EDSL.Source.Objects.BlockEval

set_option autoImplicit false
namespace EDSL.Source.Objects.BlockEval
open StateSyntax
variable {target : Target} {stateParameters : List IntType} {Environment : Type}

@[simp] theorem reserveAll_cons (dialect : Dialect) (kind : ArithmeticType)
    (kinds : List ArithmeticType) :
    (reserveAll dialect (kind :: kinds) : Op target stateParameters Environment _) =
      Op.bind (reserve dialect kind) (fun reference =>
        Op.bind (reserveAll dialect kinds) (fun tail => Op.pure (.cons reference tail))) := rfl

@[simp] theorem enterParameters_nil (dialect : Dialect) :
    (enterParameters (kinds := []) dialect .nil : Op target stateParameters Environment _) =
      Op.pure .nil := rfl

@[simp] theorem enterParameters_cons (dialect : Dialect) (kind : ArithmeticType)
    {kinds : List ArithmeticType} (value : Value target kind.asIntType)
    (rest : CallInputs target kinds) :
    (enterParameters (kinds := kind :: kinds) dialect (.cons value rest) :
      Op target stateParameters Environment _) =
      Op.bind (reserve dialect kind) (fun reference =>
        Op.bind («initialize» dialect reference (some value)) (fun _ =>
          Op.bind (enterParameters dialect rest) (fun tail => Op.pure (.cons reference tail)))) := rfl

@[simp] theorem closeAll_cons {kind : ArithmeticType} {kinds : List ArithmeticType}
    (reference : LValue kind) (tail : Env kinds) :
    (closeAll (.cons reference tail) : Op target stateParameters Environment Unit) =
      Op.bind (closeAll tail) (fun _ => endLifetime reference) := rfl

@[simp] theorem evalDecls_body (dialect : Dialect) (policy : IntegerConversionPolicy)
    {context : List ArithmeticType} {result : IntType} (environment : Env context)
    (statement : Stmt target context result) :
    (evalDecls dialect policy (.body statement) environment .nil :
      Op target stateParameters Environment _) =
      StateEval.evalStmt dialect policy environment statement := rfl

@[simp] theorem evalDecls_declare (dialect : Dialect) (policy : IntegerConversionPolicy)
    {context : List ArithmeticType} {result : IntType} (kind : ArithmeticType)
    (initial : Option (RHS target context kind.asIntType))
    (rest : Decls target (kind :: context) result) (environment : Env context)
    (reference : LValue kind) (tail : ReservationPlan rest) :
    (evalDecls dialect policy (.declare kind initial rest) environment (.cons reference tail) :
      Op target stateParameters Environment _) =
      Op.bind (match initial with
        | none => Op.pure none
        | some expression => Op.bind (StateEval.evalExpr dialect policy environment expression)
            (fun value => Op.pure (some value))) (fun value =>
        Op.bind («initialize» dialect reference value) (fun _ =>
          evalDecls dialect policy rest (environment.extend reference) tail)) := by
  cases initial <;> rfl

end EDSL.Source.Objects.BlockEval
