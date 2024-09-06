module type Ast_Types = sig
  type namedTy
  type structTy
  type primTy

  type field
  module FieldMap : Map.S with type key = field

  type attribute
  type element

  type action
  type functn
  type uninterp
  type literal

  type variable
  module VariableMap : Map.S with type key = variable
end

module type AST = sig
  module Types : Ast_Types

  type uid
  type typ
  type expr
  type value
  type qual
  type bqual
  type attr
  type stmt
end

module Ast(Types : Ast_Types) : AST with module Types = Types = struct
  module Types = Types
  open Types

  type uid = unit ref

  type typ = Primitive of primTy
           | Product   of typ * typ
           | Named     of namedTy
           | Struct    of structTy

  type expr = Function      of functn   * expr
            | Uninterpreted of uninterp * expr
            | Literal       of literal
            | Variable      of variable
            | Pair          of expr     * expr
            | Projection    of bool     * expr (* true = 1, false = 2 *)
            | Constructor   of namedTy  * bool  * expr (* true = L, false = R *)
            | EmptyStruct   of structTy
            (* struct type, field name, original struct, new field value *)
            | SetField      of structTy * field * expr * expr
            | RemoveField   of structTy * field * expr

  type value = Unknown       of uid      * typ
             | Literal       of literal  * primTy
             | Function      of functn   * value * typ
             | Uninterpreted of uninterp * value * typ
             | Pair          of value    * value * typ
             | Constructor   of namedTy  * bool  * value (* true = L, false = R *)
             | Struct        of structTy * value FieldMap.t

  type qual = BaseQual  of bqual
            | NotQual   of bqual
            | AndQual   of qual * qual
  and bqual = Attribute of attribute * expr
            | Element   of element   * expr
            (* Qualifiable qualifier first, what we're qualifying this second *)
            | With      of bqual     * qual

  type attr = AttrAccess  of attribute
            | OnAttribute of attribute * expr * attr
            | OnElement   of element   * expr * attr

  (* All statements, other than branches and terminators, take an additional
   * statement which is the "next" statement. This avoids having a Seq
   * constructor which would be somewhat annoying to implement *)
  type stmt = Action   of variable * action * expr * stmt
            | Assign   of variable * expr          * stmt
            | Add      of qual                     * stmt
            | Get      of variable * attr          * stmt
            | Contains of qual     * stmt   * stmt
            | Cond     of expr     * stmt   * stmt
            | Loop     of variable * expr   * stmt * stmt (* body then next *)
            (* Variable is the name for the value in the constructor *)
            | Match    of variable * expr   * stmt * stmt
            | Fail     of string
            | Return   of expr
end

module type Ast_Defs = sig
  module Types : Ast_Types
  module Ast : AST

  (* Definitions for the parameterized components *)
  val namedTyDef : Ast.Types.namedTy -> Ast.typ * Ast.typ
  val structTyDef : Ast.Types.structTy -> Ast.typ Ast.Types.FieldMap.t
  val attributeDef : Ast.Types.attribute -> Ast.typ
  val elementDef : Ast.Types.element -> Ast.typ
  val literalTyp : Ast.Types.literal -> Ast.Types.primTy
  val actionDef : Ast.Types.action -> Ast.Types.variable * Ast.typ * Ast.typ * Ast.stmt
end
