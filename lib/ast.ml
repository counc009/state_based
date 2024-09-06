type uid = unit ref

(* Type Variables:
  * 'p : primitive types
  * 'n : named types
  * 's : struct types
  * 'f : functions
  * 'l : literals
  * 'v : variables
  * 'd : struct fields
  * 'a : attributes
  * 'e : elements
  * 'c : actions
  *)
type ('p, 'n, 's) typD
  = Product   of ('p, 'n, 's) typD * ('p, 'n, 's) typD
  | Primitive of 'p
  | Named     of 'n
  | Struct    of 's

type ('f, 'l, 'v) exprD
  = Function of 'f * ('f, 'l, 'v) exprD
  | Literal  of 'l
  | Variable of 'v
  | Pair     of ('f, 'l, 'v) exprD * ('f, 'l, 'v) exprD

type ('p, 'n, 's, 'f, 'l, 'd) valueD
  = Unknown     of uid * ('p, 'n, 's) typD
  | Literal     of 'l  * 'p
  | Function    of 'f 
                 * ('p, 'n, 's, 'f, 'l, 'd) valueD
                 * ('p, 'n, 's) typD
  | Pair        of ('p, 'n, 's, 'f, 'l, 'd) valueD
                 * ('p, 'n, 's, 'f, 'l, 'd) valueD
                 * ('p, 'n, 's) typD
  | Constructor of 'n  * bool (* true = L, false = R *)
                 * ('p, 'n, 's, 'f, 'l, 'd) valueD
  | Struct      of 's  * ('d -> ('p, 'n, 's, 'f, 'l, 'd) valueD)

type ('f, 'l, 'v, 'a, 'e) qualD
  = BaseQual  of ('f, 'l, 'v, 'a, 'e) bqualD
  | NotQual   of ('f, 'l, 'v, 'a, 'e) bqualD
  | AndQual   of ('f, 'l, 'v, 'a, 'e) qualD * ('f, 'l, 'v, 'a, 'e) qualD
and ('f, 'l, 'v, 'a, 'e) bqualD
  = Attribute of 'a * ('f, 'l, 'v) exprD
  | Element   of 'e * ('f, 'l, 'v) exprD
  (* Qualifiable qualifier first, what we're qualifying this second *)
  | With      of ('f, 'l, 'v, 'a, 'e) bqualD * ('f, 'l, 'v, 'a, 'e) qualD

type ('f, 'l, 'v, 'a, 'e) attrD
  = AttrAccess  of 'a
  | OnAttribute of 'a * ('f, 'l, 'v) exprD * ('f, 'l, 'v, 'a, 'e) attrD
  | OnElement   of 'e * ('f, 'l, 'v) exprD * ('f, 'l, 'v, 'a, 'e) attrD

(* All statements, other than branches and terminators, take an additional
 * statement which is the "next" statement. This avoids having a Seq
 * constructor which would be somewhat annoying to implement *)
type ('f, 'l, 'v, 'a, 'e, 'c) stmtD
  = Action   of 'v * 'c * ('f, 'l, 'v) exprD    * ('f, 'l, 'v, 'a, 'e, 'c) stmtD
  | Assign   of 'v * ('f, 'l, 'v) exprD         * ('f, 'l, 'v, 'a, 'e, 'c) stmtD
  | Add      of ('f, 'l, 'v, 'a, 'e) qualD      * ('f, 'l, 'v, 'a, 'e, 'c) stmtD
  | Get      of 'v * ('f, 'l, 'v, 'a, 'e) attrD * ('f, 'l, 'v, 'a, 'e, 'c) stmtD
  | Contains of ('f, 'l, 'v, 'a, 'e) qualD
              * ('f, 'l, 'v, 'a, 'e, 'c) stmtD
              * ('f, 'l, 'v, 'a, 'e, 'c) stmtD
  | Cond     of ('f, 'l, 'v) exprD
              * ('f, 'l, 'v, 'a, 'e, 'c) stmtD
              * ('f, 'l, 'v, 'a, 'e, 'c) stmtD
  | Loop     of ('f, 'l, 'v) exprD
              * ('f, 'l, 'v, 'a, 'e, 'c) stmtD (* body of loop *)
              * ('f, 'l, 'v, 'a, 'e, 'c) stmtD (* following the loop *)
  | Match    of ('f, 'l, 'v) exprD * 'v (* variable is for value in constructor *)
              * ('f, 'l, 'v, 'a, 'e, 'c) stmtD
              * ('f, 'l, 'v, 'a, 'e, 'c) stmtD
  | Fail     of string
  | Return   of ('f, 'l, 'v) exprD

module type Ast_Defs = sig
  type primTy
  type namedTy
  type structTy

  type funct
  type literal
  type variable
  module VariableMap : Map.S with type key = variable

  type field
  module FieldMap : Map.S with type key = field

  type attribute
  type element

  type action

  type typ = (primTy, namedTy, structTy) typD
  type expr = (funct, literal, variable) exprD
  type value = (primTy, namedTy, structTy, funct, literal, field) valueD
  type qual = (funct, literal, variable, attribute, element) qualD
  type bqual = (funct, literal, variable, attribute, element) bqualD
  type attr = (funct, literal, variable, attribute, element) attrD
  type stmt = (funct, literal, variable, attribute, element, action) stmtD

  (* Definitions for the parameterized components *)
  val namedTyDef : namedTy -> typ * typ
  val structTyDef : structTy -> typ FieldMap.t

  val funcDef : funct -> typ * typ * (value -> value option)
  val literalTyp : literal -> primTy

  val attributeDef : attribute -> typ
  val elementDef : element -> typ

  val actionDef : action -> variable * typ * typ * stmt
end
