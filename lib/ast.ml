type uid = unit ref

type 'a eval = Reduced of 'a
             | Stuck
             | Err of string

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
  * 'r : record (i.e. the representation of a struct)
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
  (* Special expression, really intended for use as the return value of a loop
   * Used to thread the environment from the loop body back into the interpreter *)
  | Env

type ('p, 'n, 's, 'f, 'l, 'd, 'r) valueD
  = Unknown     of uid * ('p, 'n, 's) typD
  | Literal     of 'l  * 'p
  | Function    of 'f 
                 * ('p, 'n, 's, 'f, 'l, 'd, 'r) valueD
                 * ('p, 'n, 's) typD
  | Pair        of ('p, 'n, 's, 'f, 'l, 'd, 'r) valueD
                 * ('p, 'n, 's, 'f, 'l, 'd, 'r) valueD
                 * ('p, 'n, 's) typD
  | Constructor of 'n  * bool (* true = L, false = R *)
                 * ('p, 'n, 's, 'f, 'l, 'd, 'r) valueD
  | Struct      of 's  * 'r

(* A qualifier is either a base qualifier that is qualified or the negation
 * of a base qualifier (constructing states with negations of qualified qualifiers
 * is more difficult) *)
type ('f, 'l, 'v, 'a, 'e) qualD
  = BaseQual  of ('f, 'l, 'v, 'a, 'e) bqualD * (('f, 'l, 'v, 'a, 'e) qualD) list
  | NotQual   of ('f, 'l, 'v, 'a, 'e) bqualD
(* A base qual is an attribute or element and an expression.
 * It does not have other qualifiers (or attributes) attached to it *)
and ('f, 'l, 'v, 'a, 'e) bqualD
  = Attribute of 'a * ('f, 'l, 'v) exprD
  | Element   of 'e * ('f, 'l, 'v) exprD

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
  (* Note: Because all statements have to finish with either a fail or a return,
   * loop bodies must return () *)
  | Loop     of 'v * ('f, 'l, 'v) exprD
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
  type record
  module FieldMap : Map.S with type key = field

  type attribute
  type element

  type action

  type typ = (primTy, namedTy, structTy) typD
  type expr = (funct, literal, variable) exprD
  type value = (primTy, namedTy, structTy, funct, literal, field, record) valueD
  type qual = (funct, literal, variable, attribute, element) qualD
  type bqual = (funct, literal, variable, attribute, element) bqualD
  type attr = (funct, literal, variable, attribute, element) attrD
  type stmt = (funct, literal, variable, attribute, element, action) stmtD

  type env = (value * typ) VariableMap.t

  (* Definitions for the parameterized components *)
  val namedTyDef : namedTy -> typ * typ
  val structTyDef : structTy -> typ FieldMap.t

  val funcDef : funct -> typ * typ * (value -> value eval)
  val literalTyp : literal -> primTy

  val attributeDef : attribute -> typ
  val elementDef : element -> typ

  val actionDef : action -> variable * typ * typ * stmt

  (* Used to handle conditionals
   * - isTruthType returns whether a type can be used like a truth value 
   * - asTruth takes a value and produces its truth value (true/false) or
   *   fails if it cannot be reduced to a boolean value for any reason *)
  val isTruthType : typ -> bool
  val asTruth : value -> bool option
  
  (* Used to handle loops
   * - To determine that a type is loop-like we need to know if types are unit
   *   types *)
  val isUnit : typ -> bool

  (* Used to handle the special "Env" expression:
   * - The envType is a primitive (the type of the Env expression)
   * - The envLit is a literal constructed from an environment *)
  val envType : typ
  val envToVal : env -> value
  val envFromVal : value -> env
end
