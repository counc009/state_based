let uid_count = ref 0
let uid () = let x = !uid_count in uid_count := x + 1 ; x

type uid = int
type id = Loop of int | Val of int

type 'a eval = Reduced of 'a
             | Stuck
             | Err of string

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

  type typ = Product    of typ * typ
           | Primitive  of primTy
           | Named      of namedTy
           | Struct     of structTy
  type expr = Function  of funct * expr
            | Literal   of literal
            | Variable  of variable
            | Pair      of expr * expr
            (* Special expression, really intended for use as the return value
             * of a loop
             * Used to thread the environment from the loop body back into the
             * interpreter *)
            | Env

  type value = Unknown      of id * typ
             | Literal      of literal * primTy
             | Function     of funct * value * typ
             | Pair         of value * value * typ
             | Constructor  of namedTy * bool (* true = L, false = R *)
                             * value
             | Struct       of structTy * record
  and record = value FieldMap.t

  (* A qualifier is either an attribute or element with qualifiers on it or
   * a negated element (which are not further qualified, as handling negations
   * of qualified qualifiers is quite difficult; it also doesn't make sense to
   * negate attributes) *)
  type qual = Attribute   of attribute * expr * qual list
            | Element     of element * expr * qual list
            | NotElement  of element * expr
  type attr = AttrAccess  of attribute
            | OnAttribute of attribute * attr
            | OnElement   of element * expr * attr
  type elem = Element     of element * expr
            | NotElement  of element * expr
            | OnAttribute of attribute * elem
            | OnElement   of element * expr * elem

  (* All statements, other than branches and terminators, take an additional
   * statement which is the "next" statement. This avoids having a Seq
   * constructor which would be somewhat annoying to implement *)
  type stmt = Action   of variable * action * expr * stmt
            | Assign   of variable * expr * stmt
            | Add      of qual * stmt
            | Get      of variable * attr * stmt
            | Contains of elem * stmt * stmt
            | Cond     of expr * stmt * stmt
            (* Note: Because all statements have to finish with either a fail
             * or a return, loop bodies must return the environment *)
            | Loop     of variable * expr * stmt (* body of loop *)
                        * stmt (* following the loop *)
            | Match    of expr * variable (* value in constructor *)
                        * stmt * stmt (* left and right cases *)
            | Fail     of string
            | Return   of expr

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
