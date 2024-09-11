module Interp(Ast : Ast.Ast_Defs) = struct
  open Ast

  (* bools indicate negation (if true) or non-negated (if false) *)
  type state = State of (element * value * bool, state) Hashtbl.t
                      * (attribute * bool, value * state) Hashtbl.t
  let init_state = State (Hashtbl.create 10, Hashtbl.create 10)

  type prg_type = state * state
  let init_prg_type = (init_state, init_state)

  type env = (value * typ) VariableMap.t
  let new_env = VariableMap.empty

  type 'a error = Ok of 'a
                | Err of string
  type prg_res = (prg_type * value) error

  let interpret (s : stmt) (retTy : typ) : prg_res list =
    let rec eval_expr (e : expr) (env : env) : (value * typ) error =
      match e with
      | Function (f, exp) ->
          begin match eval_expr exp env with
          | Err m -> Err m
          | Ok (v, t) ->
              let (argTy, retTy, interp) = funcDef f
              in if t <> argTy
                 then Err "Type error, argument type mismatch"
                 else
                   match interp v with
                   | Reduced w -> Ok (w, retTy)
                   | Stuck -> Ok (Function (f, v, retTy), retTy)
                   | Err msg -> Err msg
          end
      | Literal l ->
          let p = literalTyp l
          in Ok (Literal (l, p), Primitive p)
      | Variable v ->
          begin match VariableMap.find_opt v env with
          | None -> Err "Undefined variable"
          | Some v -> Ok v
          end
      | Pair (x, y) ->
          begin match eval_expr x env, eval_expr y env with
          | Ok (x, tx), Ok (y, ty)
            -> let t : typ = Product (tx, ty) in Ok (Pair (x, y, t), t)
          | Err m, Err n -> Err (m ^ "\n" ^ n)
          | Err m, Ok _ -> Err m
          | Ok _ , Err n -> Err n
          end
    in let rec interp (b : stmt) (s : prg_type) (env : env) (ret : typ) : prg_res list =
      match b with
      | Action   (var, action, expr, next) -> []
      | Assign   (var, expr, next) -> []
      | Add      (qual, next) -> []
      | Get      (var, attr, next) -> []
      | Contains (qual, thn, els) -> []
      | Cond     (expr, thn, els) -> []
      (* If the expression does not evaluate to either true or false, is that
         an error, or do we propagate some sort of constraint on the two
         cases? *)
      | Loop     (var, expr, body, next) -> []
      | Match    (expr, var, left, right) -> []
      | Fail     msg -> (Err msg) :: []
      | Return   expr ->
          begin match eval_expr expr env with
          | Ok (v, t) ->
              if t <> ret
              then Err "Incorrect return type" :: []
              else Ok (s, v) :: []
          | Err msg -> Err msg :: []
          end
    in interp s init_prg_type new_env retTy
end
