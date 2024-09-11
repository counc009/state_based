type uid = Ast.uid

module Interp(Ast : Ast.Ast_Defs) = struct
  open Ast

  module ValueOrder : Map.OrderedType with type t = value = struct
    type t = value
    let compare : value -> value -> int = compare
  end
  module ValueMap : Map.S with type key = value = Map.Make(ValueOrder)

  (* bools indicate negation (if true) or non-negated (if false) *)
  type state = State of (element * value * bool, state) Hashtbl.t
                      * (attribute * bool, value * state) Hashtbl.t
  let init_state = State (Hashtbl.create 10, Hashtbl.create 10)

  type prg_type = { init : state; final : state; loops : uid ValueMap.t; }
  let init_prg_type = { init = init_state; final = init_state; loops = ValueMap.empty; }

  let new_env = VariableMap.empty

  type 'a error = Ok of 'a
                | Err of string
  type prg_res = (prg_type * value) error

  (* A list-like type is any named type defined as n = () + t * n
   * Returns the element type is the give type is list like *)
  let list_like (n : namedTy) : typ option =
    let (nil, cons) = namedTyDef n
    in if not (isUnit nil) then None
    else match cons with
         | Product (hd, Named tl) when tl = n -> Some hd
         | _ -> None

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
      | Env -> Ok (envToVal env, envType)
    (* Notes on loops: the bodies should return the special expression "Env",
     * which is used to thread the environment back to the processing here so
     * so that loop can modify the environment outside of it. This does mean
     * you cannot return a value for an entire action from inside a loop *)
    (* Note: ret arg here is the return for the next statement not the loop *)
    in let rec process_loop (var : variable) (lst : value) (elemTy : typ)
                            (body : stmt) (next : stmt) (s : prg_type)
                            (env : env) (ret : typ) : prg_res list =
      match lst with
      | Literal _ | Pair _ | Struct _ ->
          failwith "Loop value has non-list value"
      | Constructor (_, true, _) -> (* Nil case *)
          interp next s env ret
      | Constructor (_, false, Pair (hd, tl, _)) -> (* Cons case *)
          let res_hd = interp body s (VariableMap.add var (hd, elemTy) env) envType
          in List.flatten
              (List.map
                (fun s ->
                  match s with Err msg -> [Err msg]
                  | Ok (s, e) ->
                      process_loop var tl elemTy body next s (envFromVal e) ret)
                res_hd)
      | _ -> (* Loop over an unknown value *)
          (* The way we handle loops over unknown lists is to assign the value
           * we loop over a particular UID which represents the loop variable
           * while we loop over that list. We record this information in the
           * state so we can reconstruct repeat constructs at the end, without
           * having to deal with them during interpretation *)
          (* Identify whether there's already a "loop variable" for looping over
           * this value. If so, use it, otherwise create our own.
           * If we create our own, we also update the map in the state *)
          let (uid, s) =
            match ValueMap.find_opt lst s.loops with
            | Some uid -> (uid, s)
            | None ->
                let uid = ref ()
                in let state = { init  = s.init; final = s.final;
                                 loops = ValueMap.add lst uid s.loops; }
                in (uid, state)
          in let head : value = Unknown (uid, elemTy)
          in let res_loop = interp body s (VariableMap.add var (head, elemTy) env) envType
          in List.flatten
              (List.map
                (fun s ->
                  match s with Err msg -> [Err msg]
                  | Ok (s, e) -> interp next s (envFromVal e) ret)
                res_loop)
    and interp (b : stmt) (s : prg_type) (env : env) (ret : typ) : prg_res list =
      match b with
      | Action   (var, action, expr, next) ->
          let (arg, in_type, out_type, body) = actionDef action
          in begin match eval_expr expr env with
          | Err msg -> Err msg :: []
          | Ok (v, t) ->
              if t <> in_type
              then Err "Incorrect argument type to action" :: []
              else let results = interp body s (VariableMap.singleton arg (v, t)) out_type
              in List.flatten
                  (List.map (fun r ->
                      match r with
                      | Ok (s, v) ->
                          interp next s (VariableMap.add var (v, out_type) env) ret
                      | Err msg -> Err msg :: []) results)
          end
      | Assign   (var, expr, next) ->
          begin match eval_expr expr env with
          | Err msg -> Err msg :: []
          | Ok (v, t) ->
              interp next s (VariableMap.add var (v, t) env) ret
          end
      | Add      (qual, next) -> [] (* TODO *)
      | Get      (var, attr, next) -> [] (* TODO *)
      | Contains (qual, thn, els) -> [] (* TODO *)
      (* TODO: For both cond and match, if the result of expression is not
       * a concrete value we could evaluate both branches and track the
       * "constraint" of what we've assumed the value was (this is much like
       * you would do with refinement/dependent types). For the moment I have
       * not done this for simplicity
       *)
      | Cond     (expr, thn, els) ->
          begin match eval_expr expr env with
          | Err msg -> Err msg :: []
          | Ok (v, t) ->
              if not (isTruthType t)
              then Err "Condition is not truthy" :: []
              else match asTruth v with
                   (* If we were to track the constraints, we would do that here *)
                   | None -> Err "Could not evaluate truth of condition" :: []
                   | Some true -> interp thn s env ret
                   | Some false -> interp els s env ret
          end
      | Match    (expr, var, left, right) ->
          begin match eval_expr expr env with
          | Err msg -> Err msg :: []
          | Ok (v, t) ->
              match t with
              | Named n ->
                  begin match v with
                  | Constructor (_, b, v) ->
                      let t = (if b then fst else snd) (namedTyDef n)
                      in interp (if b then left else right) s
                            (VariableMap.add var (v, t) env) ret
                  (* Modify here to track constraints *)
                  | _ -> Err "Could not evaluate to constructor on match" :: []
                  end
              | _ -> Err "Cannot match over non-named type" :: []
          end
      | Loop     (var, expr, body, next) ->
          begin match eval_expr expr env with
          | Err msg -> Err msg :: []
          | Ok (v, t) ->
              match t with
              | Named n ->
                  begin match list_like n with
                  | None -> Err "Cannot loop over non list-like type" :: []
                  | Some elemTy ->
                      process_loop var v elemTy body next s env ret
                  end
              | _ -> Err "Cannot loop over non-list-like type" :: []
          end
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
