let uid = Ast.uid
type uid = Ast.uid

type id = Ast.id

module Interp(Ast : Ast.Ast_Defs) = struct
  open Ast

  type env = (value * typ) VariableMap.t

  let rec eval_expr (e : expr) (env : env) : (value * typ, string) result =
    match e with
    | Function (f, exp) ->
        Result.bind (eval_expr exp env) (fun (v, t) ->
          let (argTy, retTy, interp) = funcDef f
          in if t <> argTy
            then Error "Type error, argument type mismatch"
            else
              match interp v with
              | Reduced w -> Ok (w, retTy)
              | Stuck     -> Ok (Function (f, v, retTy), retTy)
              | Err msg   -> Error msg)
    | Literal l ->
        let p = literalTyp l
        in Ok (Literal (l, p), Primitive p)
    | Variable v ->
        begin match VariableMap.find_opt v env with
        | None -> Error "Undefined variable"
        | Some v -> Ok v
        end
    | Pair (x, y) ->
        begin match eval_expr x env, eval_expr y env with
        | Ok (x, tx), Ok (y, ty)
          -> let t : typ = Product (tx, ty) in Ok (Pair (x, y, t), t)
        | Error m, Error n -> Error (m ^ "\n" ^ n)
        | Error m, Ok _ -> Error m
        | Ok _, Error n -> Error n
        end

  let fieldMap_map_result (f : 'a -> ('b, 'e) result) (m : 'a FieldMap.t)
    : ('b FieldMap.t, 'e) result
    = FieldMap.fold
        (fun k v res -> Result.bind res (fun new_map ->
          Result.bind (f v) (fun new_v ->
            Ok (FieldMap.add k new_v new_map))))
        m
        (Ok FieldMap.empty)

  let variableMap_map_result (f : 'a -> ('b, 'e) result) (m : 'a VariableMap.t)
    : ('b VariableMap.t, 'e) result
    = VariableMap.fold
        (fun k v res -> Result.bind res (fun new_map ->
          Result.bind (f v) (fun new_v ->
            Ok (VariableMap.add k new_v new_map))))
        m
        (Ok VariableMap.empty)

  module ValueOrder : Map.OrderedType with type t = value = struct
    type t = value
    let compare : value -> value -> int = compare
  end
  module ValueMap : (Map.S with type key = value) = Map.Make(ValueOrder)

  (* States are made up of maps of qualifiers. For elements, we store the
   * element, value, and whether or not it is negated (true = negated) as the
   * key and the value is qualifiers applied to it. For attributes, the key is
   * just the attribute and whether it is negated and this maps to the value and
   * any qualifiers applied to it. *)
  module ElementOrder : Map.OrderedType with type t = element * value * bool = struct
    type t = element * value * bool
    let compare : t -> t -> int = compare
  end
  module ElementMap : (Map.S with type key = element * value * bool)
    = Map.Make(ElementOrder)

  module AttributeOrder : Map.OrderedType with type t = attribute = struct
    type t = attribute
    let compare : t -> t -> int = compare
  end
  module AttributeMap : (Map.S with type key = attribute)
    = Map.Make(AttributeOrder)

  type state = State of state ElementMap.t * (value * state) AttributeMap.t
  let empty_state = State (ElementMap.empty, AttributeMap.empty)

  type loop_info = AllUnknown of uid | AllKnown of value | LastKnown of uid * value

  type interp_state = {
    init    : state;
    final   : state;
    (* Map between values and the loop variable over that value *)
    loops   : loop_info ValueMap.t;
    (* Map between values and its boolean value *)
    bools   : bool ValueMap.t;
    (* Map between values and its constructor value (true = L) *)
    constrs : (bool * value) ValueMap.t;
  }

  let init_interp_state = {
    init    = empty_state;
    final   = empty_state;
    loops   = ValueMap.empty;
    bools   = ValueMap.empty;
    constrs = ValueMap.empty;
  }

  type interp_res =
    | Err     of string
    | Success of interp_state
    | Both    of interp_res * interp_res

  let rec add_qual
      ((q, v, qs) : (element * bool, attribute) Either.t * value * state)
      (State (els, ats) : state) : state =
    match q with
    | Left (elem, neg) ->
        let removed = ElementMap.remove (elem, v, not neg) els
        in let added = ElementMap.update (elem, v, neg)
                        (fun cur ->
                          match cur with
                          | None -> Some qs
                          | Some ps -> Some (add_quals qs ps))
                        removed
        in State (added, ats)
    | Right attr ->
        let added = AttributeMap.update attr
                      (fun cur ->
                        match cur with
                        | None -> Some (v, qs)
                        | Some (_, ps) -> Some (v, add_quals qs ps))
                      ats
        in State (els, added)
  and add_quals (State (els, ats) : state) (ps : state) =
    let rec helper els ats state =
      match els with
      | ((el, v, neg), qs) :: tl
        -> helper tl ats (add_qual (Left (el, neg), v, qs) state)
      | [] ->
          match ats with
          | (at, (v, qs)) :: tl
            -> helper [] tl (add_qual (Right at, v, qs) state)
          | [] -> state
    in helper (ElementMap.bindings els) (AttributeMap.bindings ats) ps

  let substitute_unknown (u : id) (v : value) (s : interp_state) (env : env)
    : (interp_state * env, string) result =
    let rec subst_in_value (w : value) : (value, string) result =
      match w with
      | Unknown (w, _) when u = w -> Ok v
      | Unknown (_, _) | Literal (_, _) -> Ok w
      | Function (f, v, t) ->
          Result.bind (subst_in_value v) (fun new_v ->
            let (_, _, f_def) = funcDef f
            in match f_def new_v with
            | Reduced w -> Ok w
            | Stuck -> Ok (Function (f, new_v, t))
            | Err msg -> Error msg)
      | Pair (x, y, t) ->
          Result.bind (subst_in_value x) (fun new_x ->
            Result.bind (subst_in_value y) (fun new_y ->
              Ok (Pair (new_x, new_y, t))))
      | Constructor (n, c, v) ->
          Result.bind (subst_in_value v) (fun new_v ->
            Ok (Constructor (n, c, new_v)))
      | Struct (t, r) ->
          Result.bind (fieldMap_map_result subst_in_value r) (fun new_r ->
            Ok (Struct (t, new_r)))
      (* Unlike substituting loop variables where we skip listvals we do handle
       * listvals here since they may contain unknown values that we want to
       * eliminate *)
      | ListVal (n, w) ->
          Result.bind (subst_in_value w) (fun new_w ->
            Ok (ListVal (n, new_w)))
    in let rec subst_in_state (s : state) : (state, string) result =
      match s with
      | State (elems, attrs) ->
          let with_elems =
            ElementMap.fold
              (fun (el, v, neg) s new_state ->
                Result.bind new_state (fun new_state ->
                  Result.bind (subst_in_value v) (fun new_v ->
                    Result.bind (subst_in_state s) (fun new_s ->
                      Ok (add_qual (Either.Left (el, neg), new_v, new_s) new_state)))))
              elems (Ok empty_state)
          in let with_attrs =
            Result.bind with_elems (fun with_elems ->
              AttributeMap.fold
                (fun attr (v, s) new_state ->
                  Result.bind new_state (fun new_state ->
                    Result.bind (subst_in_value v) (fun new_v ->
                      Result.bind (subst_in_state s) (fun new_s ->
                        Ok (add_qual (Either.Right attr, new_v, new_s) new_state)))))
                attrs (Ok with_elems))
          in with_attrs
    in let new_env : (env, string) result =
      variableMap_map_result
        (fun (v, t) -> Result.bind (subst_in_value v) (fun v -> Ok (v, t)))
        env
    in let new_init = subst_in_state s.init
    in let new_final = subst_in_state s.final
    (* TODO: Don't add bools and constrs back manually, invoke addConstraint
       for each. *)
    in let new_bools = s.bools
    in let new_constrs = s.constrs
    in let new_loops = s.loops
    in Result.bind new_init (fun new_init ->
        Result.bind new_final (fun new_final ->
          Result.bind new_env (fun new_env ->
            Ok ({ init = new_init; final = new_final; loops = new_loops;
                  bools = new_bools; constrs = new_constrs }, new_env))))

  let addConstraint (v : value) (c : constr) (s : interp_state) (env : env)
    (k : interp_state -> env -> interp_res) : (interp_res, string) result =
    let checkValue =
      match c with
      | IsBool b ->
          begin match ValueMap.find_opt v s.bools with
          | Some c when b = c -> Some (k s env)
          | Some _ -> Some (Err "Incompatible constraints")
          | None ->
              match asTruth v with
              | Some c when b = c -> Some (k s env)
              | Some _ -> Some (Err "Incompatible constraints")
              | None -> None
          end
      | IsConstructor (_, _) -> failwith "TODO"
    in match checkValue with
    | Some res -> Ok res
    | None ->
        match v with
        | Unknown (id, _) ->
            let new_val =
              match c with
              | IsBool b -> boolAsValue b
              | IsConstructor (_, _) -> failwith "TODO"
            in Result.bind (substitute_unknown id new_val s env)
                (fun (s, env) -> Ok (k s env))
        | Function (_f, _arg, _) -> failwith "TODO"
        | _ ->
            match c with
            | IsBool b ->
                let new_state = {
                  init = s.init; final = s.final; loops = s.loops;
                  bools = ValueMap.add v b s.bools;
                  constrs = s.constrs }
                in Ok (k new_state env)
            | IsConstructor (_, _) -> failwith "TODO"


  let rec interpret (p : stmt) (s : interp_state) (env : env)
    (cont  : interp_state -> env -> interp_res)
    (yield : interp_state -> env -> value * typ -> interp_res)
    (ret   : interp_state -> env -> value * typ -> interp_res)
    (raise : interp_state -> env -> value * typ -> interp_res) : interp_res =
    match p with
    | Seq (x, y) ->
        interpret x s env
          (fun s env -> interpret y s env cont yield ret raise)
          yield
          ret
          raise
    | Action (var, a, e) ->
        begin match eval_expr e env with
        | Error msg -> Err msg
        | Ok (v, t) ->
            let (in_var, in_ty, ret_ty, body) = actionDef a
            in if t <> in_ty
            then Err "Incorrect argument type for action"
            else
              interpret body s (VariableMap.singleton in_var (v, t))
                (fun _ _ -> Err "No return from action, continued instead")
                (fun _ _ _ -> Err "No return from action, yielded instead")
                (fun s _ (r, t) ->
                  if t <> ret_ty
                  then Err "Incorrect return type from action"
                  else cont s (VariableMap.add var (r, t) env))
                (fun s _ e -> raise s env e)
        end
    | Assign (var, e) ->
        begin match eval_expr e env with
        | Error msg -> Err msg
        | Ok v -> cont s (VariableMap.add var v env)
        end
    (* TODO: A bunch of other things *)
    (* For both cond and match we try to reduce the expression to a concrete
     * value that we can branch on. However, if it cannot reduce to such an
     * expression then we try both possible options (which involves
     * interacting with the constraints of the current state) *)
    | Cond (c, thn, els) ->
        begin match eval_expr c env with
        | Error msg -> Err msg
        | Ok (v, t) ->
            if not (isTruthType t)
            then Err "Condition is not truthy"
            else
              match asTruth v with
              | Some true  -> interpret thn s env cont yield ret raise
              | Some false -> interpret els s env cont yield ret raise
              | None ->
                  let true_res = addConstraint v (IsBool true) s env
                      (fun s env -> interpret thn s env cont yield ret raise)
                  in let false_res = addConstraint v (IsBool false) s env
                      (fun s env -> interpret els s env cont yield ret raise)
                  in match true_res, false_res with
                  | Ok true_res, Ok false_res -> Both (true_res, false_res)
                  | Error m, Error n -> Err (m ^ "\n" ^ n)
                  | Error m, Ok _ | Ok _, Error m -> Err m
        end
    (* TODO: A bunch of other things *)
    | TryCatch (body, var, catch, finally) ->
        interpret body s env
          (* continue : execute finally and then continue as usual *)
          (fun s env -> interpret finally s env cont yield ret raise)
          (* yield : execute finally and then yield the value, unless the finally did already *)
          (fun s env e ->
            interpret finally s env
              (* continue -- yield e *) (fun s env -> yield s env e)
              (* yield -- just yield *) yield
              (* ret -- just return  *) ret
              (* raise -- just raise *) raise)
          (* ret : execute finally and then return the value, unless the finally did already *)
          (fun s env e ->
            interpret finally s env
              (* continue -- return e *) (fun s env -> ret s env e)
              (* yield -- still ret e *) (fun s env _ -> ret s env e)
              (* ret -- just return   *) ret
              (* raise -- just raise  *) raise)
          (* raise : execute catch and then finally and continue as usual *)
          (fun s env e ->
            interpret catch s (VariableMap.add var e env)
              (* continue -- finally then continue *)
              (fun s env -> interpret finally s env cont yield ret raise)
              (* yield -- finally then yield *)
              (fun s env e ->
                interpret finally s env
                  (* continue - yield e *) (fun s env -> yield s env e)
                  (* yield - just yield *) yield
                  (* ret - just return  *) ret
                  (* raise - just raise *) raise)
              (* ret -- finally then ret *)
              (fun s env e ->
                interpret finally s env
                  (* continue - return e *) (fun s env -> ret s env e)
                  (* yield - still ret e *) (fun s env _ -> ret s env e)
                  (* ret - just return   *) ret
                  (* raise - just raise  *) raise)
              (* raise -- finally then raise *)
              (fun s env e ->
                interpret finally s env
                  (* continue - raise e *) (fun s env -> raise s env e)
                  (* yield - raise e    *) (fun s env _ -> raise s env e)
                  (* ret - just return  *) ret
                  (* raise - just raise *) raise))
    | Raise e ->
        begin match eval_expr e env with
        | Error msg -> Err msg
        | Ok v -> raise s env v
        end
    | Return e ->
        begin match eval_expr e env with
        | Error msg -> Err msg
        | Ok v -> ret s env v
        end
    | Yield e ->
        begin match eval_expr e env with
        | Error msg -> Err msg
        | Ok v -> yield s env v
        end
    | _ -> failwith "TODO"
end
