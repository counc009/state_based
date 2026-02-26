let uid = Ast.uid
type uid = Ast.uid

type id = Ast.id

module Interp(Ast : Ast.Ast_Defs) = struct
  open Ast

  let type_of_val (v : value) : typ =
    match v with
    | Unknown (_, t) -> t
    | Literal (_, p) -> Primitive p
    | Function (_, _, t) -> t
    | Pair (_, _, t) -> t
    | Constructor (n, _, _) -> Named n
    | Struct (s, _) -> Struct s
    | ListVal (n, _) -> Named n

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


  let construct_equals v w : (value, string) result =
    let tv = type_of_val v
    in let tw = type_of_val w
    in if tv <> tw
      then Error "Type error, cannot equate values of different types"
      else
        let equals = equality_func tv
        in let (_, retTy, _) = funcDef equals
        in Ok (
        Function (
          equals,
          Pair (v, w, Product (tv, tw)),
          retTy))

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
  module ElementOrder : Map.OrderedType with type t = element * value = struct
    type t = element * value
    let compare : t -> t -> int = compare
  end
  module ElementMap : (Map.S with type key = element * value)
    = Map.Make(ElementOrder)

  module AttributeOrder : Map.OrderedType with type t = attribute = struct
    type t = attribute
    let compare : t -> t -> int = compare
  end
  module AttributeMap : (Map.S with type key = attribute)
    = Map.Make(AttributeOrder)

  type element_result = Negated | Positive of state
  and state = State of element_result ElementMap.t * value AttributeMap.t

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

  (* Add the second state to the first state *)
  let rec add_states (State (el, at)) (State (em, ar)) : state =
    let new_attrs =
      AttributeMap.merge (fun _attr orig added ->
        match added with
        | Some v -> Some v
        | None -> orig)
        at ar
    in let new_elems =
      ElementMap.merge (fun _elem orig added ->
        match orig, added with
        | None, None -> None
        | None, Some added -> Some added
        | Some orig, None -> Some orig
        | Some Negated, Some added -> Some added
        | Some _, Some Negated -> Some Negated
        | Some (Positive orig), Some (Positive added) ->
            Some (Positive (add_states orig added)))
        el em
    in State (new_elems, new_attrs)

  type qualifier = Attribute  of attribute * value
                 | Element    of element   * value * state
                 | NotElement of element   * value

  let add_qual (q : qualifier) (State (els, ats) : state) : state =
    match q with
    | Attribute (attr, v) ->
        State (els, AttributeMap.add attr v ats)
    | NotElement (elem, v) ->
        State (ElementMap.add (elem, v) Negated els, ats)
    | Element (elem, v, nested) ->
        let updated =
          ElementMap.update (elem, v)
            (fun cur ->
              let s =
                match cur with
                | None | Some Negated -> empty_state
                | Some (Positive s) -> s
              in Some (Positive (add_states s nested)))
            els
        in State (updated, ats)

  let rec eval_qual (q : qual) (env : env) : (qualifier, string) result =
    match q with
    | Attribute (attr, exp) ->
        Result.bind (eval_expr exp env) (fun (v, _) ->
          Ok (Attribute (attr, v)))
    | Element (elem, exp, q) ->
        Result.bind (eval_expr exp env) (fun (v, _) ->
          match q with
          | None -> Ok (Element (elem, v, empty_state))
          | Some q ->
              Result.bind (eval_qual q env) (fun q ->
                Ok (Element (elem, v, add_qual q empty_state))))
    | NotElement (elem, exp) ->
        Result.bind (eval_expr exp env) (fun (v, _) ->
          Ok (NotElement (elem, v)))

  (* A type representing attempting to find some value in a structure where we
   * may or may not find it or may be able to create the value and if so we need
   * to return additional information *)
  type ('a, 'b) find = NotLocated
                     | Located of 'a
                     | Created of 'a * 'b

  let get_attribute (_a : attr) (_s : interp_state) (_env : env)
    : (value * interp_state, string) result =
      failwith "TODO"

  let rec substitute_unknown (u : id) (v : value) (s : interp_state) (env : env)
    (k : interp_state -> env -> (interp_res, string) result)
    (merge : interp_res -> interp_res -> interp_res)
    : (interp_res, string) result =
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
              (fun (el, v) s new_state ->
                Result.bind new_state (fun new_state ->
                  Result.bind (subst_in_value v) (fun new_v ->
                    match s with
                    | Negated -> Ok (add_qual (NotElement (el, new_v)) new_state)
                    | Positive s ->
                        Result.bind (subst_in_state s) (fun new_s ->
                          Ok (add_qual (Element (el, new_v, new_s)) new_state)))))
              elems (Ok empty_state)
          in let with_attrs =
            Result.bind with_elems (fun with_elems ->
              AttributeMap.fold
                (fun attr v new_state ->
                  Result.bind new_state (fun new_state ->
                    Result.bind (subst_in_value v) (fun new_v ->
                      Ok (add_qual (Attribute (attr, new_v)) new_state))))
                attrs (Ok with_elems))
          in with_attrs
    in let new_env : (env, string) result =
      variableMap_map_result
        (fun (v, t) -> Result.bind (subst_in_value v) (fun v -> Ok (v, t)))
        env
    in let new_init = subst_in_state s.init
    in let new_final = subst_in_state s.final
    in let new_loops =
      ValueMap.fold (fun lst loop new_loops ->
        Result.bind new_loops (fun new_loops ->
          let new_lst = subst_in_value lst
          in let new_loop =
            match loop, u with
            | AllUnknown i, Loop j when i = j -> Ok (AllKnown v)
            | AllUnknown i, Val j when i = j -> Ok (LastKnown (i, v))
            | AllUnknown _, _ -> Ok loop
            | AllKnown w, _ ->
                Result.bind (subst_in_value w) (fun w -> Ok (AllKnown w))
            | LastKnown (i, _w), Loop j when i = j ->
                (* TODO: Should unify w and v *) Ok (AllKnown v)
            | LastKnown  (i, w), _ ->
                Result.bind (subst_in_value w) (fun w -> Ok (LastKnown (i, w)))
          in Result.bind new_loop (fun new_loop ->
              Result.bind new_lst (fun new_lst ->
                match ValueMap.find_opt new_lst new_loops with
                | None ->
                    Ok (ValueMap.add new_lst new_loop new_loops)
                | Some _l -> (* TODO: Should unify l and new_loop *)
                    Ok new_loops))))
        s.loops
        (Ok ValueMap.empty)
    (* We don't add bools and constrs manually, we use addConstraint *)
    in let partial_state =
      Result.bind new_init (fun new_init ->
        Result.bind new_final (fun new_final ->
          Result.bind new_loops (fun new_loops ->
            Result.bind new_env (fun new_env ->
              Ok ({ init = new_init; final = new_final; loops = new_loops;
                    bools = ValueMap.empty; constrs = ValueMap.empty },
                  new_env)))))
    in let add_bools =
      ValueMap.fold
        (fun old_v constr k state env -> 
          Result.bind (subst_in_value old_v) (fun new_v ->
            addConstraint new_v (IsBool constr) state env k merge))
        s.bools
        k
    in let add_constrs =
      ValueMap.fold
        (fun old_v (cb, cv) k state env -> 
          Result.bind (subst_in_value old_v) (fun new_v ->
            addConstraint new_v (IsConstructor (cb, cv)) state env k merge))
        s.constrs
        add_bools
    in Result.bind partial_state (fun (s, env) -> add_constrs s env)

  and addConstraint (v : value) (c : constr) (s : interp_state) (env : env)
    (k : interp_state -> env -> (interp_res, string) result)
    (merge : interp_res -> interp_res -> interp_res)
    : (interp_res, string) result =
    let addConstraintBasic (v : value) (c : constr) (s : interp_state)
      (env : env) (k : interp_state -> env -> (interp_res, string) result) =
      match c with
      | IsBool b ->
          let new_state = {
            init = s.init; final = s.final; loops = s.loops;
            bools = ValueMap.add v b s.bools;
            constrs = s.constrs }
          in k new_state env
      | IsConstructor (which, c) ->
          let new_state = {
            init = s.init; final = s.final; loops = s.loops;
            bools = s.bools;
            constrs = ValueMap.add v (which, c) s.constrs }
          in k new_state env
      | IsEqual w ->
          (* TODO: Ideally we would track a congruence closure data structure
           * (i.e., an e-graph) but that's very complicated as we'd need a
           * pure or persistent e-graph implementation *)
          Result.bind (construct_equals v w) (fun equality_vw ->
            Result.bind (construct_equals w v) (fun equality_wv ->
              let new_state = {
                init = s.init; final = s.final; loops = s.loops;
                bools = ValueMap.add equality_vw true
                          (ValueMap.add equality_wv true s.bools);
                constrs = s.constrs }
              in k new_state env))

    in let checkValue =
      match c with
      | IsBool b ->
          begin match asTruth v with
          | Some c when b = c -> Some (k s env)
          | Some _ -> Some (Error "Incompatible constraints")
          | None ->
              match ValueMap.find_opt v s.bools with
              | Some c when b = c -> Some (k s env)
              | Some _ -> Some (Error "Incompatible constraints")
              | None -> None
          end
      | IsConstructor (which, b) ->
          begin match v with
          | Constructor (_, c, x) when c = which ->
              Some (addConstraint x (IsEqual b) s env k merge)
          | Constructor (_, _, _) -> Some (Error "Incompatible constraints")
          | _ ->
              match ValueMap.find_opt v s.constrs with
              | Some (c, x) when c = which ->
                  Some (addConstraint x (IsEqual b) s env k merge)
              | Some (_, _) -> Some (Error "Incompatible constraints")
              | None -> None
          end
      | IsEqual w ->
          if v = w
          then Some (k s env)
          else
            match construct_equals v w with
            | Error msg -> Some (Error msg)
            | Ok equality_check ->
              match ValueMap.find_opt equality_check s.bools with
              | Some true -> Some (k s env)
              | Some false -> Some (Error "Incompatible constraints")
              | None ->
                match v, w with
                | Unknown (id, _), _ ->
                    Some (substitute_unknown id w s env k merge)
                | _, Unknown (id, _) ->
                    Some (substitute_unknown id v s env k merge)
                (* TODO: Is it fair to assume literals must be syntactically equal? *)
                | Literal (_, _), Literal (_, _) ->
                    Some (Error "Incompatible constraints")
                | Pair (a, b, _), Pair (x, y, _) ->
                    Some (addConstraint a (IsEqual x) s env
                      (fun s env ->
                        addConstraint b (IsEqual y) s env k merge)
                      merge)
                | Constructor (_, a, b), Constructor (_, x, y) ->
                    if a = x
                    then
                      Some (addConstraint b (IsEqual y) s env k merge)
                    else Some (Error "Incompatiable constraints")
                | Struct (_, x), Struct (_, y) ->
                    let merged =
                      FieldMap.merge (fun _f x y ->
                        match x, y with
                        | Some x, Some y -> Some (Ok (x, y))
                        | None, None -> None
                        | _, _ -> Some (Error "Incompatible constraints"))
                        x y
                    in Some (FieldMap.fold (fun _f vals k s env ->
                        Result.bind vals (fun (x, y) ->
                          addConstraint x (IsEqual y) s env k merge))
                        merged k s env)
                | ListVal (_, x), ListVal (_, y) ->
                    (* TODO: Is this correct? *)
                    Some (addConstraint x (IsEqual y) s env k merge)
                (* TODO: Is there more we can do here? *)
                | Constructor (_, _, _), ListVal (_, _) -> None
                | ListVal (_, _), Constructor (_, _, _) -> None
                (* Try to simplify function stuff below *)
                | Function (_, _, _), _ -> None
                | _, Function (_, _, _) ->
                    (* Swap so that we can simplify the function *)
                    Some (addConstraint w (IsEqual v) s env k merge)
                | _, _ -> Some (Error "Incompatible constraints")
    in match checkValue with
    | Some res -> res
    | None ->
        match v with
        | Unknown (id, typ) ->
            let new_val =
              match c with
              | IsBool b -> Ok (boolAsValue b)
              | IsConstructor (which, c) ->
                  begin match typ with
                  | Named nm -> Ok (Constructor (nm, which, c))
                  | _ -> Error "Invalid type for constructor"
                  end
              | IsEqual w -> Ok w
            in begin match new_val with
            | Ok new_val -> substitute_unknown id new_val s env k merge
            | Error msg -> Error msg
            end
        | Function (f, arg, _) ->
            begin match reduceFuncConstraint f arg c with
            | Unreducible -> addConstraintBasic v c s env k
            | Reducible options ->
                List.fold_left
                  (fun total_res cs ->
                    let this_res : (interp_res, string) result =
                      List.fold_left
                        (fun k c s env ->
                          match c with
                          | IsBool (v, b) ->
                              addConstraint v (IsBool b) s env k merge
                          | IsConstructor (v, (which, arg)) ->
                              addConstraint v (IsConstructor (which, arg))
                                s env k merge
                          | IsEqual (x, y) ->
                              addConstraint x (IsEqual y) s env k merge)
                        k
                        cs
                        s
                        env
                    in match total_res, this_res with
                    | Error _, _ -> this_res
                    | _, Error _ -> total_res
                    | Ok total, Ok this -> Ok (merge total this))
                  (Error "Unsatisfiable function constraint reduction")
                  options
            end
        | _ -> addConstraintBasic v c s env k

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
    | Add qual ->
        begin match eval_qual qual env with
        | Error msg -> Err msg
        | Ok q ->
            let new_final = add_qual q s.final
            in let new_state = {
              init = s.init; final = new_final; loops = s.loops;
              bools = s.bools; constrs = s.constrs }
            in cont new_state env
        end
    | Get (var, attr) ->
        begin match get_attribute attr s env with
        | Error msg -> Err msg
        | Ok (v, new_state) ->
            let new_env = VariableMap.add var (v, type_of_val v) env
            in cont new_state new_env
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
                  let true_res =
                    addConstraint v (IsBool true) s env
                      (fun s env ->
                        Ok (interpret thn s env cont yield ret raise))
                      (* If this is an existential condition, then use Either
                       * here instead of Both *)
                      (fun x y -> Both (x, y))
                  in let false_res =
                    addConstraint v (IsBool false) s env
                      (fun s env ->
                        Ok (interpret els s env cont yield ret raise))
                      (fun x y -> Both (x, y))
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
